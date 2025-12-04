use std::{cell::Cell, fmt};

use itertools::Itertools;
use smol_strc::{SmolStr, format_smolstr};
use text_size::{TextRange, TextSize};

pub enum VisitAction {
    Enter,
    Leave,
}

impl VisitAction {
    /// Returns `true` if the visit kind is [`Enter`].
    ///
    /// [`Enter`]: VisitAction::Enter
    #[must_use]
    pub fn is_enter(&self) -> bool {
        matches!(self, Self::Enter)
    }

    /// Returns `true` if the visit kind is [`Leave`].
    ///
    /// [`Leave`]: VisitAction::Leave
    #[must_use]
    pub fn is_leave(&self) -> bool {
        matches!(self, Self::Leave)
    }
}
use VisitAction::*;

#[derive(Debug)]
pub struct Node {
    kind: SmolStr,
    range: TextRange,
    sub: Vec<Node>,
}

impl core::ops::Index<&Node> for str {
    type Output = str;

    #[inline]
    fn index(&self, index: &Node) -> &str {
        &self[index.range]
    }
}

impl Node {
    pub fn visit(&self, f: &mut impl FnMut(&Self, VisitAction) -> Option<()>) {
        f(self, Enter);
        self.sub.iter().for_each(|node| node.visit(f));
        f(self, Leave);
    }

    pub fn find_children(&self, kind: &str) -> Option<&Node> {
        self.sub.iter().find(|it| it.kind == kind)
    }

    pub fn start(&self) -> TextSize {
        self.range.start()
    }

    pub fn end(&self) -> TextSize {
        self.range.end()
    }

    pub fn sub(&self) -> &[Node] {
        &self.sub
    }
}

impl fmt::LowerHex for Node {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Node { kind, range, sub, .. } = self;
        write!(f, "{kind}@{}..{}", u32::from(range.start()), u32::from(range.end()))?;
        if !sub.is_empty() {
            write!(f, "{{{:x}}}", sub.iter().format(", "))?;
        }
        Ok(())
    }
}
pub fn make_node(src: &str) -> Node {
    let mut parsed_nodes = src.lines()
        .filter(|line| !line.trim().is_empty())
        .map(|line| {
            line.split_at(line.find(|it| it != ' ').unwrap())
        })
        .map(|(ws, content)| {
            assert_eq!(ws.trim(), "");
            (ws.len() / 2, content)
        })
        .map(|(level, content)| {
            let (content, _) = content.split_once(' ').unwrap_or((content, r#""""#));
            let Some((kind, range)) = content.split_once('@') else {
                panic!("invalid node: `{content}`");
            };
            let Some((start, end)) = range.split_once("..") else {
                panic!("invalid node range: `{content}`");
            };
            let [start, end] = [start, end].map(|s| s.parse().unwrap_or_else(|e| {
                panic!("invalid node range number ({e}): `{content}`");
            })).map(TextSize::new);
            (level, Node {
                kind: kind.into(),
                range: TextRange::new(start, end),
                sub: vec![],
            })
        });
    let (first_level, node) = parsed_nodes.next().expect("nodes by empty");
    let parsed_nodes = parsed_nodes.map(|(l, node)| {
        let Some(l) = l.checked_sub(first_level) else {
            panic!("level {l} < first_level {first_level} of {node:x}");
        };
        assert!(l != 0, "multiple root node: {node:x}");
        (l, node)
    });

    let pop_and_push = |stack: &mut Vec<Node>| {
        let value = stack.pop().unwrap();
        stack.last_mut().unwrap().sub.push(value);
    };
    let mut node_stack = vec![node];
    for (level, node) in parsed_nodes {
        for _ in level..node_stack.len() {
            pop_and_push(&mut node_stack);
        }
        node_stack.push(node);
    }
    while node_stack.len() > 1 {
        pop_and_push(&mut node_stack);
    }
    node_stack.into_iter().next().unwrap()
}

struct ShowMark(Cell<u32>);

impl fmt::Display for ShowMark {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "'{}", self.0.get())?;
        if self.0.get() < 10 {
            write!(f, " ")?;
        }
        self.0.update(|n| n+1);
        Ok(())
    }
}

#[derive(Debug, Default)]
pub struct Config {
    pub debug: bool,
    pub stderr: bool,
}

pub fn term_expr_inserts(
    node: &Node,
    src: &str,
    Config { debug, stderr }: Config,
) -> Vec<(TextSize, SmolStr)> {
    let mut inserts = vec![];
    macro_rules! at {
        ($at:expr, $($t:tt)*) => {
            inserts.push(($at, format_smolstr!($($t)*)));
        };
    }
    let mut fn_names = vec!["unnamed_fn".into()];
    let mark = ShowMark(0.into());
    let closures = ShowMark(0.into());
    let debug = if debug { " = {__val:?}" } else { "" };
    let output = if stderr { "eprintln" } else { "println" };
    let pather = r#"::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1)"#;

    node.visit(&mut |node, action| {
        if action.is_leave() {
            if let "FN" | "CLOSURE_EXPR" = node.kind.as_str() {
                fn_names.pop().unwrap();
            }
            return None;
        }
        if node.kind == "FN" {
            let name = node.find_children("NAME")?;
            fn_names.push(format_smolstr!("[track] {}", &src[name]));
        } else if node.kind == "CLOSURE_EXPR" {
            let name = format_smolstr!("closure{closures}");
            fn_names.push(format_smolstr!("[track] {name}"));
            at!(node.start(), "/*{name}*/");
        }
        let name = fn_names.last().unwrap();

        let try_trait = format!{"trait _IsTryOk{{\
                fn is_try_ok(&self)->bool;\
            }}impl<T,E>_IsTryOk for ::core::result::Result<T,E>{{\
                fn is_try_ok(&self)->bool{{self.is_ok()}}\
            }}impl<T>_IsTryOk for ::core::option::Option<T>{{\
                fn is_try_ok(&self)->bool{{self.is_some()}}\
            }}\
            macro_rules!_track{{\
                (@$s:tt,$e:expr)=>({{let __val = $e;if !_IsTryOk::is_try_ok(&__val){{{output}!(\
                    \"{name} tryret{{}} at {{}}:{{}}{debug}\",\
                    $s,{pather},::core::line!())}}; __val }});\
                (+$s:tt,$e:expr)=>({{let __val = $e;{output}!(\
                    \"{name} return{{}} at {{}}:{{}}{debug}\",\
                    $s,{pather},::core::line!()); __val }});\
                (%$s:tt,$e:expr)=>({{let __val = $e;{output}!(\
                    \"{name} endret{{}} at {{}}:{{}}{debug}\",\
                    $s,{pather},::core::line!()); __val }});\
            }}\
            {output}!(\"{name} enter     at {{}}:{{}}\",{pather},::core::line!());\
            "};

        match node.kind.as_str() {
            "FN" => {
                let stmt_list = node
                    .find_children("BLOCK_EXPR")?
                    .find_children("STMT_LIST")?;
                let l_curly = stmt_list.find_children("L_CURLY")?;
                at!(l_curly.end(), "{try_trait}");

                let tail = stmt_list.sub().iter().rfind(|it| !matches!(it.kind.as_str(),
                        | "L_CURLY"
                        | "R_CURLY"
                        | "WHITESPACE"
                        | "COMMENT"
                        ))?;
                at!(tail.start(), r#"_track!{{%"{mark}","#);
                at!(tail.end(), r#"}}"#);
            }
            "CLOSURE_EXPR" => {
                let tail = node.sub().last()?;
                at!(tail.start(), r#"{{{try_trait}_track!{{%"{mark}","#);
                at!(tail.end(), r#"}}}}"#);
            }
            "RETURN_EXPR" => {
                let kw = node.find_children("RETURN_KW")?;
                at!(kw.end(), r#" _track!(+"{mark}","#);
                at!(node.end(), r#")"#);
            }
            "TRY_EXPR" => {
                let op = node.find_children("QUESTION")?;
                at!(node.start(), r#" _track!(@"{mark}","#);
                at!(op.start(), r#")"#);
            }
            _ => {}
        }
        None
    });
    inserts
}

pub fn apply_inserts(mut inserts: Vec<(TextSize, SmolStr)>, s: &mut String) {
    inserts.sort_by_key(|(at, _)| u32::from(*at));
    for (at, text) in inserts.iter().rev() {
        s.insert_str((*at).into(), text);
    }
}

#[cfg(test)]
mod tests {
    use expect_test::expect;

    use super::*;

    const TEST_AST: &str = {r#"
SOURCE_FILE@0..137
  FN@0..136
    FN_KW@0..2 "fn"
    WHITESPACE@2..3 " "
    NAME@3..6
      IDENT@3..6 "foo"
    PARAM_LIST@6..13
      L_PAREN@6..7 "("
      PARAM@7..12
        IDENT_PAT@7..8
          NAME@7..8
            IDENT@7..8 "n"
        COLON@8..9 ":"
        WHITESPACE@9..10 " "
        PATH_TYPE@10..12
          PATH@10..12
            PATH_SEGMENT@10..12
              NAME_REF@10..12
                IDENT@10..12 "u8"
      R_PAREN@12..13 ")"
    WHITESPACE@13..14 " "
    RET_TYPE@14..27
      THIN_ARROW@14..16 "->"
      WHITESPACE@16..17 " "
      PATH_TYPE@17..27
        PATH@17..27
          PATH_SEGMENT@17..27
            NAME_REF@17..23
              IDENT@17..23 "Option"
            GENERIC_ARG_LIST@23..27
              L_ANGLE@23..24 "<"
              TYPE_ARG@24..26
                PATH_TYPE@24..26
                  PATH@24..26
                    PATH_SEGMENT@24..26
                      NAME_REF@24..26
                        IDENT@24..26 "u8"
              R_ANGLE@26..27 ">"
    WHITESPACE@27..28 " "
    BLOCK_EXPR@28..136
      STMT_LIST@28..136
        L_CURLY@28..29 "{"
        WHITESPACE@29..34 "\n    "
        LET_STMT@34..61
          LET_KW@34..37 "let"
          WHITESPACE@37..38 " "
          IDENT_PAT@38..39
            NAME@38..39
              IDENT@38..39 "m"
          WHITESPACE@39..40 " "
          EQ@40..41 "="
          WHITESPACE@41..42 " "
          TRY_EXPR@42..60
            METHOD_CALL_EXPR@42..59
              PATH_EXPR@42..43
                PATH@42..43
                  PATH_SEGMENT@42..43
                    NAME_REF@42..43
                      IDENT@42..43 "n"
              DOT@43..44 "."
              NAME_REF@44..55
                IDENT@44..55 "checked_sub"
              ARG_LIST@55..59
                L_PAREN@55..56 "("
                LITERAL@56..58
                  INT_NUMBER@56..58 "16"
                R_PAREN@58..59 ")"
            QUESTION@59..60 "?"
          SEMICOLON@60..61 ";"
        WHITESPACE@61..66 "\n    "
        LET_STMT@66..79
          LET_KW@66..69 "let"
          WHITESPACE@69..70 " "
          WILDCARD_PAT@70..71
            UNDERSCORE@70..71 "_"
          WHITESPACE@71..72 " "
          EQ@72..73 "="
          WHITESPACE@73..74 " "
          CLOSURE_EXPR@74..78
            PARAM_LIST@74..76
              PIPE@74..75 "|"
              PIPE@75..76 "|"
            WHITESPACE@76..77 " "
            LITERAL@77..78
              INT_NUMBER@77..78 "2"
          SEMICOLON@78..79 ";"
        WHITESPACE@79..84 "\n    "
        EXPR_STMT@84..122
          IF_EXPR@84..122
            IF_KW@84..86 "if"
            WHITESPACE@86..87 " "
            BIN_EXPR@87..93
              PATH_EXPR@87..88
                PATH@87..88
                  PATH_SEGMENT@87..88
                    NAME_REF@87..88
                      IDENT@87..88 "m"
              WHITESPACE@88..89 " "
              EQ2@89..91 "=="
              WHITESPACE@91..92 " "
              LITERAL@92..93
                INT_NUMBER@92..93 "0"
            WHITESPACE@93..94 " "
            BLOCK_EXPR@94..122
              STMT_LIST@94..122
                L_CURLY@94..95 "{"
                WHITESPACE@95..104 "\n        "
                EXPR_STMT@104..116
                  RETURN_EXPR@104..115
                    RETURN_KW@104..110 "return"
                    WHITESPACE@110..111 " "
                    PATH_EXPR@111..115
                      PATH@111..115
                        PATH_SEGMENT@111..115
                          NAME_REF@111..115
                            IDENT@111..115 "None"
                  SEMICOLON@115..116 ";"
                WHITESPACE@116..121 "\n    "
                R_CURLY@121..122 "}"
        WHITESPACE@122..127 "\n    "
        CALL_EXPR@127..134
          PATH_EXPR@127..131
            PATH@127..131
              PATH_SEGMENT@127..131
                NAME_REF@127..131
                  IDENT@127..131 "Some"
          ARG_LIST@131..134
            L_PAREN@131..132 "("
            PATH_EXPR@132..133
              PATH@132..133
                PATH_SEGMENT@132..133
                  NAME_REF@132..133
                    IDENT@132..133 "m"
            R_PAREN@133..134 ")"
        WHITESPACE@134..135 "\n"
        R_CURLY@135..136 "}"
  WHITESPACE@136..137 "\n"
"#};
    const TEST_SRC: &str = {
r#"fn foo(n: u8) -> Option<u8> {
    let m = n.checked_sub(16)?;
    let _ = || 2;
    if m == 0 {
        return None;
    }
    Some(m)
}
"#};

    #[test]
    fn test_data() {
        let node = make_node(TEST_AST);
        assert_eq!(usize::from(node.range.end()), TEST_SRC.len());
    }

    #[test]
    fn test_replace() {
        let mut s = TEST_SRC.to_string();
        let node = make_node(TEST_AST);
        let inserts = term_expr_inserts(&node, &s, Config { debug: true, ..Default::default() });
        apply_inserts(inserts, &mut s);
        expect![[r#"
            fn foo(n: u8) -> Option<u8> {trait _IsTryOk{fn is_try_ok(&self)->bool;}impl<T,E>_IsTryOk for ::core::result::Result<T,E>{fn is_try_ok(&self)->bool{self.is_ok()}}impl<T>_IsTryOk for ::core::option::Option<T>{fn is_try_ok(&self)->bool{self.is_some()}}macro_rules!_track{(@$s:tt,$e:expr)=>({let __val = $e;if !_IsTryOk::is_try_ok(&__val){println!("[track] foo tryret{} at {}:{} = {__val:?}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!())}; __val });(+$s:tt,$e:expr)=>({let __val = $e;println!("[track] foo return{} at {}:{} = {__val:?}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); __val });(%$s:tt,$e:expr)=>({let __val = $e;println!("[track] foo endret{} at {}:{} = {__val:?}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); __val });}println!("[track] foo enter     at {}:{}",::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!());
                let m =  _track!(@"'1 ",n.checked_sub(16))?;
                let _ = /*closure'0 */|| {trait _IsTryOk{fn is_try_ok(&self)->bool;}impl<T,E>_IsTryOk for ::core::result::Result<T,E>{fn is_try_ok(&self)->bool{self.is_ok()}}impl<T>_IsTryOk for ::core::option::Option<T>{fn is_try_ok(&self)->bool{self.is_some()}}macro_rules!_track{(@$s:tt,$e:expr)=>({let __val = $e;if !_IsTryOk::is_try_ok(&__val){println!("[track] closure'0  tryret{} at {}:{} = {__val:?}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!())}; __val });(+$s:tt,$e:expr)=>({let __val = $e;println!("[track] closure'0  return{} at {}:{} = {__val:?}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); __val });(%$s:tt,$e:expr)=>({let __val = $e;println!("[track] closure'0  endret{} at {}:{} = {__val:?}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); __val });}println!("[track] closure'0  enter     at {}:{}",::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!());_track!{%"'2 ",2}};
                if m == 0 {
                    return _track!(+"'3 ", None);
                }
                _track!{%"'0 ",Some(m)}
            }
        "#]].assert_eq(&s);
    }
}
