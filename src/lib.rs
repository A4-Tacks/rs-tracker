use std::{cell::Cell, fmt};

use itertools::Itertools;
use smol_strc::{SmolStr, format_smolstr};
use text_size::{TextRange, TextSize};

mod kind;

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

    pub fn next_of(&self, of: &Node) -> Option<&Node> {
        self.sub.iter().find(|it| it.start() == of.end())
    }

    pub fn split_part(&self, kind: &str) -> Option<(&[Node], &[Node])> {
        let sub = self.sub();
        let i = sub.iter().position(|it| it.kind == kind)?;
        Some((&sub[..i], &sub[i+1..]))
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

#[derive(Debug, PartialEq, Eq)]
pub enum Debug {
    Inline,
    Expand,
    Disable,
}

impl Default for Debug {
    fn default() -> Self {
        Self::Disable
    }
}

#[derive(Debug, Default)]
pub struct Config {
    pub debug: Debug,
    pub stderr: bool,
}

fn is_complex_closure(node: &Node) -> bool {
    if node.kind != "CLOSURE_EXPR" {
        return false;
    }
    node.range.len() > TextSize::new(140)
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
    let debug = match debug {
        Debug::Inline => " = {__val:?}",
        Debug::Expand => " = {__val:#?}",
        Debug::Disable => "",
    };
    let output = if stderr { "eprintln" } else { "println" };
    let pather = r#"::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1)"#;

    node.visit(&mut |node, action| {
        const SIMPLE_CLOSURE: SmolStr = SmolStr::new_inline("__simple_closure__");
        if action.is_leave() {
            if node.kind == "FN" || node.kind == "CLOSURE_EXPR" {
                fn_names.pop().unwrap();
            }
            return None;
        }
        if node.kind == "FN" {
            let name = node.find_children("NAME")?;
            fn_names.push(format_smolstr!("[track] {}", &src[name]));
        } else if node.kind == "CLOSURE_EXPR" {
            if is_complex_closure(node) {
                let name = format_smolstr!("closure{closures}");
                fn_names.push(format_smolstr!("[track] {name}"));
                at!(node.start(), "/*{name}*/");
            } else {
                fn_names.push(SIMPLE_CLOSURE);
            }
        }
        let name = fn_names.last().unwrap();

        if name == &SIMPLE_CLOSURE {
            return None;
        }

        let try_trait = format!{"trait _IsTryOk{{\
                fn is_try_ok(&self)->bool;\
            }}impl<T,E>_IsTryOk for ::core::result::Result<T,E>{{\
                fn is_try_ok(&self)->bool{{self.is_ok()}}\
            }}impl<T>_IsTryOk for ::core::option::Option<T>{{\
                fn is_try_ok(&self)->bool{{self.is_some()}}\
            }}\
            macro_rules!_track{{\
                (!)=>(());\
                (!$t:tt)=>($t);\
                (@$s:tt,$($e:expr)?)=>({{let __val = _track!(!$($e)?);if !_IsTryOk::is_try_ok(&__val){{{output}!(\
                    \"{name} tryret{{}} at {{}}:{{}}{debug}\",\
                    $s,{pather},::core::line!())}}; __val }});\
                (+$s:tt,$($e:expr)?)=>({{let __val = _track!(!$($e)?);{output}!(\
                    \"{name} return{{}} at {{}}:{{}}{debug}\",\
                    $s,{pather},::core::line!()); __val }});\
                (%$s:tt,$($e:expr)?)=>({{let __val = _track!(!$($e)?);{output}!(\
                    \"{name} endret{{}} at {{}}:{{}}{debug}\",\
                    $s,{pather},::core::line!()); __val }});\
                (%$s:tt,$e:stmt $(;)?)=>({{{{$e}};let __val = ();{output}!(\
                    \"{name} endret{{}} at {{}}:{{}}{debug}\",\
                    $s,{pather},::core::line!()); }});\
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

                each_value_expr_leafs(stmt_list, &mut |tail| {
                    at!(tail.start(), r#"{{_track!{{%"{mark}","#);
                    at!(tail.end(), r#"}}}}"#);
                });
            }
            "CLOSURE_EXPR" => {
                let tail = node.sub().last()?;
                at!(tail.start(), r#"{{{try_trait}{{_track!{{%"{mark}","#);
                at!(tail.end(), r#"}}}}}}"#);
            }
            "RETURN_EXPR" => {
                let kw = node.find_children("RETURN_KW")?;
                at!(kw.end(), r#"{{_track!(+"{mark}","#);
                at!(node.end(), r#")}}"#);
            }
            "TRY_EXPR" => {
                let op = node.find_children("QUESTION")?;
                at!(node.start(), r#"{{_track!(@"{mark}","#);
                at!(op.start(), r#")}}"#);
            }
            _ => {}
        }
        None
    });

    assert_eq!(fn_names, ["unnamed_fn"]);

    inserts
}

fn each_value_expr_leafs(tail: &Node, handler: &mut impl FnMut(&Node)) -> Option<()> {
    match tail.kind.as_str() {
        "MATCH_EXPR" => {
            tail.find_children("MATCH_ARM_LIST")?
                .sub().iter().filter(|it| it.kind == "MATCH_ARM")
                .for_each(|leaf| {
                    if let Some(expr) = leaf.sub().iter()
                        .rev()
                        .take_while(|it| it.kind != "FAT_ARROW")
                        .find(|it| it.kind != "COMMA")
                    {
                        each_value_expr_leafs(expr, handler);
                    }
                });
        }
        "BLOCK_EXPR" => each_value_expr_leafs(tail.find_children("STMT_LIST")?, handler)?,
        "STMT_LIST" => {
            let tail_expr = tail.sub().iter().rfind(|it| !matches!(it.kind.as_str(),
                    | "L_CURLY"
                    | "R_CURLY"
                    | "WHITESPACE"
                    | "COMMENT"
                    ))?;
            each_value_expr_leafs(tail_expr, handler)?
        }
        "IF_EXPR" if tail.find_children("ELSE_KW").is_some() => {
            let (bef, aft) = tail.split_part("ELSE_KW").unwrap();
            for part in [bef, aft] {
                if let Some(part) = part.iter()
                    .rfind(|it| matches!(&*it.kind, "BLOCK_EXPR" | "IF_EXPR"))
                {
                    let _ = each_value_expr_leafs(part, handler);
                }
            }
        }
        _ if kind::is_item_or_let(tail) => (),
        _ => handler(tail),
    }
    Some(())
}

mod remove_handles;
pub use remove_handles::remove_tracks;

pub fn apply_inserts(mut inserts: Vec<(TextSize, SmolStr)>, s: &mut String) {
    inserts.sort_by_key(|(at, _)| u32::from(*at));
    for (at, text) in inserts.iter().rev() {
        s.insert_str((*at).into(), text);
    }
}

pub fn apply_deletes(mut deletes: Vec<TextRange>, s: &mut String) {
    deletes.sort_by_key(|range| u32::from(range.start()));
    for (a, b) in deletes.iter().tuple_windows() {
        assert!(a.end() <= b.start(), "overlap deletes {a:?} & {b:?}\n{deletes:#?}");
    }
    for range in deletes.iter().rev() {
        let range = usize::from(range.start())..usize::from(range.end());
        s.drain(range);
    }
}

#[cfg(test)]
mod tests {
    use std::{io::Write, process::{Command, Stdio}};

    use expect_test::{Expect, expect};

    use super::*;

    #[allow(unused_braces)]
    const TEST_AST: Expect = {expect![[r#"
        SOURCE_FILE@0..377
          FN@0..376
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
            BLOCK_EXPR@28..376
              STMT_LIST@28..376
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
                LET_STMT@84..319
                  LET_KW@84..87 "let"
                  WHITESPACE@87..88 " "
                  WILDCARD_PAT@88..89
                    UNDERSCORE@88..89 "_"
                  WHITESPACE@89..90 " "
                  EQ@90..91 "="
                  WHITESPACE@91..92 " "
                  CLOSURE_EXPR@92..318
                    PARAM_LIST@92..94
                      PIPE@92..93 "|"
                      PIPE@93..94 "|"
                    WHITESPACE@94..95 " "
                    BLOCK_EXPR@95..318
                      STMT_LIST@95..318
                        L_CURLY@95..96 "{"
                        WHITESPACE@96..105 "\n        "
                        EXPR_STMT@105..121
                          MACRO_EXPR@105..120
                            MACRO_CALL@105..120
                              PATH@105..112
                                PATH_SEGMENT@105..112
                                  NAME_REF@105..112
                                    IDENT@105..112 "println"
                              BANG@112..113 "!"
                              TOKEN_TREE@113..120
                                L_PAREN@113..114 "("
                                STRING@114..119 "\"xxx\""
                                R_PAREN@119..120 ")"
                          SEMICOLON@120..121 ";"
                        WHITESPACE@121..130 "\n        "
                        IF_EXPR@130..312
                          IF_KW@130..132 "if"
                          WHITESPACE@132..133 " "
                          LITERAL@133..137
                            TRUE_KW@133..137 "true"
                          WHITESPACE@137..138 " "
                          BLOCK_EXPR@138..163
                            STMT_LIST@138..163
                              L_CURLY@138..139 "{"
                              WHITESPACE@139..152 "\n            "
                              LITERAL@152..153
                                INT_NUMBER@152..153 "3"
                              WHITESPACE@153..162 "\n        "
                              R_CURLY@162..163 "}"
                          WHITESPACE@163..164 " "
                          ELSE_KW@164..168 "else"
                          WHITESPACE@168..169 " "
                          IF_EXPR@169..312
                            IF_KW@169..171 "if"
                            WHITESPACE@171..172 " "
                            PATH_EXPR@172..176
                              PATH@172..176
                                PATH_SEGMENT@172..176
                                  NAME_REF@172..176
                                    IDENT@172..176 "cond"
                            WHITESPACE@176..177 " "
                            BLOCK_EXPR@177..202
                              STMT_LIST@177..202
                                L_CURLY@177..178 "{"
                                WHITESPACE@178..191 "\n            "
                                LITERAL@191..192
                                  INT_NUMBER@191..192 "0"
                                WHITESPACE@192..201 "\n        "
                                R_CURLY@201..202 "}"
                            WHITESPACE@202..203 " "
                            ELSE_KW@203..207 "else"
                            WHITESPACE@207..208 " "
                            BLOCK_EXPR@208..312
                              STMT_LIST@208..312
                                L_CURLY@208..209 "{"
                                WHITESPACE@209..222 "\n            "
                                IF_EXPR@222..302
                                  IF_KW@222..224 "if"
                                  WHITESPACE@224..225 " "
                                  LITERAL@225..229
                                    TRUE_KW@225..229 "true"
                                  WHITESPACE@229..230 " "
                                  BLOCK_EXPR@230..263
                                    STMT_LIST@230..263
                                      L_CURLY@230..231 "{"
                                      WHITESPACE@231..248 "\n                "
                                      LITERAL@248..249
                                        INT_NUMBER@248..249 "4"
                                      WHITESPACE@249..262 "\n            "
                                      R_CURLY@262..263 "}"
                                  WHITESPACE@263..264 " "
                                  ELSE_KW@264..268 "else"
                                  WHITESPACE@268..269 " "
                                  BLOCK_EXPR@269..302
                                    STMT_LIST@269..302
                                      L_CURLY@269..270 "{"
                                      WHITESPACE@270..287 "\n                "
                                      LITERAL@287..288
                                        INT_NUMBER@287..288 "5"
                                      WHITESPACE@288..301 "\n            "
                                      R_CURLY@301..302 "}"
                                WHITESPACE@302..311 "\n        "
                                R_CURLY@311..312 "}"
                        WHITESPACE@312..317 "\n    "
                        R_CURLY@317..318 "}"
                  SEMICOLON@318..319 ";"
                WHITESPACE@319..324 "\n    "
                EXPR_STMT@324..362
                  IF_EXPR@324..362
                    IF_KW@324..326 "if"
                    WHITESPACE@326..327 " "
                    BIN_EXPR@327..333
                      PATH_EXPR@327..328
                        PATH@327..328
                          PATH_SEGMENT@327..328
                            NAME_REF@327..328
                              IDENT@327..328 "m"
                      WHITESPACE@328..329 " "
                      EQ2@329..331 "=="
                      WHITESPACE@331..332 " "
                      LITERAL@332..333
                        INT_NUMBER@332..333 "0"
                    WHITESPACE@333..334 " "
                    BLOCK_EXPR@334..362
                      STMT_LIST@334..362
                        L_CURLY@334..335 "{"
                        WHITESPACE@335..344 "\n        "
                        EXPR_STMT@344..356
                          RETURN_EXPR@344..355
                            RETURN_KW@344..350 "return"
                            WHITESPACE@350..351 " "
                            PATH_EXPR@351..355
                              PATH@351..355
                                PATH_SEGMENT@351..355
                                  NAME_REF@351..355
                                    IDENT@351..355 "None"
                          SEMICOLON@355..356 ";"
                        WHITESPACE@356..361 "\n    "
                        R_CURLY@361..362 "}"
                WHITESPACE@362..367 "\n    "
                CALL_EXPR@367..374
                  PATH_EXPR@367..371
                    PATH@367..371
                      PATH_SEGMENT@367..371
                        NAME_REF@367..371
                          IDENT@367..371 "Some"
                  ARG_LIST@371..374
                    L_PAREN@371..372 "("
                    PATH_EXPR@372..373
                      PATH@372..373
                        PATH_SEGMENT@372..373
                          NAME_REF@372..373
                            IDENT@372..373 "m"
                    R_PAREN@373..374 ")"
                WHITESPACE@374..375 "\n"
                R_CURLY@375..376 "}"
          WHITESPACE@376..377 "\n"

    "#]]};
    const TEST_SRC: &str = {
r#"fn foo(n: u8) -> Option<u8> {
    let m = n.checked_sub(16)?;
    let _ = || 2;
    let _ = || {
        println!("xxx");
        if true {
            3
        } else if cond {
            0
        } else {
            if true {
                4
            } else {
                5
            }
        }
    };
    if m == 0 {
        return None;
    }
    Some(m)
}
"#};

    #[test]
    fn test_data() {
        let mut child = Command::new("rust-analyzer")
            .arg("parse")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .unwrap();
        child.stdin.as_mut().unwrap().write_all(TEST_SRC.as_bytes()).unwrap();
        let output = child.wait_with_output().unwrap().stdout;

        let output = String::from_utf8_lossy(&output);
        TEST_AST.assert_eq(&output);
        let node = make_node(TEST_AST.data());
        assert_eq!(usize::from(node.range.end()), TEST_SRC.len());
    }

    #[test]
    fn test_replace() {
        let mut s = TEST_SRC.to_string();
        let node = make_node(TEST_AST.data());
        let inserts = term_expr_inserts(&node, &s, Config { debug: Debug::Inline, ..Default::default() });
        apply_inserts(inserts, &mut s);
        expect![[r#"
            fn foo(n: u8) -> Option<u8> {trait _IsTryOk{fn is_try_ok(&self)->bool;}impl<T,E>_IsTryOk for ::core::result::Result<T,E>{fn is_try_ok(&self)->bool{self.is_ok()}}impl<T>_IsTryOk for ::core::option::Option<T>{fn is_try_ok(&self)->bool{self.is_some()}}macro_rules!_track{(!)=>(());(!$t:tt)=>($t);(@$s:tt,$($e:expr)?)=>({let __val = _track!(!$($e)?);if !_IsTryOk::is_try_ok(&__val){println!("[track] foo tryret{} at {}:{} = {__val:?}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!())}; __val });(+$s:tt,$($e:expr)?)=>({let __val = _track!(!$($e)?);println!("[track] foo return{} at {}:{} = {__val:?}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); __val });(%$s:tt,$($e:expr)?)=>({let __val = _track!(!$($e)?);println!("[track] foo endret{} at {}:{} = {__val:?}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); __val });(%$s:tt,$e:stmt $(;)?)=>({{$e};let __val = ();println!("[track] foo endret{} at {}:{} = {__val:?}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); });}println!("[track] foo enter     at {}:{}",::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!());
                let m = {_track!(@"'1 ",n.checked_sub(16))}?;
                let _ = || 2;
                let _ = /*closure'0 */|| {trait _IsTryOk{fn is_try_ok(&self)->bool;}impl<T,E>_IsTryOk for ::core::result::Result<T,E>{fn is_try_ok(&self)->bool{self.is_ok()}}impl<T>_IsTryOk for ::core::option::Option<T>{fn is_try_ok(&self)->bool{self.is_some()}}macro_rules!_track{(!)=>(());(!$t:tt)=>($t);(@$s:tt,$($e:expr)?)=>({let __val = _track!(!$($e)?);if !_IsTryOk::is_try_ok(&__val){println!("[track] closure'0  tryret{} at {}:{} = {__val:?}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!())}; __val });(+$s:tt,$($e:expr)?)=>({let __val = _track!(!$($e)?);println!("[track] closure'0  return{} at {}:{} = {__val:?}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); __val });(%$s:tt,$($e:expr)?)=>({let __val = _track!(!$($e)?);println!("[track] closure'0  endret{} at {}:{} = {__val:?}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); __val });(%$s:tt,$e:stmt $(;)?)=>({{$e};let __val = ();println!("[track] closure'0  endret{} at {}:{} = {__val:?}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); });}println!("[track] closure'0  enter     at {}:{}",::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!());{_track!{%"'2 ",{
                    println!("xxx");
                    if true {
                        3
                    } else if cond {
                        0
                    } else {
                        if true {
                            4
                        } else {
                            5
                        }
                    }
                }}}};
                if m == 0 {
                    return{_track!(+"'3 ", None)};
                }
                {_track!{%"'0 ",Some(m)}}
            }
        "#]].assert_eq(&s);
    }
}
