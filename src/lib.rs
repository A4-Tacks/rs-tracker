use std::borrow::Borrow;

use text::{is_complex_closure, ShowMark};
use smol_strc::{SmolStr, format_smolstr};
use text_size::{TextRange, TextSize};

mod kind;
mod text;
mod config;
pub use config::*;

pub mod node;
pub mod edits;
pub use node::*;

pub struct EditInsert<'input, 'node> {
    cfg: Config,
    src: &'input str,
    names: Vec<SmolStr>,
    inserts: Vec<(TextSize, SmolStr)>,
    mark: ShowMark,
    closures: ShowMark,
    ancestors: Vec<&'node Node>,
    ignored_level: u32,
}

impl<'input, 'node> EditInsert<'input, 'node> {
    pub fn create(src: &'input str, cfg: Config) -> Self {
        Self {
            cfg,
            src,
            names: vec![],
            inserts: vec![],
            mark: ShowMark(0.into()),
            closures: ShowMark(0.into()),
            ancestors: vec![],
            ignored_level: 0,
        }
    }

    pub fn generate_edits(mut self, node: &'node Node) -> Vec<(TextSize, SmolStr)> {
        node.visit(&mut |node, action| {
            match action {
                VisitAction::Enter => {
                    self.pre_enter(node);
                    self.on_enter(node);
                    self.post_enter(node);
                },
                VisitAction::Leave => self.on_leave(node),
            }
            None
        });
        assert!(self.ancestors.is_empty(), "{:#?}", self.ancestors);
        assert!(self.names.is_empty(), "{:#?}", self.names);
        self.inserts
    }

    fn text(&self, node: Option<&Node>) -> &'input str {
        node.map_or("<?>", |node| &self.src[node])
    }

    fn indent_of<I, N>(&self, a: I, u: &'input str) -> &'input str
    where I: IntoIterator<Item = &'node N>,
          I::IntoIter: DoubleEndedIterator,
          N: Borrow<Node> + 'node,
    {
        if self.cfg.inline {
            return "";
        }
        let ancestors = a.into_iter().map(|it| it.borrow());
        text::indent_of(self.src, ancestors).unwrap_or(u)
    }

    fn preattr(&self, block: &Block) -> &'static str {
        match block {
            Block::Fn => "#![cfg_attr(rustfmt, rustfmt::skip)]#![allow(unused_braces)]",
            _ => "",
        }
    }

    fn preset(&self) -> String {
        let name = self.names.last().unwrap();
        let pather = r#"::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1)"#;
        let iname = format_smolstr!(
            "[track] {}{name}",
            if self.cfg.indent_name { "  ".repeat(self.names.len().saturating_sub(1)) } else { String::new() },
        );
        let debug = match self.cfg.debug {
            Debug::Inline => " = {__s:?}",
            Debug::Expand => " = {__s:#?}",
            Debug::Disable => "",
        };
        let output = if self.cfg.stderr { "eprintln" } else { "println" };

        let ps = "let __s=_S(&__val);let __s=__s._s();";
        format!{"\
            trait _IsTryOk{{\
                fn is_try_ok(&self)->bool;\
            }}impl<T,E>_IsTryOk for ::core::result::Result<T,E>{{\
                fn is_try_ok(&self)->bool{{self.is_ok()}}\
            }}impl<T>_IsTryOk for ::core::option::Option<T>{{\
                fn is_try_ok(&self)->bool{{self.is_some()}}\
            }}\
            struct _S<T>(T);impl<T: ::core::fmt::Debug>_S<T>{{\
                fn _s(&self)->&T{{&self.0}}\
            }}\
            impl<T>::core::fmt::Debug for _S<T>{{\
                fn fmt(&self,f:&mut::core::fmt::Formatter<'_>)->::core::fmt::Result{{\
                    f.write_str(\"<opaque>\")\
                }}\
            }}\
            trait _Opaque {{fn _s(&self)->&Self{{self}}}}impl<T>_Opaque for _S<T>{{}}\
            macro_rules!_track{{\
                (!)=>(());\
                (!$t:tt)=>($t);\
                (@$s:tt,$($e:expr)?)=>({{let __val = _track!(!$($e)?);if !_IsTryOk::is_try_ok(&__val){{{ps}{output}!(\
                    \"{iname} tryret{{}} at {{}}:{{}}{debug}\",\
                    $s,{pather},::core::line!())}}; __val }});\
                (+$s:tt,$($e:expr)?)=>({{let __val = _track!(!$($e)?);{ps}{output}!(\
                    \"{iname} return{{}} at {{}}:{{}}{debug}\",\
                    $s,{pather},::core::line!()); __val }});\
                (%$s:tt,$($e:expr)?)=>({{let __val = _track!(!$($e)?);{ps}{output}!(\
                    \"{iname} endret{{}} at {{}}:{{}}{debug}\",\
                    $s,{pather},::core::line!()); __val }});\
                (%$s:tt,$e:stmt $(;)?)=>({{{{$e}};let __val = ();{ps}{output}!(\
                    \"{iname} endret{{}} at {{}}:{{}}{debug}\",\
                    $s,{pather},::core::line!()); }});\
                (*$s:tt)=>({{{output}!(\
                    \"{iname} labels{{}} at {{}}:{{}}\",\
                    $s,{pather},::core::line!()); }});\
                (*$s:tt,$n:ident)=>({{let __val = &$n;{ps}{output}!(\
                    \"{iname} labels{{}} at {{}}:{{}} let {{}}{debug}\",\
                    $s,{pather},::core::line!(),::core::stringify!($n)); }});\
            }}\
            {output}!(\"{iname} enter      at {{}}:{{}}\",{pather},::core::line!());\
        "}
    }

    fn needs_track(&self, node: &Node) -> bool {
        match node.kind.as_str() {
            "FN" => true,
            "CLOSURE_EXPR" => true,
            _ => false,
        }
    }

    fn needs_ignore_descendants(&self, name: &str) -> bool {
        let included = self.cfg.included.is_empty() || self.cfg.included.is_match(name);
        let matched = included && !self.cfg.excluded.is_match(name);
        !matched
    }

    fn on_leave(&mut self, node: &Node) {
        if self.needs_track(node) {
            let name = self.names.pop().unwrap();

            if self.needs_ignore_descendants(&name) {
                self.ignored_level = self.ignored_level.checked_sub(1).unwrap();
            }
        }
        self.ancestors.pop().unwrap();
    }

    fn pre_enter(&mut self, node: &'node Node) {
        if self.needs_track(node) {
            let name = match node.kind.as_str() {
                "FN" => self.text(node.find_children("NAME")).into(),
                "CLOSURE_EXPR" if is_complex_closure(node) => format_smolstr!("closure{}", self.closures),
                "CLOSURE_EXPR" => "".into(),
                _ => unreachable!(),
            };

            if self.needs_ignore_descendants(&name) {
                self.ignored_level += 1;
            }

            self.names.push(name);
        }
    }

    fn post_enter(&mut self, node: &'node Node) {
        self.ancestors.push(node);
    }

    fn on_enter(&mut self, node: &Node) -> Option<()> {
        if self.ignored_level != 0 {
            return None;
        }
        let indent = self.indent_of(&self.ancestors, "\n");
        let block = Block::with(self.ancestors.iter().rev().map(|it| it.kind.as_str()));
        let preattr = self.preattr(&block);

        macro_rules! at {
            ($at:expr, $($t:tt)*) => {
                self.inserts.push(($at, format_smolstr!($($t)*)));
            };
        }

        let src = self.src;
        let mark = &self.mark;
        let tracked = !self.names.is_empty();
        let (label_stmt, label_lets) = (self.cfg.label_stmt&tracked, self.cfg.label_lets&tracked);

        match node.kind.as_str() {
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
            "CLOSURE_EXPR" if !self.cfg.only_fn && is_complex_closure(node) => {
                let tail = node.sub().last()?;

                at!(node.start(), "/*{}*/", self.names.last().unwrap());
                at!(tail.start(), r#"{{{preattr}{}"#, self.preset());

                each_value_expr_leafs(tail, &mut |tail| {
                    at!(tail.start(), r#"{{_track!{{%"{mark}","#);
                    at!(tail.end(), r#"}}}}"#);
                });

                at!(tail.end(), r#"}}"#);
            }
            "STMT_LIST" => match block {
                Block::Fn => {
                    let l_curly = node.find_children("L_CURLY")?;
                    let after = stmt_list_content_after(node)?;
                    at!(l_curly.end(), "{preattr}");
                    at!(after, "{}", self.preset());
                    let mut has_ret = false;

                    each_value_expr_leafs(node, &mut |tail| {
                        let mut start = tail.start();
                        if let Some(last) = tail.sub().iter()
                            .take_while(|it| kind::is_trivia(it) || it.kind == "ATTR").last()
                        {
                            start = last.end();
                        }
                        at!(start, r#"{{_track!{{%"{mark}","#);
                        at!(tail.end(), r#"}}}}"#);
                        has_ret = true;
                    });

                    if !has_ret {
                        let (tail, _) = node.split_once("R_CURLY")?;
                        let tail = tail.iter().rfind(|it| !kind::is_trivia(*it))?;
                        let indent = self.indent_of([node], "");
                        at!(tail.end(), r#"{indent}{{_track!{{%"{mark}",}}}}"#);
                    }
                },
                Block::Closure => {},
                Block::None => if label_stmt {
                    let l_curly = node.find_children("L_CURLY")?;
                    let indent = self.indent_of([node], "");
                    at!(l_curly.end(), r#"{indent}{{_track!(*"{mark}");}}"#);
                }
            }
            "LET_STMT" => if label_lets && node.find_children("EQ").is_some() {
                for bind in pat_binds(node) {
                    let bind = &src[bind];
                    at!(node.end(), r#"{indent}{{_track!(*"{mark}", {bind});}}"#);
                }
            } else if label_stmt {
                at!(node.end(), r#"{indent}{{_track!(*"{mark}");}}"#);
            }
            "EXPR_STMT" => if label_stmt && !like_jumping(node, src) {
                at!(node.end(), r#"{indent}{{_track!(*"{mark}");}}"#);
            }
            _ => {}
        }

        None
    }
}

fn each_value_expr_leafs(tail: &Node, handler: &mut impl FnMut(&Node)) -> Option<()> {
    match tail.kind.as_str() {
        "MATCH_EXPR" => {
            tail.find_children("MATCH_ARM_LIST")?
                .sub().iter().filter(|it| it.kind == "MATCH_ARM")
                .for_each(|leaf| {
                    if let Some(expr) = leaf.sub().iter()
                        .rev()
                        .filter(|it| !kind::is_trivia(*it))
                        .take_while(|it| it.kind != "FAT_ARROW")
                        .find(|it| it.kind != "COMMA")
                    {
                        if each_value_expr_leafs(expr, handler).is_none() {
                            handler(expr)
                        }
                    }
                });
        }
        "BLOCK_EXPR" => each_value_expr_leafs(tail.find_children("STMT_LIST")?, handler)?,
        "STMT_LIST" => {
            let tail_expr = tail.sub().iter().rfind(|it| {
                kind::is_content(*it) && !kind::is_item_or_let(*it)
                    && it.kind != "EXPR_STMT"
            })?;
            each_value_expr_leafs(tail_expr, handler)?
        }
        "IF_EXPR" if tail.find_children("ELSE_KW").is_some() => {
            let (bef, aft) = tail.split_once("ELSE_KW").unwrap();
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

fn pat_binds(node: &Node) -> Vec<TextRange> {
    match node.kind.as_str() {
        "IDENT_PAT" => {
            node.find_children("NAME")
                .map(|it| it.range())
                .into_iter()
                .collect()
        }
        "RECORD_PAT" => {
            node.find_children("RECORD_PAT_FIELD_LIST")
                .into_iter()
                .flat_map(|it| it.sub())
                .filter(|it| it.kind == "RECORD_PAT_FIELD")
                .flat_map(pat_binds)
                .collect()
        }
        "TUPLE_PAT" | "TUPLE_STRUCT_PAT" | "LET_STMT" | "LET_EXPR" | "RECORD_PAT_FIELD" => {
            node.sub().iter().flat_map(pat_binds).collect()
        }
        _ => vec![],
    }
}

fn like_jumping(node: &Node, src: &str) -> bool {
    node.any(|node| {
        if node.kind == "MACRO_EXPR"
            && let Some(mcall) = node.find_children("MACRO_CALL")
            && let Some(path) = mcall.find_children("PATH")
            && like_panic(&src[path])
        {
            return true;
        }
        kind::is_jumping(node)
    })
}

fn like_panic(path: &str) -> bool {
    let name = path.rsplit_once(':').map_or(path, |it| it.1);
    matches!(name, "panic" | "unreachable" | "todo" | "unimplemented")
}

fn stmt_list_content_after(node: &Node) -> Option<TextSize> {
    assert_eq!(node.kind.as_str(), "STMT_LIST");
    let l_curly = node.find_children("L_CURLY")?;

    // 不考虑内部文档注释, 想在内部文档注释后插入很麻烦
    node.find_childrens(kind::Pred(kind::is_attr)).last()
        .unwrap_or(l_curly)
        .end()
        .into()
}

enum Block {
    Fn,
    Closure,
    None,
}
impl Block {
    fn with<'a>(ancestors: impl IntoIterator<Item = &'a str>) -> Self {
        let mut iter = ancestors.into_iter().peekable();
        iter.next_if(|it| *it == "STMT_LIST");
        iter.next_if(|it| *it == "BLOCK_EXPR");
        match iter.next().unwrap_or("") {
            "FN" => Self::Fn,
            "CLOSURE_EXPR" => Self::Closure,
            _ => Self::None,
        }
    }
}

mod remove_handles;
pub use remove_handles::remove_tracks;

#[cfg(test)]
mod tests {
    use std::{io::Write, process::{Command, Stdio}};

    use contains_match::{Pattern, PatternSet};
    use expect_test::{expect, Expect};

    use super::*;

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

    fn parse_source(source: &str) -> Node {
        let mut child = Command::new("rust-analyzer")
            .arg("parse")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .unwrap();
        child.stdin.as_mut().unwrap().write_all(source.as_bytes()).unwrap();
        let output = child.wait_with_output().unwrap().stdout;
        let output = String::from_utf8_lossy(&output);

        let node = make(&output);
        assert_eq!(usize::from(node.end()), source.len(), "{node:#?}");
        node
    }

    fn trim_indent(src: &str) -> String {
        let src = src.trim_matches(['\n', '\r']);
        let indent = src.lines().filter(|it| !it.is_empty())
            .map(|line| {
                let trimmed = line.trim_start_matches(' ');
                line.len() - trimmed.len()
            })
            .min()
            .unwrap_or_default();
        src.split_inclusive('\n')
            .map(|it| it.get(indent..).unwrap_or(it))
            .collect()
    }

    fn format_chunks(chunks: Vec<dissimilar::Chunk>) {
        for chunk in chunks {
            match chunk {
                dissimilar::Chunk::Equal(text) => print!("{text}"),
                dissimilar::Chunk::Delete(text) => print!("\x1b[41m{}\x1b[0m", text),
                dissimilar::Chunk::Insert(text) => print!("\x1b[42m{}\x1b[0m", text),
            }
        }
    }

    fn term_expr_inserts(
        node: &Node,
        src: &str,
        cfg: Config,
    ) -> Vec<(TextSize, SmolStr)> {
        EditInsert::create(src, cfg).generate_edits(node)
    }

    #[track_caller]
    fn check_apply_and_remove(pass: u32, cfg: Config, src: &str, expect: Expect) {
        let source = trim_indent(src);
        let mut s = source.clone();
        let node = parse_source(&s);
        let inserts = term_expr_inserts(&node, &s, cfg);
        edits::apply_inserts(inserts, &mut s);
        expect.assert_eq(&s);


        for pass in 0..pass {
            let node = parse_source(&s);
            let removes = remove_tracks(&node, &s);
            assert!(!removes.is_empty(), "redundant pass: {pass}");
            edits::apply_deletes(removes, &mut s);
        }

        if s != source {
            println!("============== Source ==============\n{source}");
            println!("============== Actual ==============\n{s}");
            println!("==============  Diff  ==============");
            format_chunks(dissimilar::diff(&source, &s));
            println!();
            panic!()
        }
    }

    #[test]
    fn test_replace() {
        let mut s = TEST_SRC.to_string();
        let node = parse_source(TEST_SRC);
        let inserts = term_expr_inserts(&node, &s, Config { debug: Debug::Inline, ..Default::default() });
        edits::apply_inserts(inserts, &mut s);
        expect![[r#"
            fn foo(n: u8) -> Option<u8> {#![cfg_attr(rustfmt, rustfmt::skip)]#![allow(unused_braces)]trait _IsTryOk{fn is_try_ok(&self)->bool;}impl<T,E>_IsTryOk for ::core::result::Result<T,E>{fn is_try_ok(&self)->bool{self.is_ok()}}impl<T>_IsTryOk for ::core::option::Option<T>{fn is_try_ok(&self)->bool{self.is_some()}}struct _S<T>(T);impl<T: ::core::fmt::Debug>_S<T>{fn _s(&self)->&T{&self.0}}impl<T>::core::fmt::Debug for _S<T>{fn fmt(&self,f:&mut::core::fmt::Formatter<'_>)->::core::fmt::Result{f.write_str("<opaque>")}}trait _Opaque {fn _s(&self)->&Self{self}}impl<T>_Opaque for _S<T>{}macro_rules!_track{(!)=>(());(!$t:tt)=>($t);(@$s:tt,$($e:expr)?)=>({let __val = _track!(!$($e)?);if !_IsTryOk::is_try_ok(&__val){let __s=_S(&__val);let __s=__s._s();println!("[track] foo tryret{} at {}:{} = {__s:?}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!())}; __val });(+$s:tt,$($e:expr)?)=>({let __val = _track!(!$($e)?);let __s=_S(&__val);let __s=__s._s();println!("[track] foo return{} at {}:{} = {__s:?}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); __val });(%$s:tt,$($e:expr)?)=>({let __val = _track!(!$($e)?);let __s=_S(&__val);let __s=__s._s();println!("[track] foo endret{} at {}:{} = {__s:?}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); __val });(%$s:tt,$e:stmt $(;)?)=>({{$e};let __val = ();let __s=_S(&__val);let __s=__s._s();println!("[track] foo endret{} at {}:{} = {__s:?}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); });(*$s:tt)=>({println!("[track] foo labels{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); });(*$s:tt,$n:ident)=>({let __val = &$n;let __s=_S(&__val);let __s=__s._s();println!("[track] foo labels{} at {}:{} let {} = {__s:?}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!(),::core::stringify!($n)); });}println!("[track] foo enter      at {}:{}",::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!());
                let m = {_track!(@"'1  ",n.checked_sub(16))}?;
                let _ = || 2;
                let _ = /*closure'0  */|| {trait _IsTryOk{fn is_try_ok(&self)->bool;}impl<T,E>_IsTryOk for ::core::result::Result<T,E>{fn is_try_ok(&self)->bool{self.is_ok()}}impl<T>_IsTryOk for ::core::option::Option<T>{fn is_try_ok(&self)->bool{self.is_some()}}struct _S<T>(T);impl<T: ::core::fmt::Debug>_S<T>{fn _s(&self)->&T{&self.0}}impl<T>::core::fmt::Debug for _S<T>{fn fmt(&self,f:&mut::core::fmt::Formatter<'_>)->::core::fmt::Result{f.write_str("<opaque>")}}trait _Opaque {fn _s(&self)->&Self{self}}impl<T>_Opaque for _S<T>{}macro_rules!_track{(!)=>(());(!$t:tt)=>($t);(@$s:tt,$($e:expr)?)=>({let __val = _track!(!$($e)?);if !_IsTryOk::is_try_ok(&__val){let __s=_S(&__val);let __s=__s._s();println!("[track] closure'0   tryret{} at {}:{} = {__s:?}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!())}; __val });(+$s:tt,$($e:expr)?)=>({let __val = _track!(!$($e)?);let __s=_S(&__val);let __s=__s._s();println!("[track] closure'0   return{} at {}:{} = {__s:?}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); __val });(%$s:tt,$($e:expr)?)=>({let __val = _track!(!$($e)?);let __s=_S(&__val);let __s=__s._s();println!("[track] closure'0   endret{} at {}:{} = {__s:?}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); __val });(%$s:tt,$e:stmt $(;)?)=>({{$e};let __val = ();let __s=_S(&__val);let __s=__s._s();println!("[track] closure'0   endret{} at {}:{} = {__s:?}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); });(*$s:tt)=>({println!("[track] closure'0   labels{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); });(*$s:tt,$n:ident)=>({let __val = &$n;let __s=_S(&__val);let __s=__s._s();println!("[track] closure'0   labels{} at {}:{} let {} = {__s:?}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!(),::core::stringify!($n)); });}println!("[track] closure'0   enter      at {}:{}",::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!());{
                    println!("xxx");
                    if true {
                        {_track!{%"'2  ",3}}
                    } else if cond {
                        {_track!{%"'3  ",0}}
                    } else {
                        if true {
                            {_track!{%"'4  ",4}}
                        } else {
                            {_track!{%"'5  ",5}}
                        }
                    }
                }};
                if m == 0 {
                    return{_track!(+"'6  ", None)};
                }
                {_track!{%"'0  ",Some(m)}}
            }
        "#]].assert_eq(&s);
    }

    #[test]
    fn test_only_fn_replace() {
        let mut s = TEST_SRC.to_string();
        let node = parse_source(TEST_SRC);
        let inserts = term_expr_inserts(&node, &s, Config { only_fn: true, ..Default::default() });
        edits::apply_inserts(inserts, &mut s);
        expect![[r#"
            fn foo(n: u8) -> Option<u8> {#![cfg_attr(rustfmt, rustfmt::skip)]#![allow(unused_braces)]trait _IsTryOk{fn is_try_ok(&self)->bool;}impl<T,E>_IsTryOk for ::core::result::Result<T,E>{fn is_try_ok(&self)->bool{self.is_ok()}}impl<T>_IsTryOk for ::core::option::Option<T>{fn is_try_ok(&self)->bool{self.is_some()}}struct _S<T>(T);impl<T: ::core::fmt::Debug>_S<T>{fn _s(&self)->&T{&self.0}}impl<T>::core::fmt::Debug for _S<T>{fn fmt(&self,f:&mut::core::fmt::Formatter<'_>)->::core::fmt::Result{f.write_str("<opaque>")}}trait _Opaque {fn _s(&self)->&Self{self}}impl<T>_Opaque for _S<T>{}macro_rules!_track{(!)=>(());(!$t:tt)=>($t);(@$s:tt,$($e:expr)?)=>({let __val = _track!(!$($e)?);if !_IsTryOk::is_try_ok(&__val){let __s=_S(&__val);let __s=__s._s();println!("[track] foo tryret{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!())}; __val });(+$s:tt,$($e:expr)?)=>({let __val = _track!(!$($e)?);let __s=_S(&__val);let __s=__s._s();println!("[track] foo return{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); __val });(%$s:tt,$($e:expr)?)=>({let __val = _track!(!$($e)?);let __s=_S(&__val);let __s=__s._s();println!("[track] foo endret{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); __val });(%$s:tt,$e:stmt $(;)?)=>({{$e};let __val = ();let __s=_S(&__val);let __s=__s._s();println!("[track] foo endret{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); });(*$s:tt)=>({println!("[track] foo labels{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); });(*$s:tt,$n:ident)=>({let __val = &$n;let __s=_S(&__val);let __s=__s._s();println!("[track] foo labels{} at {}:{} let {}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!(),::core::stringify!($n)); });}println!("[track] foo enter      at {}:{}",::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!());
                let m = {_track!(@"'1  ",n.checked_sub(16))}?;
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
                    return{_track!(+"'2  ", None)};
                }
                {_track!{%"'0  ",Some(m)}}
            }
        "#]].assert_eq(&s);
    }

    #[test]
    fn test_attr_tail_return() {
        let mut s = trim_indent(r#"
        fn foo() {
            let x = 2;
            #[cfg(test)]
            if cond {}
        }
        "#);
        let node = parse_source(&s);
        let inserts = term_expr_inserts(&node, &s, Config { ..Default::default() });
        edits::apply_inserts(inserts, &mut s);
        expect![[r#"
            fn foo() {#![cfg_attr(rustfmt, rustfmt::skip)]#![allow(unused_braces)]trait _IsTryOk{fn is_try_ok(&self)->bool;}impl<T,E>_IsTryOk for ::core::result::Result<T,E>{fn is_try_ok(&self)->bool{self.is_ok()}}impl<T>_IsTryOk for ::core::option::Option<T>{fn is_try_ok(&self)->bool{self.is_some()}}struct _S<T>(T);impl<T: ::core::fmt::Debug>_S<T>{fn _s(&self)->&T{&self.0}}impl<T>::core::fmt::Debug for _S<T>{fn fmt(&self,f:&mut::core::fmt::Formatter<'_>)->::core::fmt::Result{f.write_str("<opaque>")}}trait _Opaque {fn _s(&self)->&Self{self}}impl<T>_Opaque for _S<T>{}macro_rules!_track{(!)=>(());(!$t:tt)=>($t);(@$s:tt,$($e:expr)?)=>({let __val = _track!(!$($e)?);if !_IsTryOk::is_try_ok(&__val){let __s=_S(&__val);let __s=__s._s();println!("[track] foo tryret{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!())}; __val });(+$s:tt,$($e:expr)?)=>({let __val = _track!(!$($e)?);let __s=_S(&__val);let __s=__s._s();println!("[track] foo return{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); __val });(%$s:tt,$($e:expr)?)=>({let __val = _track!(!$($e)?);let __s=_S(&__val);let __s=__s._s();println!("[track] foo endret{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); __val });(%$s:tt,$e:stmt $(;)?)=>({{$e};let __val = ();let __s=_S(&__val);let __s=__s._s();println!("[track] foo endret{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); });(*$s:tt)=>({println!("[track] foo labels{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); });(*$s:tt,$n:ident)=>({let __val = &$n;let __s=_S(&__val);let __s=__s._s();println!("[track] foo labels{} at {}:{} let {}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!(),::core::stringify!($n)); });}println!("[track] foo enter      at {}:{}",::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!());
                let x = 2;
                #[cfg(test)]
                {_track!{%"'0  ",if cond {}}}
            }
        "#]].assert_eq(&s);
    }

    #[test]
    fn test_inner_attr() {
        let mut s = trim_indent(r#"
        fn foo() {
            #![cfg_attr(docsrs, doc(cfg(x)))]
            let x = 2;
            #[cfg(test)]
            if cond {}
        }
        "#);
        let node = parse_source(&s);
        let inserts = term_expr_inserts(&node, &s, Config { ..Default::default() });
        edits::apply_inserts(inserts, &mut s);
        expect![[r#"
            fn foo() {#![cfg_attr(rustfmt, rustfmt::skip)]#![allow(unused_braces)]
                #![cfg_attr(docsrs, doc(cfg(x)))]trait _IsTryOk{fn is_try_ok(&self)->bool;}impl<T,E>_IsTryOk for ::core::result::Result<T,E>{fn is_try_ok(&self)->bool{self.is_ok()}}impl<T>_IsTryOk for ::core::option::Option<T>{fn is_try_ok(&self)->bool{self.is_some()}}struct _S<T>(T);impl<T: ::core::fmt::Debug>_S<T>{fn _s(&self)->&T{&self.0}}impl<T>::core::fmt::Debug for _S<T>{fn fmt(&self,f:&mut::core::fmt::Formatter<'_>)->::core::fmt::Result{f.write_str("<opaque>")}}trait _Opaque {fn _s(&self)->&Self{self}}impl<T>_Opaque for _S<T>{}macro_rules!_track{(!)=>(());(!$t:tt)=>($t);(@$s:tt,$($e:expr)?)=>({let __val = _track!(!$($e)?);if !_IsTryOk::is_try_ok(&__val){let __s=_S(&__val);let __s=__s._s();println!("[track] foo tryret{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!())}; __val });(+$s:tt,$($e:expr)?)=>({let __val = _track!(!$($e)?);let __s=_S(&__val);let __s=__s._s();println!("[track] foo return{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); __val });(%$s:tt,$($e:expr)?)=>({let __val = _track!(!$($e)?);let __s=_S(&__val);let __s=__s._s();println!("[track] foo endret{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); __val });(%$s:tt,$e:stmt $(;)?)=>({{$e};let __val = ();let __s=_S(&__val);let __s=__s._s();println!("[track] foo endret{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); });(*$s:tt)=>({println!("[track] foo labels{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); });(*$s:tt,$n:ident)=>({let __val = &$n;let __s=_S(&__val);let __s=__s._s();println!("[track] foo labels{} at {}:{} let {}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!(),::core::stringify!($n)); });}println!("[track] foo enter      at {}:{}",::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!());
                let x = 2;
                #[cfg(test)]
                {_track!{%"'0  ",if cond {}}}
            }
        "#]].assert_eq(&s);
    }

    #[test]
    fn test_no_tail_return() {
        let source = r#"
        fn foo() {
            let x = 2;
        }
        "#;
        let cfg = Config { label_stmt: true, ..Default::default() };
        check_apply_and_remove(1, cfg, source, expect![[r#"
            fn foo() {#![cfg_attr(rustfmt, rustfmt::skip)]#![allow(unused_braces)]trait _IsTryOk{fn is_try_ok(&self)->bool;}impl<T,E>_IsTryOk for ::core::result::Result<T,E>{fn is_try_ok(&self)->bool{self.is_ok()}}impl<T>_IsTryOk for ::core::option::Option<T>{fn is_try_ok(&self)->bool{self.is_some()}}struct _S<T>(T);impl<T: ::core::fmt::Debug>_S<T>{fn _s(&self)->&T{&self.0}}impl<T>::core::fmt::Debug for _S<T>{fn fmt(&self,f:&mut::core::fmt::Formatter<'_>)->::core::fmt::Result{f.write_str("<opaque>")}}trait _Opaque {fn _s(&self)->&Self{self}}impl<T>_Opaque for _S<T>{}macro_rules!_track{(!)=>(());(!$t:tt)=>($t);(@$s:tt,$($e:expr)?)=>({let __val = _track!(!$($e)?);if !_IsTryOk::is_try_ok(&__val){let __s=_S(&__val);let __s=__s._s();println!("[track] foo tryret{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!())}; __val });(+$s:tt,$($e:expr)?)=>({let __val = _track!(!$($e)?);let __s=_S(&__val);let __s=__s._s();println!("[track] foo return{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); __val });(%$s:tt,$($e:expr)?)=>({let __val = _track!(!$($e)?);let __s=_S(&__val);let __s=__s._s();println!("[track] foo endret{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); __val });(%$s:tt,$e:stmt $(;)?)=>({{$e};let __val = ();let __s=_S(&__val);let __s=__s._s();println!("[track] foo endret{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); });(*$s:tt)=>({println!("[track] foo labels{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); });(*$s:tt,$n:ident)=>({let __val = &$n;let __s=_S(&__val);let __s=__s._s();println!("[track] foo labels{} at {}:{} let {}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!(),::core::stringify!($n)); });}println!("[track] foo enter      at {}:{}",::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!());
                let x = 2;
                {_track!{%"'0  ",}}
                {_track!(*"'1  ");}
            }
        "#]]);

        let source = r#"
        fn foo() {
            let x = 2;
        }
        "#;
        let cfg = Config { label_stmt: true, inline: true, ..Default::default() };
        check_apply_and_remove(1, cfg, source, expect![[r#"
            fn foo() {#![cfg_attr(rustfmt, rustfmt::skip)]#![allow(unused_braces)]trait _IsTryOk{fn is_try_ok(&self)->bool;}impl<T,E>_IsTryOk for ::core::result::Result<T,E>{fn is_try_ok(&self)->bool{self.is_ok()}}impl<T>_IsTryOk for ::core::option::Option<T>{fn is_try_ok(&self)->bool{self.is_some()}}struct _S<T>(T);impl<T: ::core::fmt::Debug>_S<T>{fn _s(&self)->&T{&self.0}}impl<T>::core::fmt::Debug for _S<T>{fn fmt(&self,f:&mut::core::fmt::Formatter<'_>)->::core::fmt::Result{f.write_str("<opaque>")}}trait _Opaque {fn _s(&self)->&Self{self}}impl<T>_Opaque for _S<T>{}macro_rules!_track{(!)=>(());(!$t:tt)=>($t);(@$s:tt,$($e:expr)?)=>({let __val = _track!(!$($e)?);if !_IsTryOk::is_try_ok(&__val){let __s=_S(&__val);let __s=__s._s();println!("[track] foo tryret{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!())}; __val });(+$s:tt,$($e:expr)?)=>({let __val = _track!(!$($e)?);let __s=_S(&__val);let __s=__s._s();println!("[track] foo return{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); __val });(%$s:tt,$($e:expr)?)=>({let __val = _track!(!$($e)?);let __s=_S(&__val);let __s=__s._s();println!("[track] foo endret{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); __val });(%$s:tt,$e:stmt $(;)?)=>({{$e};let __val = ();let __s=_S(&__val);let __s=__s._s();println!("[track] foo endret{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); });(*$s:tt)=>({println!("[track] foo labels{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); });(*$s:tt,$n:ident)=>({let __val = &$n;let __s=_S(&__val);let __s=__s._s();println!("[track] foo labels{} at {}:{} let {}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!(),::core::stringify!($n)); });}println!("[track] foo enter      at {}:{}",::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!());
                let x = 2;{_track!{%"'0  ",}}{_track!(*"'1  ");}
            }
        "#]]);
    }

    #[test]
    fn test_lebel_stmts() {
        let source = r#"
        fn foo() {
            let x = 2;
            bar(x);
            match () {
                () => x /* ... */,
                () => {
                    let _ = 3;
                    x
                }
                () => (),
                () => {},
                () => {
                    baz()?
                },
                () => {
                    let _ = 3;
                    return;
                }
                () => {
                    let _ = 3;
                    break;
                }
                () => {
                    let _ = 3;
                    unreachable!();
                }
            }
        }
        const NO: () = {
            let _ = ();
            ()
        };
        static NO: () = {
            let _ = ();
            ()
        };
        "#;
        let cfg = Config { label_stmt: true, ..Default::default() };
        check_apply_and_remove(2, cfg, source, expect![[r#"
            fn foo() {#![cfg_attr(rustfmt, rustfmt::skip)]#![allow(unused_braces)]trait _IsTryOk{fn is_try_ok(&self)->bool;}impl<T,E>_IsTryOk for ::core::result::Result<T,E>{fn is_try_ok(&self)->bool{self.is_ok()}}impl<T>_IsTryOk for ::core::option::Option<T>{fn is_try_ok(&self)->bool{self.is_some()}}struct _S<T>(T);impl<T: ::core::fmt::Debug>_S<T>{fn _s(&self)->&T{&self.0}}impl<T>::core::fmt::Debug for _S<T>{fn fmt(&self,f:&mut::core::fmt::Formatter<'_>)->::core::fmt::Result{f.write_str("<opaque>")}}trait _Opaque {fn _s(&self)->&Self{self}}impl<T>_Opaque for _S<T>{}macro_rules!_track{(!)=>(());(!$t:tt)=>($t);(@$s:tt,$($e:expr)?)=>({let __val = _track!(!$($e)?);if !_IsTryOk::is_try_ok(&__val){let __s=_S(&__val);let __s=__s._s();println!("[track] foo tryret{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!())}; __val });(+$s:tt,$($e:expr)?)=>({let __val = _track!(!$($e)?);let __s=_S(&__val);let __s=__s._s();println!("[track] foo return{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); __val });(%$s:tt,$($e:expr)?)=>({let __val = _track!(!$($e)?);let __s=_S(&__val);let __s=__s._s();println!("[track] foo endret{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); __val });(%$s:tt,$e:stmt $(;)?)=>({{$e};let __val = ();let __s=_S(&__val);let __s=__s._s();println!("[track] foo endret{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); });(*$s:tt)=>({println!("[track] foo labels{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); });(*$s:tt,$n:ident)=>({let __val = &$n;let __s=_S(&__val);let __s=__s._s();println!("[track] foo labels{} at {}:{} let {}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!(),::core::stringify!($n)); });}println!("[track] foo enter      at {}:{}",::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!());
                let x = 2;
                {_track!(*"'8  ");}
                bar(x);
                {_track!(*"'9  ");}
                match () {
                    () => {_track!{%"'0  ",x}} /* ... */,
                    () => {
                        {_track!(*"'10 ");}
                        let _ = 3;
                        {_track!(*"'11 ");}
                        {_track!{%"'1  ",x}}
                    }
                    () => {_track!{%"'2  ",()}},
                    () => {_track!{%"'3  ",{{_track!(*"'12 ");}}}},
                    () => {
                        {_track!(*"'13 ");}
                        {_track!{%"'4  ",{_track!(@"'14 ",baz())}?}}
                    },
                    () => {_track!{%"'5  ",{
                        {_track!(*"'15 ");}
                        let _ = 3;
                        {_track!(*"'16 ");}
                        return{_track!(+"'17 ",)};
                    }}}
                    () => {_track!{%"'6  ",{
                        {_track!(*"'18 ");}
                        let _ = 3;
                        {_track!(*"'19 ");}
                        break;
                    }}}
                    () => {_track!{%"'7  ",{
                        {_track!(*"'20 ");}
                        let _ = 3;
                        {_track!(*"'21 ");}
                        unreachable!();
                    }}}
                }
            }
            const NO: () = {
                let _ = ();
                ()
            };
            static NO: () = {
                let _ = ();
                ()
            };
        "#]]);
    }

    #[test]
    fn test_lebel_let_stmts() {
        let source = r#"
        fn foo() {
            let x = 2;
            bar(x);
            let (mut y, (z, t)) = (2, (3, 4));
            let (Foo { m }, Bar(n)) = todo!();
            let uninit;
            ()
        }
        "#;
        let cfg = Config { label_lets: true, ..Default::default() };
        check_apply_and_remove(1, cfg, source, expect![[r#"
            fn foo() {#![cfg_attr(rustfmt, rustfmt::skip)]#![allow(unused_braces)]trait _IsTryOk{fn is_try_ok(&self)->bool;}impl<T,E>_IsTryOk for ::core::result::Result<T,E>{fn is_try_ok(&self)->bool{self.is_ok()}}impl<T>_IsTryOk for ::core::option::Option<T>{fn is_try_ok(&self)->bool{self.is_some()}}struct _S<T>(T);impl<T: ::core::fmt::Debug>_S<T>{fn _s(&self)->&T{&self.0}}impl<T>::core::fmt::Debug for _S<T>{fn fmt(&self,f:&mut::core::fmt::Formatter<'_>)->::core::fmt::Result{f.write_str("<opaque>")}}trait _Opaque {fn _s(&self)->&Self{self}}impl<T>_Opaque for _S<T>{}macro_rules!_track{(!)=>(());(!$t:tt)=>($t);(@$s:tt,$($e:expr)?)=>({let __val = _track!(!$($e)?);if !_IsTryOk::is_try_ok(&__val){let __s=_S(&__val);let __s=__s._s();println!("[track] foo tryret{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!())}; __val });(+$s:tt,$($e:expr)?)=>({let __val = _track!(!$($e)?);let __s=_S(&__val);let __s=__s._s();println!("[track] foo return{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); __val });(%$s:tt,$($e:expr)?)=>({let __val = _track!(!$($e)?);let __s=_S(&__val);let __s=__s._s();println!("[track] foo endret{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); __val });(%$s:tt,$e:stmt $(;)?)=>({{$e};let __val = ();let __s=_S(&__val);let __s=__s._s();println!("[track] foo endret{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); });(*$s:tt)=>({println!("[track] foo labels{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); });(*$s:tt,$n:ident)=>({let __val = &$n;let __s=_S(&__val);let __s=__s._s();println!("[track] foo labels{} at {}:{} let {}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!(),::core::stringify!($n)); });}println!("[track] foo enter      at {}:{}",::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!());
                let x = 2;
                {_track!(*"'1  ", x);}
                bar(x);
                let (mut y, (z, t)) = (2, (3, 4));
                {_track!(*"'2  ", y);}
                {_track!(*"'3  ", z);}
                {_track!(*"'4  ", t);}
                let (Foo { m }, Bar(n)) = todo!();
                {_track!(*"'5  ", m);}
                {_track!(*"'6  ", n);}
                let uninit;
                {_track!{%"'0  ",()}}
            }
        "#]]);
    }

    #[test]
    fn test_excluded_fn() {
        let source = r#"
        fn foo() {
            let x = 2;
            bar(x);
        }
        fn bar() {
            fn baz() {
                let x = 2;
                f(x)
            }
            f(baz())
        }
        "#;
        let excluded = PatternSet::from_iter([
            Pattern::new("bar").unwrap()
        ]);
        let cfg = Config { label_lets: true, label_stmt: true, excluded, ..Default::default() };
        check_apply_and_remove(1, cfg, source, expect![[r#"
            fn foo() {#![cfg_attr(rustfmt, rustfmt::skip)]#![allow(unused_braces)]trait _IsTryOk{fn is_try_ok(&self)->bool;}impl<T,E>_IsTryOk for ::core::result::Result<T,E>{fn is_try_ok(&self)->bool{self.is_ok()}}impl<T>_IsTryOk for ::core::option::Option<T>{fn is_try_ok(&self)->bool{self.is_some()}}struct _S<T>(T);impl<T: ::core::fmt::Debug>_S<T>{fn _s(&self)->&T{&self.0}}impl<T>::core::fmt::Debug for _S<T>{fn fmt(&self,f:&mut::core::fmt::Formatter<'_>)->::core::fmt::Result{f.write_str("<opaque>")}}trait _Opaque {fn _s(&self)->&Self{self}}impl<T>_Opaque for _S<T>{}macro_rules!_track{(!)=>(());(!$t:tt)=>($t);(@$s:tt,$($e:expr)?)=>({let __val = _track!(!$($e)?);if !_IsTryOk::is_try_ok(&__val){let __s=_S(&__val);let __s=__s._s();println!("[track] foo tryret{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!())}; __val });(+$s:tt,$($e:expr)?)=>({let __val = _track!(!$($e)?);let __s=_S(&__val);let __s=__s._s();println!("[track] foo return{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); __val });(%$s:tt,$($e:expr)?)=>({let __val = _track!(!$($e)?);let __s=_S(&__val);let __s=__s._s();println!("[track] foo endret{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); __val });(%$s:tt,$e:stmt $(;)?)=>({{$e};let __val = ();let __s=_S(&__val);let __s=__s._s();println!("[track] foo endret{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); });(*$s:tt)=>({println!("[track] foo labels{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); });(*$s:tt,$n:ident)=>({let __val = &$n;let __s=_S(&__val);let __s=__s._s();println!("[track] foo labels{} at {}:{} let {}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!(),::core::stringify!($n)); });}println!("[track] foo enter      at {}:{}",::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!());
                let x = 2;
                {_track!(*"'1  ", x);}
                bar(x);
                {_track!{%"'0  ",}}
                {_track!(*"'2  ");}
            }
            fn bar() {
                fn baz() {
                    let x = 2;
                    f(x)
                }
                f(baz())
            }
        "#]]);
    }

    #[test]
    fn test_included_fn() {
        let source = r#"
        fn foo() {
            let x = 2;
            bar(x);
        }
        fn bar() {
            fn baz() {
                let x = 2;
                f(x)
            }
            f(baz())
        }
        "#;
        let included = PatternSet::from_iter([
            Pattern::new("foo").unwrap()
        ]);
        let cfg = Config { label_lets: true, label_stmt: true, included, ..Default::default() };
        check_apply_and_remove(1, cfg, source, expect![[r#"
            fn foo() {#![cfg_attr(rustfmt, rustfmt::skip)]#![allow(unused_braces)]trait _IsTryOk{fn is_try_ok(&self)->bool;}impl<T,E>_IsTryOk for ::core::result::Result<T,E>{fn is_try_ok(&self)->bool{self.is_ok()}}impl<T>_IsTryOk for ::core::option::Option<T>{fn is_try_ok(&self)->bool{self.is_some()}}struct _S<T>(T);impl<T: ::core::fmt::Debug>_S<T>{fn _s(&self)->&T{&self.0}}impl<T>::core::fmt::Debug for _S<T>{fn fmt(&self,f:&mut::core::fmt::Formatter<'_>)->::core::fmt::Result{f.write_str("<opaque>")}}trait _Opaque {fn _s(&self)->&Self{self}}impl<T>_Opaque for _S<T>{}macro_rules!_track{(!)=>(());(!$t:tt)=>($t);(@$s:tt,$($e:expr)?)=>({let __val = _track!(!$($e)?);if !_IsTryOk::is_try_ok(&__val){let __s=_S(&__val);let __s=__s._s();println!("[track] foo tryret{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!())}; __val });(+$s:tt,$($e:expr)?)=>({let __val = _track!(!$($e)?);let __s=_S(&__val);let __s=__s._s();println!("[track] foo return{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); __val });(%$s:tt,$($e:expr)?)=>({let __val = _track!(!$($e)?);let __s=_S(&__val);let __s=__s._s();println!("[track] foo endret{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); __val });(%$s:tt,$e:stmt $(;)?)=>({{$e};let __val = ();let __s=_S(&__val);let __s=__s._s();println!("[track] foo endret{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); });(*$s:tt)=>({println!("[track] foo labels{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); });(*$s:tt,$n:ident)=>({let __val = &$n;let __s=_S(&__val);let __s=__s._s();println!("[track] foo labels{} at {}:{} let {}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!(),::core::stringify!($n)); });}println!("[track] foo enter      at {}:{}",::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!());
                let x = 2;
                {_track!(*"'1  ", x);}
                bar(x);
                {_track!{%"'0  ",}}
                {_track!(*"'2  ");}
            }
            fn bar() {
                fn baz() {
                    let x = 2;
                    f(x)
                }
                f(baz())
            }
        "#]]);
    }

    #[test]
    fn test_lebel_stmts_with_inline() {
        let source = r#"
        fn foo() {
            let x = 2;
            bar(x);
            match () {
                () => x /* ... */,
                () => {
                    let _ = 3;
                    x
                }
                () => (),
                () => {},
                () => {
                    baz()?
                },
                () => {
                    let _ = 3;
                    return;
                }
                () => {
                    let _ = 3;
                    break;
                }
                () => {
                    let _ = 3;
                    unreachable!();
                }
            }
        }
        "#;
        let cfg = Config { label_stmt: true, inline: true, ..Default::default() };
        check_apply_and_remove(2, cfg, source, expect![[r#"
            fn foo() {#![cfg_attr(rustfmt, rustfmt::skip)]#![allow(unused_braces)]trait _IsTryOk{fn is_try_ok(&self)->bool;}impl<T,E>_IsTryOk for ::core::result::Result<T,E>{fn is_try_ok(&self)->bool{self.is_ok()}}impl<T>_IsTryOk for ::core::option::Option<T>{fn is_try_ok(&self)->bool{self.is_some()}}struct _S<T>(T);impl<T: ::core::fmt::Debug>_S<T>{fn _s(&self)->&T{&self.0}}impl<T>::core::fmt::Debug for _S<T>{fn fmt(&self,f:&mut::core::fmt::Formatter<'_>)->::core::fmt::Result{f.write_str("<opaque>")}}trait _Opaque {fn _s(&self)->&Self{self}}impl<T>_Opaque for _S<T>{}macro_rules!_track{(!)=>(());(!$t:tt)=>($t);(@$s:tt,$($e:expr)?)=>({let __val = _track!(!$($e)?);if !_IsTryOk::is_try_ok(&__val){let __s=_S(&__val);let __s=__s._s();println!("[track] foo tryret{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!())}; __val });(+$s:tt,$($e:expr)?)=>({let __val = _track!(!$($e)?);let __s=_S(&__val);let __s=__s._s();println!("[track] foo return{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); __val });(%$s:tt,$($e:expr)?)=>({let __val = _track!(!$($e)?);let __s=_S(&__val);let __s=__s._s();println!("[track] foo endret{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); __val });(%$s:tt,$e:stmt $(;)?)=>({{$e};let __val = ();let __s=_S(&__val);let __s=__s._s();println!("[track] foo endret{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); });(*$s:tt)=>({println!("[track] foo labels{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); });(*$s:tt,$n:ident)=>({let __val = &$n;let __s=_S(&__val);let __s=__s._s();println!("[track] foo labels{} at {}:{} let {}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!(),::core::stringify!($n)); });}println!("[track] foo enter      at {}:{}",::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!());
                let x = 2;{_track!(*"'8  ");}
                bar(x);{_track!(*"'9  ");}
                match () {
                    () => {_track!{%"'0  ",x}} /* ... */,
                    () => {{_track!(*"'10 ");}
                        let _ = 3;{_track!(*"'11 ");}
                        {_track!{%"'1  ",x}}
                    }
                    () => {_track!{%"'2  ",()}},
                    () => {_track!{%"'3  ",{{_track!(*"'12 ");}}}},
                    () => {{_track!(*"'13 ");}
                        {_track!{%"'4  ",{_track!(@"'14 ",baz())}?}}
                    },
                    () => {_track!{%"'5  ",{{_track!(*"'15 ");}
                        let _ = 3;{_track!(*"'16 ");}
                        return{_track!(+"'17 ",)};
                    }}}
                    () => {_track!{%"'6  ",{{_track!(*"'18 ");}
                        let _ = 3;{_track!(*"'19 ");}
                        break;
                    }}}
                    () => {_track!{%"'7  ",{{_track!(*"'20 ");}
                        let _ = 3;{_track!(*"'21 ");}
                        unreachable!();
                    }}}
                }
            }
        "#]]);
    }

    #[test]
    #[ignore]
    fn slow_test_remove_multi_apply() {
        let source = r#"
        fn foo() -> i32 {
            let x = 3;
            f();
            2
        }
        "#;
        let cfg = Config { label_stmt: true, inline: true, label_lets: true, ..Default::default() };
        let source = trim_indent(source);
        let mut s = source.clone();
        for _ in 0..3 {
            let node = parse_source(&s);
            let inserts = term_expr_inserts(&node, &s, cfg.clone());
            edits::apply_inserts(inserts, &mut s);
        }
        for pass in 0..5 {
            let node = parse_source(&s);
            let removes = remove_tracks(&node, &s);
            assert!(!removes.is_empty(), "redundant pass: {pass}");
            edits::apply_deletes(removes, &mut s);
        }
        assert_eq!(source, s);
    }
}
