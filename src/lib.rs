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

pub fn term_expr_inserts(
    node: &Node,
    src: &str,
    Config { debug, stderr, label_stmt, indent_name }: Config,
) -> Vec<(TextSize, SmolStr)> {
    let mut inserts = vec![];
    macro_rules! at {
        ($at:expr, $($t:tt)*) => {
            inserts.push(($at, format_smolstr!($($t)*)));
        };
    }
    let mut fn_names = vec!["unnamed_fn".into()];
    let mark = ShowMark(0.into());
    let label_mark = ShowMark(0.into());
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
            fn_names.push(src[name].into());
        } else if node.kind == "CLOSURE_EXPR" {
            if is_complex_closure(node) {
                let name = format_smolstr!("closure{closures}");
                at!(node.start(), "/*{name}*/");
                fn_names.push(name);
            } else {
                fn_names.push(SIMPLE_CLOSURE);
            }
        }
        let name = fn_names.last().unwrap();

        if name == &SIMPLE_CLOSURE {
            return None;
        }
        let iname = format_smolstr!(
            "[track] {}{name}",
            if indent_name { "  ".repeat(fn_names.len().saturating_sub(2)) } else { String::new() },
        );

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
                    \"{iname} tryret{{}} at {{}}:{{}}{debug}\",\
                    $s,{pather},::core::line!())}}; __val }});\
                (+$s:tt,$($e:expr)?)=>({{let __val = _track!(!$($e)?);{output}!(\
                    \"{iname} return{{}} at {{}}:{{}}{debug}\",\
                    $s,{pather},::core::line!()); __val }});\
                (%$s:tt,$($e:expr)?)=>({{let __val = _track!(!$($e)?);{output}!(\
                    \"{iname} endret{{}} at {{}}:{{}}{debug}\",\
                    $s,{pather},::core::line!()); __val }});\
                (%$s:tt,$e:stmt $(;)?)=>({{{{$e}};let __val = ();{output}!(\
                    \"{iname} endret{{}} at {{}}:{{}}{debug}\",\
                    $s,{pather},::core::line!()); }});\
                (*$s:tt)=>({{{output}!(\
                    \"{iname} labels{{}} at {{}}:{{}}\",\
                    $s,{pather},::core::line!()); }});\
            }}\
            {output}!(\"{iname} enter      at {{}}:{{}}\",{pather},::core::line!());\
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
                at!(tail.start(), r#"{{{try_trait}"#);

                each_value_expr_leafs(tail, &mut |tail| {
                    at!(tail.start(), r#"{{_track!{{%"{mark}","#);
                    at!(tail.end(), r#"}}}}"#);
                });

                at!(tail.end(), r#"}}"#);
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
            "STMT_LIST" if label_stmt => {
                let indent = node.find_children("WHITESPACE")
                    .and_then(|it| text::indent(&src[it]))
                    .unwrap_or("\n");
                let stmts = node.sub().iter().filter(|it| kind::is_content(*it));
                for stmt_like in stmts {
                    at!(stmt_like.start(), r#"{{_track!(*"{label_mark}");}}{indent}"#);
                }
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
            let tail_expr = tail.sub().iter().rfind(|it| kind::is_content(*it))?;
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

#[cfg(test)]
mod tests {
    use std::{io::Write, process::{Command, Stdio}};

    use expect_test::expect;

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

    #[test]
    fn test_replace() {
        let mut s = TEST_SRC.to_string();
        let node = parse_source(TEST_SRC);
        let inserts = term_expr_inserts(&node, &s, Config { debug: Debug::Inline, ..Default::default() });
        edits::apply_inserts(inserts, &mut s);
        expect![[r#"
            fn foo(n: u8) -> Option<u8> {trait _IsTryOk{fn is_try_ok(&self)->bool;}impl<T,E>_IsTryOk for ::core::result::Result<T,E>{fn is_try_ok(&self)->bool{self.is_ok()}}impl<T>_IsTryOk for ::core::option::Option<T>{fn is_try_ok(&self)->bool{self.is_some()}}macro_rules!_track{(!)=>(());(!$t:tt)=>($t);(@$s:tt,$($e:expr)?)=>({let __val = _track!(!$($e)?);if !_IsTryOk::is_try_ok(&__val){println!("[track] foo tryret{} at {}:{} = {__val:?}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!())}; __val });(+$s:tt,$($e:expr)?)=>({let __val = _track!(!$($e)?);println!("[track] foo return{} at {}:{} = {__val:?}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); __val });(%$s:tt,$($e:expr)?)=>({let __val = _track!(!$($e)?);println!("[track] foo endret{} at {}:{} = {__val:?}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); __val });(%$s:tt,$e:stmt $(;)?)=>({{$e};let __val = ();println!("[track] foo endret{} at {}:{} = {__val:?}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); });(*$s:tt)=>({println!("[track] foo labels{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); });}println!("[track] foo enter      at {}:{}",::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!());
                let m = {_track!(@"'1  ",n.checked_sub(16))}?;
                let _ = || 2;
                let _ = /*closure'0  */|| {trait _IsTryOk{fn is_try_ok(&self)->bool;}impl<T,E>_IsTryOk for ::core::result::Result<T,E>{fn is_try_ok(&self)->bool{self.is_ok()}}impl<T>_IsTryOk for ::core::option::Option<T>{fn is_try_ok(&self)->bool{self.is_some()}}macro_rules!_track{(!)=>(());(!$t:tt)=>($t);(@$s:tt,$($e:expr)?)=>({let __val = _track!(!$($e)?);if !_IsTryOk::is_try_ok(&__val){println!("[track] closure'0   tryret{} at {}:{} = {__val:?}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!())}; __val });(+$s:tt,$($e:expr)?)=>({let __val = _track!(!$($e)?);println!("[track] closure'0   return{} at {}:{} = {__val:?}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); __val });(%$s:tt,$($e:expr)?)=>({let __val = _track!(!$($e)?);println!("[track] closure'0   endret{} at {}:{} = {__val:?}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); __val });(%$s:tt,$e:stmt $(;)?)=>({{$e};let __val = ();println!("[track] closure'0   endret{} at {}:{} = {__val:?}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); });(*$s:tt)=>({println!("[track] closure'0   labels{} at {}:{}",$s,::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!()); });}println!("[track] closure'0   enter      at {}:{}",::core::file!().rsplit_once(['/','\\']).map_or(::core::file!(), |x|x.1),::core::line!());{
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
}
