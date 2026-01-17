use crate::TextSize;
use crate::Node;
use std::{cell::Cell, fmt};

pub(crate) struct ShowMark(pub Cell<u32>);

impl fmt::Display for ShowMark {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "'{:<3}", self.0.get())?;
        self.0.update(|n| n+1);
        Ok(())
    }
}

pub(crate) fn is_complex_closure(node: &Node) -> bool {
    if node.kind != "CLOSURE_EXPR" {
        return false;
    }
    node.range().len() > TextSize::new(140)
}

#[track_caller]
pub fn indent(ws: &str) -> Option<&str> {
    if ws.trim().len() != 0 {
        debug_assert!(false, "{ws:?}");
        return None;
    }
    let i = ws.rfind('\n')?;
    Some(&ws[i..])
}

pub fn indent_of<'a, I>(src: &str, ancestors: I) -> Option<&str>
where I: IntoIterator<Item = &'a Node>,
      I::IntoIter: DoubleEndedIterator,
{
    ancestors.into_iter().rev()
        .flat_map(|it| it.sub())
        .filter_map(|it| (it.kind == "WHITESPACE").then_some(&src[it]))
        .find_map(indent)
}
