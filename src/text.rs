use crate::TextSize;
use crate::Node;
use std::{cell::Cell, fmt};

pub(crate) struct ShowMark(pub Cell<u32>);

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

pub(crate) fn is_complex_closure(node: &Node) -> bool {
    if node.kind != "CLOSURE_EXPR" {
        return false;
    }
    node.range().len() > TextSize::new(140)
}

pub fn indent(ws: &str) -> Option<&str> {
    if ws.trim().len() != 0 {
        debug_assert!(false, "{ws:?}");
        return None;
    }
    let i = ws.rfind('\n')?;
    Some(&ws[i..])
}
