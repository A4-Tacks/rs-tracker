use std::fmt;

use itertools::Itertools;
use smol_strc::SmolStr;
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
    pub kind: SmolStr,
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

    pub fn range(&self) -> TextRange {
        self.range
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
pub fn make(src: &str) -> Node {
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
