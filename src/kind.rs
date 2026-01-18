use crate::Node;

pub fn is_item(node: &Node) -> bool {
    matches!(node.kind.as_str(),
        | "CONST"
        | "ENUM"
        | "EXTERN_BLOCK"
        | "EXTERN_CRATE"
        | "FN"
        | "IMPL"
        | "MACRO_CALL"
        | "MACRO_RULES"
        | "MACRO_DEF"
        | "MODULE"
        | "STATIC"
        | "STRUCT"
        | "TRAIT"
        | "TYPE_ALIAS"
        | "UNION"
        | "USE"
        | "ASM_EXPR")
}

pub fn is_item_or_let(node: &Node) -> bool {
    is_item(node) || node.kind == "LET_STMT"
}

pub fn is_trivia(node: &Node) -> bool {
    matches!(node.kind.as_str(),
        | "WHITESPACE"
        | "COMMENT")
}

pub fn is_content(node: &Node) -> bool {
    !is_trivia(node) && !is_delim(node) && node.kind != "ATTR"
}

pub fn is_jumping(node: &Node) -> bool {
    matches!(node.kind.as_str(),
        | "BREAK_EXPR"
        | "RETURN_EXPR"
        | "CONTINUE_EXPR")
}

pub fn is_delim(node: &Node) -> bool {
    matches!(node.kind.as_str(),
        | "L_PAREN"
        | "R_PAREN"
        | "L_BRACK"
        | "R_BRACK"
        | "L_CURLY"
        | "R_CURLY")
}

pub struct Kind<F: Fn(&Node) -> bool>(pub F);

pub trait NodePat {
    fn matches(&self, node: &Node) -> bool;
}

impl<T: NodePat + ?Sized> NodePat for &T {
    fn matches(&self, node: &Node) -> bool {
        (*self).matches(node)
    }
}

impl<F: Fn(&Node) -> bool> NodePat for Kind<F> {
    fn matches(&self, node: &Node) -> bool {
        (self.0)(node)
    }
}

impl NodePat for fn(&Node) -> bool {
    fn matches(&self, node: &Node) -> bool {
        self(node)
    }
}

impl<T: NodePat> NodePat for [T] {
    fn matches(&self, node: &Node) -> bool {
        self.iter().any(|pat| pat.matches(node))
    }
}

impl NodePat for str {
    fn matches(&self, node: &Node) -> bool {
        node.kind == self
    }
}

impl NodePat for Node {
    fn matches(&self, node: &Node) -> bool {
        self.range() == node.range()
            && self.kind == node.kind
    }
}
