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
    !is_trivia(node) && !matches!(node.kind.as_str(),
        | "ATTR"
        | "L_PAREN"
        | "R_PAREN"
        | "L_BRACK"
        | "R_BRACK"
        | "L_CURLY"
        | "R_CURLY")
}

pub fn is_jumping(node: &Node) -> bool {
    matches!(node.kind.as_str(),
        | "BREAK_EXPR"
        | "RETURN_EXPR"
        | "CONTINUE_EXPR")
}
