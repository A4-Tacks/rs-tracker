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
