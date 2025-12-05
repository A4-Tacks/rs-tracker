use super::*;

pub fn remove_tracks(node: &Node, src: &str) -> Vec<TextRange> {
    let mut deletes = vec![];
    node.visit(&mut |node, action| Some(if action.is_enter() {
        let handler = &mut Handler { src, node, deletes: &mut deletes };
        handle_expr_macro_call_block(handler);
        handle_pre_decl_trait(handler);
        handle_pre_decl_macro_rules(handler);
        handle_pre_decl_enter(handler);
    }));
    deletes
}

struct Handler<'a> {
    src: &'a str,
    node: &'a Node,
    deletes: &'a mut Vec<TextRange>,
}

fn handle_expr_macro_call_block(Handler { src, node, deletes }: &mut Handler) -> Option<()> {
    if node.kind != "STMT_LIST" {
        return None;
    }
    if node.sub.len() != 3 {
        return None;
    }
    let call = node
        .find_children("MACRO_EXPR")?
        .find_children("MACRO_CALL")?;
    let path = call.find_children("PATH")?;
    if &src[path] != "_track" {
        return None;
    }
    let tt = call.find_children("TOKEN_TREE")?;
    let r_delim = tt.find_children("R_CURLY").or_else(|| tt.find_children("R_PAREN"))?;
    let comma = tt.find_children("COMMA")?;

    deletes.push(TextRange::new(node.start(), comma.end()));
    deletes.push(TextRange::new(r_delim.start(), node.end()));

    None
}

fn handle_pre_decl_trait(Handler { src, node, deletes }: &mut Handler) -> Option<()> {
    if node.kind != "STMT_LIST" {
        return None;
    }
    let trait_ = node.find_children("TRAIT")?;
    if &src[trait_.find_children("NAME")?] != "_IsTryOk" {
        return None;
    }
    deletes.push(trait_.range);
    for next in node.sub().iter()
        .skip_while(|it| it.end() != trait_.end())
        .skip(1)
    {
        if next.kind != "IMPL" {
            return None;
        }
        if &src[next.find_children("PATH_TYPE")?] != "_IsTryOk" {
            return None;
        }
        deletes.push(next.range);
    }
    None
}

fn handle_pre_decl_macro_rules(Handler { src, node, deletes }: &mut Handler) -> Option<()> {
    if node.kind != "STMT_LIST" {
        return None;
    }
    let makro = node.find_children("MACRO_RULES")?;
    if &src[makro.find_children("NAME")?] != "_track" {
        return None;
    }
    deletes.push(makro.range);
    None
}

fn handle_pre_decl_enter(Handler { src, node, deletes }: &mut Handler) -> Option<()> {
    if node.kind != "STMT_LIST" {
        return None;
    }
    let makro = node.find_children("MACRO_RULES")?;
    if &src[makro.find_children("NAME")?] != "_track" {
        return None;
    }
    let enterer = node.next_of(makro)?;
    if enterer.kind != "EXPR_STMT" {
        return None;
    }
    let call = enterer.find_children("MACRO_EXPR")?
        .find_children("MACRO_CALL")?;
    if !matches!(&src[call.find_children("PATH")?], "println" | "eprintln") {
        return None;
    }
    deletes.push(enterer.range);
    None
}
