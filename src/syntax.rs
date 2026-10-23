use std::cell::RefCell;
use tree_sitter::{Node, Parser, Tree};

thread_local! {
    static PARSER: RefCell<Parser> = RefCell::new({
        let mut parser = Parser::new();
        parser
            .set_language(&tree_sitter_dafny::LANGUAGE.into())
            .expect("tree-sitter-dafny is compatible with the tree-sitter runtime");
        parser
    });
}

pub fn parse(text: &str, old: Option<&Tree>) -> Tree {
    PARSER.with(|p| p.borrow_mut().parse(text, old).expect("parser has a language set"))
}

pub fn text<'a>(node: Node, src: &'a str) -> &'a str {
    &src[node.byte_range()]
}

pub fn children(node: Node) -> Vec<Node> {
    let mut cursor = node.walk();
    node.children(&mut cursor).collect()
}

pub fn named_children(node: Node) -> Vec<Node> {
    let mut cursor = node.walk();
    node.named_children(&mut cursor).collect()
}

pub fn children_by_field<'t>(node: Node<'t>, field: &str) -> Vec<Node<'t>> {
    let mut cursor = node.walk();
    node.children_by_field_name(field, &mut cursor).collect()
}

pub fn is_comment(kind: &str) -> bool {
    kind == "line_comment" || kind == "block_comment"
}

/// The identifier node under the cursor, also accepting a cursor placed right after it.
/// Uses one-byte ranges: a zero-width range at the start of an identifier can
/// land in a hidden token that ends there, such as the `<` of `seq<T>`.
pub fn identifier_at(root: Node, offset: usize) -> Option<Node> {
    for (start, end) in [(offset, offset + 1), (offset.saturating_sub(1), offset)] {
        if let Some(node) = root.descendant_for_byte_range(start, end) {
            if node.kind() == "identifier" && node.start_byte() <= offset && offset <= node.end_byte() {
                return Some(node);
            }
        }
    }
    None
}

/// Smallest node covering the offset, used as the starting point for scope walks.
pub fn node_at(root: Node, offset: usize) -> Node {
    root.descendant_for_byte_range(offset, offset).unwrap_or(root)
}

pub fn ancestors(node: Node) -> impl Iterator<Item = Node> {
    std::iter::successors(Some(node), |n| n.parent())
}

pub fn is_type_node(kind: &str) -> bool {
    matches!(
        kind,
        "named_type"
            | "int_type"
            | "nat_type"
            | "real_type"
            | "bool_type"
            | "char_type"
            | "string_type"
            | "object_type"
            | "bitvector_type"
            | "float_type"
            | "ordinal_type"
            | "set_type"
            | "iset_type"
            | "multiset_type"
            | "seq_type"
            | "map_type"
            | "imap_type"
            | "array_type"
            | "arrow_type"
            | "tuple_type"
    )
}

/// The type written after the first ':' among the node's direct children.
pub fn type_after_colon(node: Node, src: &str) -> Option<String> {
    let mut seen_colon = false;
    for child in children(node) {
        if seen_colon && is_type_node(child.kind()) {
            return Some(text(child, src).to_string());
        }
        if child.kind() == ":" {
            seen_colon = true;
        } else if child.kind() == ":=" {
            break;
        }
    }
    None
}

/// Collapses a declaration header into a readable form: first line as written,
/// following lines dedented and indented by two spaces.
pub fn tidy_signature(raw: &str) -> String {
    let lines: Vec<&str> = raw.lines().map(|l| l.trim_end()).filter(|l| !l.trim().is_empty()).collect();
    if lines.is_empty() {
        return String::new();
    }
    let indent = lines[1..]
        .iter()
        .map(|l| l.len() - l.trim_start().len())
        .min()
        .unwrap_or(0);
    let mut out = lines[0].trim().to_string();
    for line in &lines[1..] {
        out.push_str("\n  ");
        out.push_str(&line[indent.min(line.len() - line.trim_start().len())..]);
    }
    out
}

pub const KEYWORDS: &[&str] = &[
    "abstract", "allocated", "as", "assert", "assume", "bool", "break", "by", "calc", "case", "char",
    "class", "codatatype", "const", "constructor", "continue", "datatype", "decreases", "downto",
    "else", "ensures", "exists", "expect", "export", "extends", "false", "for", "forall", "fresh",
    "function", "ghost", "greatest", "hide", "if", "imap", "import", "in", "include", "int",
    "invariant", "is", "iset", "iterator", "label", "least", "lemma", "map", "match", "method",
    "modifies", "modify", "module", "multiset", "nameonly", "nat", "new", "newtype", "null",
    "object", "old", "opaque", "opened", "ORDINAL", "predicate", "print", "provides", "reads",
    "real", "refines", "replaceable", "requires", "return", "returns", "reveal", "reveals", "seq",
    "set", "static", "string", "then", "this", "to", "trait", "true", "twostate", "type",
    "unchanged", "var", "while", "witness", "yield", "yields",
];

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn identifier_after_hidden_tokens() {
        let src = "method M<T>(s: seq<T>, n: nat) requires |s| > 0 && 0<n {}";
        let tree = parse(src, None);
        for needle in ["T>, n", "s| >", "n {}"] {
            let off = src.find(needle).unwrap();
            let id = identifier_at(tree.root_node(), off).map(|n| text(n, src));
            assert_eq!(id, Some(&needle[..needle.find(|c: char| !c.is_alphanumeric()).unwrap()]), "{needle}");
        }
    }

    #[test]
    fn tidy_dedents_spec_lines() {
        let raw = "method Abs(x: int) returns (y: int)\n    requires true\n    ensures y >= 0\n  ";
        assert_eq!(
            tidy_signature(raw),
            "method Abs(x: int) returns (y: int)\n  requires true\n  ensures y >= 0"
        );
    }
}
