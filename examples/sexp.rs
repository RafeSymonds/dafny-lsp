fn main() {
    let src = std::fs::read_to_string(std::env::args().nth(1).unwrap()).unwrap();
    let mut p = tree_sitter::Parser::new();
    p.set_language(&tree_sitter_dafny::LANGUAGE.into()).unwrap();
    let t = p.parse(&src, None).unwrap();
    fn show(n: tree_sitter::Node, src: &str, depth: usize) {
        let field = "";
        let txt = if n.child_count() == 0 { format!(" {:?}", &src[n.byte_range()]) } else { String::new() };
        println!("{}{}{}{} [{}..{}]", "  ".repeat(depth), field, n.kind(), txt, n.start_position().row, n.start_position().column);
        let mut c = n.walk();
        for ch in n.children(&mut c) { show(ch, src, depth + 1); }
    }
    show(t.root_node(), &src, 0);
}
