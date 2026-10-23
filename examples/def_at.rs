// Prints the definition targets for a 1-based line and column.
use dafny_lsp::{analysis, state::State};
fn main() {
    let a: Vec<String> = std::env::args().collect();
    let path = std::path::PathBuf::from(&a[1]);
    let (line, col): (usize, usize) = (a[2].parse().unwrap(), a[3].parse().unwrap());
    let st = State::default();
    st.set_roots(vec![path.parent().unwrap().to_path_buf()]);
    let f = st.file_by_path(&path).unwrap();
    let off = f.index.line_start(line - 1) + col - 1;
    let ident = dafny_lsp::syntax::identifier_at(f.root(), off);
    println!("ident: {:?} parent: {:?} has_error: {}", ident.map(|i| &f.text[i.byte_range()]), ident.and_then(|i| i.parent()).map(|p| p.kind()), f.root().has_error());
    for t in analysis::resolve_at(&st, &f, off) {
        println!("-> {}:{} {}", t.file().uri.path(), t.file().index.line_of(t.name_range().start) + 1, t.name());
    }
}
