// Resolves every identifier in the given files and reports the ones that resolve to nothing.
// Usage: cargo run --release --example resolve_corpus -- <files...>
use std::collections::HashMap;
use std::path::PathBuf;

use dafny_lsp::analysis;
use dafny_lsp::state::State;

fn main() {
    let files: Vec<PathBuf> = std::env::args().skip(1).map(PathBuf::from).collect();
    let mut total = 0;
    let mut unresolved = 0;
    let mut by_parent: HashMap<String, usize> = HashMap::new();
    let mut samples = Vec::new();
    let start = std::time::Instant::now();
    for path in &files {
        let st = State::default();
        st.set_roots(vec![path.parent().unwrap().to_path_buf()]);
        let Some(file) = st.file_by_path(path) else { continue };
        let mut stack = vec![file.root()];
        while let Some(node) = stack.pop() {
            let mut cursor = node.walk();
            stack.extend(node.children(&mut cursor));
            if node.kind() != "identifier" {
                continue;
            }
            let parent = node.parent().map(|p| p.kind()).unwrap_or("");
            if parent == "attribute" {
                continue;
            }
            total += 1;
            if analysis::resolve_ident(&st, &file, node).is_empty() {
                unresolved += 1;
                *by_parent.entry(parent.to_string()).or_default() += 1;
                if samples.len() < 40 {
                    let line = file.index.line_of(node.start_byte());
                    let start = file.index.line_start(line);
                    let end = file.index.line_end(&file.text, line);
                    samples.push(format!(
                        "{}:{}: `{}` in {}: {}",
                        path.file_name().unwrap().to_string_lossy(),
                        line + 1,
                        &file.text[node.byte_range()],
                        parent,
                        file.text[start..end].trim()
                    ));
                }
            }
        }
    }
    println!("{} files, {} identifiers, {} unresolved ({:.2}%), {:?}", files.len(), total, unresolved, 100.0 * unresolved as f64 / total.max(1) as f64, start.elapsed());
    let mut parents: Vec<_> = by_parent.into_iter().collect();
    parents.sort_by(|a, b| b.1.cmp(&a.1));
    println!("by parent kind: {parents:?}");
    for s in samples {
        println!("  {s}");
    }
}
