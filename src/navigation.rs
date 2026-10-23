//! Go to definition, references, rename, highlights and symbol lists.

use std::collections::HashMap;
use std::sync::Arc;

use tower_lsp::lsp_types::{
    DocumentHighlight, DocumentHighlightKind, DocumentSymbol, Location, Range,
    SymbolInformation, SymbolKind, TextEdit, Url, WorkspaceEdit,
};

use crate::analysis::{self, Target};
use crate::state::{FileData, State};
use crate::symbols::{Kind, Symbol};
use crate::syntax;
use crate::text::{is_valid_identifier, Encoding};

pub fn location(t: &Target, enc: Encoding) -> Location {
    let file = t.file();
    Location::new(file.uri.clone(), file.range(&t.name_range(), enc))
}

/// The file named by an include directive under the cursor.
fn include_target(st: &State, file: &FileData, offset: usize) -> Option<Location> {
    let inc = file.syms.includes.iter().find(|i| i.range.start <= offset && offset <= i.range.end)?;
    let target = st.file_by_path(&file.dir()?.join(&inc.path))?;
    Some(Location::new(target.uri.clone(), Range::default()))
}

pub fn definition(st: &State, file: &Arc<FileData>, offset: usize, enc: Encoding) -> Vec<Location> {
    if let Some(loc) = include_target(st, file, offset) {
        return vec![loc];
    }
    analysis::resolve_at(st, file, offset).iter().map(|t| location(t, enc)).collect()
}

pub fn references(st: &State, file: &Arc<FileData>, offset: usize, include_decl: bool, enc: Encoding) -> Vec<Location> {
    let Some(target) = analysis::resolve_at(st, file, offset).into_iter().next() else { return Vec::new() };
    analysis::references(st, &target, include_decl)
        .into_iter()
        .map(|(f, r)| Location::new(f.uri.clone(), f.range(&r, enc)))
        .collect()
}

pub fn highlights(st: &State, file: &Arc<FileData>, offset: usize, enc: Encoding) -> Vec<DocumentHighlight> {
    let Some(target) = analysis::resolve_at(st, file, offset).into_iter().next() else { return Vec::new() };
    let in_this_file = target.file().uri == file.uri;
    let mut out = Vec::new();
    let name = target.name();
    for ident in analysis::identifiers_named(file.root(), &file.text, &name) {
        let is_decl = in_this_file && ident.byte_range() == target.name_range();
        if is_decl || analysis::resolve_ident(st, file, ident).iter().any(|t| t.same(&target)) {
            out.push(DocumentHighlight {
                range: file.range(&ident.byte_range(), enc),
                kind: Some(if is_decl { DocumentHighlightKind::WRITE } else { DocumentHighlightKind::READ }),
            });
        }
    }
    out
}

/// Range of the identifier that can be renamed at the cursor.
pub fn prepare_rename(st: &State, file: &Arc<FileData>, offset: usize, enc: Encoding) -> Option<Range> {
    let ident = syntax::identifier_at(file.root(), offset)?;
    let target = analysis::resolve_ident(st, file, ident).into_iter().next()?;
    if target.name() != syntax::text(ident, &file.text) {
        return None;
    }
    Some(file.range(&ident.byte_range(), enc))
}

pub fn rename(st: &State, file: &Arc<FileData>, offset: usize, new_name: &str, enc: Encoding) -> Result<Option<WorkspaceEdit>, String> {
    if !is_valid_identifier(new_name) {
        return Err(format!("`{new_name}` is not a valid Dafny identifier"));
    }
    let Some(target) = analysis::resolve_at(st, file, offset).into_iter().next() else { return Ok(None) };
    let mut changes: HashMap<Url, Vec<TextEdit>> = HashMap::new();
    for (f, r) in analysis::references(st, &target, true) {
        changes.entry(f.uri.clone()).or_default().push(TextEdit::new(f.range(&r, enc), new_name.to_string()));
    }
    Ok(Some(WorkspaceEdit { changes: Some(changes), ..Default::default() }))
}

pub fn symbol_kind(kind: Kind) -> SymbolKind {
    match kind {
        Kind::Module | Kind::Import => SymbolKind::MODULE,
        Kind::Class | Kind::Iterator => SymbolKind::CLASS,
        Kind::Trait => SymbolKind::INTERFACE,
        Kind::Datatype => SymbolKind::ENUM,
        Kind::Ctor => SymbolKind::ENUM_MEMBER,
        Kind::Destructor | Kind::Field => SymbolKind::FIELD,
        Kind::Newtype | Kind::TypeSynonym => SymbolKind::STRUCT,
        Kind::Method | Kind::Lemma => SymbolKind::METHOD,
        Kind::Constructor => SymbolKind::CONSTRUCTOR,
        Kind::Function | Kind::Predicate => SymbolKind::FUNCTION,
        Kind::Const => SymbolKind::CONSTANT,
    }
}

#[allow(deprecated)]
fn document_symbol(file: &FileData, sym: &Symbol, enc: Encoding) -> DocumentSymbol {
    let children: Vec<DocumentSymbol> = sym
        .children
        .iter()
        .filter(|c| c.kind != Kind::Import)
        .map(|c| document_symbol(file, c, enc))
        .collect();
    DocumentSymbol {
        name: sym.display_name().to_string(),
        detail: Some(sym.signature.lines().next().unwrap_or("").to_string()),
        kind: symbol_kind(sym.kind),
        tags: None,
        deprecated: None,
        range: file.range(&sym.range, enc),
        selection_range: file.range(&sym.name_range, enc),
        children: (!children.is_empty()).then_some(children),
    }
}

pub fn document_symbols(file: &FileData, enc: Encoding) -> Vec<DocumentSymbol> {
    file.syms
        .symbols
        .iter()
        .filter(|s| s.kind != Kind::Import)
        .map(|s| document_symbol(file, s, enc))
        .collect()
}

/// Case-insensitive subsequence match; lower scores are better.
fn fuzzy_score(name: &str, query: &str) -> Option<usize> {
    if query.is_empty() {
        return Some(2);
    }
    let lname = name.to_lowercase();
    let lquery = query.to_lowercase();
    if lname == lquery {
        return Some(0);
    }
    if lname.starts_with(&lquery) {
        return Some(1);
    }
    let mut chars = lname.chars();
    lquery.chars().all(|q| chars.any(|c| c == q)).then_some(3)
}

#[allow(deprecated)]
pub fn workspace_symbols(st: &State, query: &str, enc: Encoding) -> Vec<SymbolInformation> {
    fn walk(file: &FileData, syms: &[Symbol], container: Option<&str>, query: &str, enc: Encoding, out: &mut Vec<(usize, SymbolInformation)>) {
        for s in syms {
            if s.kind == Kind::Import {
                continue;
            }
            if let Some(score) = fuzzy_score(&s.name, query) {
                out.push((
                    score,
                    SymbolInformation {
                        name: s.display_name().to_string(),
                        kind: symbol_kind(s.kind),
                        tags: None,
                        deprecated: None,
                        location: Location::new(file.uri.clone(), file.range(&s.name_range, enc)),
                        container_name: container.map(str::to_string),
                    },
                ));
            }
            walk(file, &s.children, Some(&s.name), query, enc, out);
        }
    }
    let mut found = Vec::new();
    for f in st.all_files() {
        walk(&f, &f.syms.symbols, None, query, enc, &mut found);
    }
    found.sort_by(|a, b| a.0.cmp(&b.0).then_with(|| a.1.name.cmp(&b.1.name)));
    found.into_iter().take(500).map(|(_, s)| s).collect()
}
