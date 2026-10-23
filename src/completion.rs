use std::collections::HashSet;
use std::sync::Arc;

use tower_lsp::lsp_types::{
    CompletionItem, CompletionItemKind, CompletionItemLabelDetails, Documentation, InsertTextFormat,
    MarkupContent, MarkupKind,
};

use crate::analysis::{self, LocalKind, SymRef, Val};
use crate::state::{FileData, State};
use crate::symbols::{base_type_name, Kind};
use crate::syntax::{self, KEYWORDS};

const SNIPPETS: &[(&str, &str, &str)] = &[
    ("method", "method declaration", "method ${1:Name}(${2})${3: returns (${4})}\n  requires ${5:true}\n  ensures ${6:true}\n{\n  $0\n}"),
    ("lemma", "lemma declaration", "lemma ${1:Name}(${2})\n  requires ${3:true}\n  ensures ${4:true}\n{\n  $0\n}"),
    ("function", "function declaration", "function ${1:Name}(${2}): ${3:int}\n{\n  $0\n}"),
    ("predicate", "predicate declaration", "predicate ${1:Name}(${2})\n{\n  $0\n}"),
    ("ghost predicate", "ghost predicate declaration", "ghost predicate ${1:Name}(${2})\n{\n  $0\n}"),
    ("datatype", "datatype declaration", "datatype ${1:Name} = ${2:Ctor}(${3})"),
    ("class", "class declaration", "class ${1:Name} {\n  constructor(${2})\n  {\n    $0\n  }\n}"),
    ("module", "module declaration", "module ${1:Name} {\n  $0\n}"),
    ("while", "while loop with invariant", "while ${1:condition}\n  invariant ${2:true}\n  decreases ${3}\n{\n  $0\n}"),
    ("for", "for loop with invariant", "for ${1:i} := ${2:0} to ${3:n}\n  invariant ${4:true}\n{\n  $0\n}"),
    ("forall", "forall statement", "forall ${1:x} | ${2:true}\n  ensures ${3:true}\n{\n  $0\n}"),
    ("if", "if statement", "if ${1:condition} {\n  $0\n}"),
    ("ifelse", "if/else statement", "if ${1:condition} {\n  $2\n} else {\n  $0\n}"),
    ("match", "match statement", "match ${1:e}\n  case ${2:Ctor} => $0"),
    ("calc", "calc statement", "calc {\n  ${1:a};\n==\n  ${2:b};\n}"),
    ("assert by", "assert with proof", "assert ${1:P} by {\n  $0\n}"),
];

const ATTRIBUTES: &[&str] = &[
    "abstemious", "assumption", "autocontracts", "auto_generated", "axiom", "compile", "extern", "focus",
    "fuel", "induction", "isolate_assertions", "nativeType", "only", "opaque", "options", "print",
    "resource_limit", "split_here", "tailrecursion", "test", "timeLimit", "timeLimitMultiplier", "trigger",
    "vcs_split_on_every_assert", "verify", "warnShadowing",
];

pub fn item_kind(kind: Kind) -> CompletionItemKind {
    match kind {
        Kind::Module | Kind::Import => CompletionItemKind::MODULE,
        Kind::Class | Kind::Iterator => CompletionItemKind::CLASS,
        Kind::Trait => CompletionItemKind::INTERFACE,
        Kind::Datatype => CompletionItemKind::ENUM,
        Kind::Ctor => CompletionItemKind::ENUM_MEMBER,
        Kind::Destructor | Kind::Field => CompletionItemKind::FIELD,
        Kind::Newtype | Kind::TypeSynonym => CompletionItemKind::STRUCT,
        Kind::Method | Kind::Lemma => CompletionItemKind::METHOD,
        Kind::Constructor => CompletionItemKind::CONSTRUCTOR,
        Kind::Function | Kind::Predicate => CompletionItemKind::FUNCTION,
        Kind::Const => CompletionItemKind::CONSTANT,
    }
}

fn first_line(s: &str) -> String {
    s.lines().next().unwrap_or("").to_string()
}

fn symbol_item(s: &SymRef, rank: u8) -> CompletionItem {
    let sym = s.sym();
    CompletionItem {
        label: sym.display_name().to_string(),
        kind: Some(item_kind(sym.kind)),
        detail: Some(first_line(&sym.signature)),
        documentation: sym.doc.clone().map(|d| Documentation::MarkupContent(MarkupContent { kind: MarkupKind::Markdown, value: d })),
        sort_text: Some(format!("{rank}{}", sym.name)),
        ..Default::default()
    }
}

fn plain_item(label: &str, kind: CompletionItemKind, detail: Option<String>, rank: u8) -> CompletionItem {
    CompletionItem {
        label: label.to_string(),
        kind: Some(kind),
        detail,
        sort_text: Some(format!("{rank}{label}")),
        ..Default::default()
    }
}

/// True when the cursor is inside a comment or a string literal.
fn in_comment_or_string(file: &FileData, offset: usize) -> bool {
    if offset == 0 {
        return false;
    }
    let node = syntax::node_at(file.root(), offset - 1);
    syntax::ancestors(node).any(|n| match n.kind() {
        "line_comment" => n.start_byte() < offset && offset <= n.end_byte(),
        "block_comment" | "string_literal" | "char_literal" => n.start_byte() < offset && offset < n.end_byte(),
        _ => false,
    })
}

pub fn complete(st: &State, file: &Arc<FileData>, offset: usize, snippets: bool) -> Vec<CompletionItem> {
    if in_comment_or_string(file, offset) {
        return Vec::new();
    }
    let src = &file.text;
    let b = src.as_bytes();
    let mut word_start = offset;
    while word_start > 0 && (b[word_start - 1].is_ascii_alphanumeric() || matches!(b[word_start - 1], b'_' | b'\'' | b'?') || b[word_start - 1] >= 0x80) {
        word_start -= 1;
    }
    while !src.is_char_boundary(word_start) {
        word_start += 1;
    }
    let before = &src[..word_start];

    if before.ends_with("{:") || before.ends_with('@') {
        return ATTRIBUTES.iter().map(|a| plain_item(a, CompletionItemKind::PROPERTY, Some("attribute".into()), 0)).collect();
    }
    if before.ends_with('.') && !before.ends_with("..") {
        let segs = analysis::chain_before(src, word_start - 1);
        if segs.is_empty() {
            return Vec::new();
        }
        let val = analysis::eval_chain(st, file, word_start, &segs);
        return member_items(st, file, &val);
    }

    let line_start = file.index.line_start(file.index.line_of(offset));
    let line_prefix = src[line_start..word_start].trim_start();
    general_items(st, file, word_start, snippets, line_prefix)
}

fn builtin_members(ty: &str) -> &'static [&'static str] {
    let base = base_type_name(ty);
    match base {
        "map" | "imap" => &["Keys", "Values", "Items"],
        "real" => &["Floor"],
        "ORDINAL" => &["IsLimit", "IsSucc", "Offset", "IsNat"],
        "array" => &["Length"],
        b if b.starts_with("array") => &["Length0", "Length1", "Length2"],
        _ => &[],
    }
}

fn member_items(st: &State, file: &Arc<FileData>, val: &Val) -> Vec<CompletionItem> {
    let mut items = Vec::new();
    let mut seen = HashSet::new();
    let mut push = |item: CompletionItem, items: &mut Vec<CompletionItem>| {
        if seen.insert(item.label.clone()) {
            items.push(item);
        }
    };
    match val {
        Val::Unknown => {
            // Without a known receiver type, offer the members of every type in scope.
            let mut files = vec![file.clone()];
            files.extend(st.scope_files(file));
            for f in &files {
                for t in all_types(&analysis::top_level(f)) {
                    for m in analysis::members_of(st, &t, 3) {
                        push(symbol_item(&m, 1), &mut items);
                    }
                }
            }
            for name in ["Keys", "Values", "Items", "Length", "Floor"] {
                push(plain_item(name, CompletionItemKind::PROPERTY, Some("built-in member".into()), 2), &mut items);
            }
        }
        Val::Typed(tv) if tv.decl.is_none() => {
            for name in builtin_members(&tv.text) {
                push(plain_item(name, CompletionItemKind::PROPERTY, Some(tv.text.clone()), 0), &mut items);
            }
        }
        _ => {
            let candidates = analysis::member_candidates(st, val);
            // On a value, constructors are only reachable as discriminators (`d.Cons?`).
            let on_value = matches!(val, Val::Typed(..) | Val::Callable(_));
            for m in &candidates {
                let kind = m.sym().kind;
                if kind == Kind::Import {
                    continue;
                }
                if kind == Kind::Ctor && on_value {
                    let label = format!("{}?", m.sym().name);
                    push(plain_item(&label, CompletionItemKind::PROPERTY, Some(format!("is {}", m.sym().name)), 1), &mut items);
                } else {
                    push(symbol_item(m, 0), &mut items);
                }
            }
        }
    }
    items
}

fn all_types(syms: &[SymRef]) -> Vec<SymRef> {
    let mut out = Vec::new();
    for s in syms {
        let kind = s.sym().kind;
        if kind.is_type() {
            out.push(s.clone());
        } else if kind == Kind::Module {
            out.extend(all_types(&s.children()));
        }
    }
    out
}

fn general_items(st: &State, file: &Arc<FileData>, offset: usize, snippets: bool, line_prefix: &str) -> Vec<CompletionItem> {
    let mut items = Vec::new();
    let mut seen = HashSet::new();

    for l in analysis::locals_at(file, offset) {
        if seen.insert(l.name.clone()) {
            let kind = if l.kind == LocalKind::TypeParam { CompletionItemKind::TYPE_PARAMETER } else { CompletionItemKind::VARIABLE };
            let detail = match &l.ty {
                Some(ty) => format!("{}: {}", l.name, ty),
                None => l.kind.label().to_string(),
            };
            items.push(plain_item(&l.name, kind, Some(detail), 0));
        }
    }

    for (depth, level) in analysis::scope_levels(st, file, offset).into_iter().enumerate() {
        let rank = if depth == 0 { 1 } else { 2 };
        for s in level {
            let sym = s.sym();
            if sym.kind == Kind::Constructor && sym.name == "_ctor" {
                continue;
            }
            if seen.insert(sym.name.clone()) {
                items.push(symbol_item(&s, rank));
            }
        }
    }

    // Import paths can name any module in the workspace.
    if line_prefix.starts_with("import") {
        for f in st.all_files() {
            for m in all_modules(&analysis::top_level(&f)) {
                if seen.insert(m.sym().name.clone()) {
                    items.push(symbol_item(&m, 1));
                }
            }
        }
    }

    for kw in KEYWORDS {
        if seen.insert(kw.to_string()) {
            items.push(plain_item(kw, CompletionItemKind::KEYWORD, None, 3));
        }
    }

    if snippets {
        for (label, detail, body) in SNIPPETS {
            items.push(CompletionItem {
                label: label.to_string(),
                kind: Some(CompletionItemKind::SNIPPET),
                label_details: Some(CompletionItemLabelDetails { detail: None, description: Some("snippet".into()) }),
                detail: Some(detail.to_string()),
                insert_text: Some(body.to_string()),
                insert_text_format: Some(InsertTextFormat::SNIPPET),
                sort_text: Some(format!("4{label}")),
                ..Default::default()
            });
        }
    }
    items
}

fn all_modules(syms: &[SymRef]) -> Vec<SymRef> {
    let mut out = Vec::new();
    for s in syms {
        if s.sym().kind == Kind::Module {
            out.push(s.clone());
            out.extend(all_modules(&s.children()));
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use tower_lsp::lsp_types::Url;

    fn labels(src: &str, cursor_marker: &str) -> Vec<String> {
        let st = State::default();
        let offset = src.find(cursor_marker).unwrap();
        let src = src.replacen(cursor_marker, "", 1);
        let uri = Url::parse("file:///ws/c.dfy").unwrap();
        st.put_doc(FileData::new(uri.clone(), Some(1), src, None, None));
        let f = st.doc(&uri).unwrap();
        complete(&st, &f, offset, true).into_iter().map(|i| i.label).collect()
    }

    #[test]
    fn member_completion_uses_declared_types() {
        let src = "datatype P = P(x: int, y: int) | Q { function Norm(): int { 0 } }\nmethod M(p: P) { var a := p.<|> }";
        let got = labels(src, "<|>");
        for want in ["x", "y", "Norm", "P?", "Q?"] {
            assert!(got.contains(&want.to_string()), "missing {want} in {got:?}");
        }
        assert!(!got.contains(&"method".to_string()));
    }

    #[test]
    fn module_member_completion() {
        let src = "module A { function F(): int { 1 } datatype D = Mk }\nmethod M() { var a := A.<|> }";
        let got = labels(src, "<|>");
        assert!(got.contains(&"F".to_string()) && got.contains(&"D".to_string()) && got.contains(&"Mk".to_string()), "{got:?}");
    }

    #[test]
    fn general_completion_has_locals_and_keywords() {
        let src = "method M(count: int) {\n  var total := 0;\n  <|>\n}";
        let got = labels(src, "<|>");
        for want in ["count", "total", "M", "assert", "while"] {
            assert!(got.contains(&want.to_string()), "missing {want}");
        }
    }

    #[test]
    fn completion_while_the_line_is_incomplete() {
        let st = State::default();
        let uri = Url::parse("file:///ws/t.dfy").unwrap();
        let good = "module App {\n  datatype S = A(x: int)\n  method Use(s: S) {\n    var a := 1;\n  }\n}\n";
        st.put_doc(FileData::new(uri.clone(), Some(1), good.to_string(), None, None));
        let typed = good.replace("var a := 1;\n", "var a := 1;\n    var q := s.\n");
        let doc = st.put_doc(FileData::new(uri.clone(), Some(2), typed.clone(), None, None));
        assert!(doc.has_syntax_errors());
        // the outline survives the syntax error
        assert_eq!(doc.syms.symbols[0].children.iter().map(|s| s.name.as_str()).collect::<Vec<_>>(), vec!["S", "Use"]);
        let offset = typed.find("s.\n").unwrap() + 2;
        let got: Vec<String> = complete(&st, &doc, offset, false).into_iter().map(|i| i.label).collect();
        assert!(got.contains(&"x".to_string()) && got.contains(&"A?".to_string()), "{got:?}");
        let line_start = typed.find("    var q").unwrap();
        let got: Vec<String> = complete(&st, &doc, line_start + 4, false).into_iter().map(|i| i.label).collect();
        assert!(got.contains(&"a".to_string()) && got.contains(&"s".to_string()), "{got:?}");
    }

    #[test]
    fn no_completion_in_comments() {
        assert!(labels("// some <|> text\nmethod M() {}", "<|>").is_empty());
    }
}
