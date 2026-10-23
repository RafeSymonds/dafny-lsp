//! Hover and signature help.

use std::sync::Arc;

use tower_lsp::lsp_types::{
    Documentation, MarkupContent, MarkupKind, ParameterInformation, ParameterLabel, SignatureHelp,
    SignatureInformation,
};

use crate::analysis::{self, classify, LocalKind, SymRef, Target, Val};
use crate::state::{FileData, State};
use crate::symbols::Kind;

pub fn kind_word(kind: Kind) -> &'static str {
    match kind {
        Kind::Module => "module",
        Kind::Import => "import",
        Kind::Class => "class",
        Kind::Trait => "trait",
        Kind::Datatype => "datatype",
        Kind::Ctor => "constructor",
        Kind::Destructor => "field",
        Kind::Newtype => "newtype",
        Kind::TypeSynonym => "type",
        Kind::Iterator => "iterator",
        Kind::Method => "method",
        Kind::Lemma => "lemma",
        Kind::Constructor => "constructor",
        Kind::Function => "function",
        Kind::Predicate => "predicate",
        Kind::Field => "field",
        Kind::Const => "const",
    }
}

fn container_line(s: &SymRef, from: &FileData) -> Option<String> {
    match s.parent() {
        Some(p) => Some(format!("in {} `{}`", kind_word(p.sym().kind), p.sym().display_name())),
        None if s.file.uri != from.uri => {
            let name = s.file.path.as_deref().and_then(|p| p.file_name()).map(|n| n.to_string_lossy().into_owned())?;
            Some(format!("in `{name}`"))
        }
        None => None,
    }
}

fn shorten(s: &str, max: usize) -> String {
    let one_line = s.split_whitespace().collect::<Vec<_>>().join(" ");
    if one_line.chars().count() <= max {
        one_line
    } else {
        format!("{}...", one_line.chars().take(max).collect::<String>())
    }
}

pub fn hover_markdown(st: &State, t: &Target, from: &FileData) -> String {
    match t {
        Target::Sym(s) => {
            let sym = s.sym();
            let mut out = format!("```dafny\n{}\n```", sym.signature);
            if let Some(c) = container_line(s, from) {
                out.push_str(&format!("\n\n{c}"));
            }
            if let Some(doc) = &sym.doc {
                out.push_str("\n\n---\n\n");
                out.push_str(doc);
            }
            out
        }
        Target::Local { file, local } => {
            let ty = local.ty.clone().or_else(|| match classify(st, t) {
                Val::Typed(tv) => Some(tv.text),
                Val::Static(s) => Some(s.sym().name.clone()),
                _ => None,
            });
            let code = match (local.kind, ty) {
                (LocalKind::TypeParam, _) => format!("type {}", local.name),
                (LocalKind::Var, Some(ty)) => format!("var {}: {}", local.name, ty),
                (LocalKind::Var, None) => match &local.init {
                    Some(init) => format!("var {} := {}", local.name, shorten(&file.text[init.range.clone()], 80)),
                    None => format!("var {}", local.name),
                },
                (kind, Some(ty)) => format!("({}) {}: {}", kind.label(), local.name, ty),
                (kind, None) => format!("({}) {}", kind.label(), local.name),
            };
            format!("```dafny\n{code}\n```")
        }
    }
}

/// Finds the `(` of the call the cursor is in and the index of the argument under the cursor.
fn enclosing_call(src: &str, offset: usize) -> Option<(usize, usize)> {
    let b = src.as_bytes();
    let mut depth = 0i32;
    let mut commas = 0;
    let mut i = offset.min(b.len());
    let floor = offset.saturating_sub(4000);
    while i > floor {
        i -= 1;
        match b[i] {
            b')' | b']' | b'}' => depth += 1,
            b'(' if depth == 0 => return Some((i, commas)),
            b'[' | b'{' if depth == 0 => return None,
            b'(' | b'[' | b'{' => depth -= 1,
            b',' if depth == 0 => commas += 1,
            b';' if depth == 0 => return None,
            _ => {}
        }
    }
    None
}

fn signature_of(s: &SymRef) -> Option<SignatureInformation> {
    let sym = s.sym();
    if !sym.kind.is_callable() && sym.kind != Kind::Iterator {
        return None;
    }
    let params: Vec<String> = sym
        .params
        .iter()
        .map(|p| if p.name.is_empty() { p.ty.clone() } else { format!("{}: {}", p.name, p.ty) })
        .collect();
    let name = match sym.kind {
        Kind::Constructor => s.parent().map(|p| p.sym().name.clone()).unwrap_or_else(|| sym.display_name().to_string()),
        _ => sym.name.clone(),
    };
    let mut label = format!("{}({})", name, params.join(", "));
    match sym.kind {
        Kind::Function | Kind::Predicate => {
            if let Some(ty) = &sym.ty {
                label.push_str(&format!(": {ty}"));
            }
        }
        Kind::Method | Kind::Lemma if !sym.returns.is_empty() => {
            let outs: Vec<String> = sym.returns.iter().map(|p| format!("{}: {}", p.name, p.ty)).collect();
            label.push_str(&format!(" returns ({})", outs.join(", ")));
        }
        _ => {}
    }
    Some(SignatureInformation {
        label,
        documentation: sym.doc.clone().map(|d| {
            Documentation::MarkupContent(MarkupContent { kind: MarkupKind::Markdown, value: d })
        }),
        parameters: Some(
            params
                .into_iter()
                .map(|p| ParameterInformation { label: ParameterLabel::Simple(p), documentation: None })
                .collect(),
        ),
        active_parameter: None,
    })
}

pub fn signature_help(st: &State, file: &Arc<FileData>, offset: usize) -> Option<SignatureHelp> {
    let src = &file.text;
    let (open, active) = enclosing_call(src, offset)?;
    let segs = analysis::chain_before(src, open);
    if segs.is_empty() {
        return None;
    }
    let chain_start = {
        let mut i = open;
        let b = src.as_bytes();
        while i > 0 && (b[i - 1].is_ascii_alphanumeric() || matches!(b[i - 1], b'_' | b'.' | b'?' | b'\'')) {
            i -= 1;
        }
        i
    };
    let is_new = src[..chain_start].trim_end().ends_with("new");
    let mut callees: Vec<SymRef> = Vec::new();
    for t in analysis::resolve_chain(st, file, open, &segs) {
        let Target::Sym(s) = t else { continue };
        if s.sym().kind == Kind::Class && is_new {
            // `new C(...)` calls the anonymous constructor.
            callees.extend(s.children().into_iter().filter(|c| c.sym().kind == Kind::Constructor && c.sym().name == "_ctor"));
        } else {
            callees.push(s);
        }
    }
    let signatures: Vec<SignatureInformation> = callees.iter().filter_map(signature_of).collect();
    if signatures.is_empty() {
        return None;
    }
    Some(SignatureHelp { signatures, active_signature: Some(0), active_parameter: Some(active as u32) })
}

#[cfg(test)]
mod tests {
    use super::*;
    use tower_lsp::lsp_types::Url;

    #[test]
    fn signature_for_call_in_progress() {
        let st = State::default();
        let src = "function Add(a: int, b: int): int { a + b }\nmethod M() { var x := Add(1, ";
        let uri = Url::parse("file:///ws/s.dfy").unwrap();
        st.put_doc(FileData::new(uri.clone(), Some(1), src.to_string(), None, None));
        let f = st.doc(&uri).unwrap();
        let help = signature_help(&st, &f, src.len()).unwrap();
        assert_eq!(help.signatures[0].label, "Add(a: int, b: int): int");
        assert_eq!(help.active_parameter, Some(1));
    }

    #[test]
    fn finds_enclosing_call() {
        assert_eq!(enclosing_call("f(a, g(b, c), ", 14), Some((1, 2)));
        assert_eq!(enclosing_call("x := y;", 7), None);
    }
}
