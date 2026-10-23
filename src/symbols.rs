use std::ops::Range;
use tree_sitter::Node;

use crate::syntax::{children, children_by_field, is_comment, named_children, text, tidy_signature, type_after_colon};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Kind {
    Module,
    Import,
    Class,
    Trait,
    Datatype,
    Ctor,
    Destructor,
    Newtype,
    TypeSynonym,
    Iterator,
    Method,
    Lemma,
    Constructor,
    Function,
    Predicate,
    Field,
    Const,
}

impl Kind {
    pub fn is_type(self) -> bool {
        matches!(
            self,
            Kind::Class | Kind::Trait | Kind::Datatype | Kind::Newtype | Kind::TypeSynonym | Kind::Iterator
        )
    }

    pub fn is_callable(self) -> bool {
        matches!(
            self,
            Kind::Method | Kind::Lemma | Kind::Constructor | Kind::Function | Kind::Predicate | Kind::Ctor
        )
    }
}

#[derive(Clone, Debug, Default, PartialEq)]
pub struct Param {
    pub name: String,
    pub ty: String,
}

#[derive(Clone, Debug)]
pub struct Symbol {
    pub name: String,
    pub kind: Kind,
    pub name_range: Range<usize>,
    pub range: Range<usize>,
    /// Header as written in the source, without the body.
    pub signature: String,
    pub doc: Option<String>,
    /// Field/const/destructor type, function result type, or the base type of a newtype/synonym.
    pub ty: Option<String>,
    pub params: Vec<Param>,
    pub returns: Vec<Param>,
    /// Module path of an import, or the module a module refines.
    pub target: Option<String>,
    pub opened: bool,
    pub extends: Vec<String>,
    /// Names of the declaration's type parameters, `T` in `function F<T>`.
    pub type_params: Vec<String>,
    pub is_static: bool,
    /// True for declarations that `dafny verify` reports progress for.
    pub verifiable: bool,
    /// Fully qualified name in the form Dafny prints it, e.g. `M.C.Foo`.
    pub qname: String,
    pub children: Vec<Symbol>,
}

impl Symbol {
    fn new(name: String, kind: Kind, name_range: Range<usize>, range: Range<usize>) -> Self {
        Symbol {
            name,
            kind,
            name_range,
            range,
            signature: String::new(),
            doc: None,
            ty: None,
            params: Vec::new(),
            returns: Vec::new(),
            target: None,
            opened: false,
            extends: Vec::new(),
            type_params: Vec::new(),
            is_static: false,
            verifiable: false,
            qname: String::new(),
            children: Vec::new(),
        }
    }

    /// Name used in source: the anonymous constructor is stored as `_ctor` like Dafny does.
    pub fn display_name(&self) -> &str {
        if self.kind == Kind::Constructor && self.name == "_ctor" {
            "constructor"
        } else {
            &self.name
        }
    }
}

#[derive(Clone, Debug)]
pub struct Include {
    pub path: String,
    pub range: Range<usize>,
}

#[derive(Clone, Debug, Default)]
pub struct FileSymbols {
    pub includes: Vec<Include>,
    pub symbols: Vec<Symbol>,
}

pub fn extract(root: Node, src: &str) -> FileSymbols {
    let mut out = FileSymbols::default();
    for child in children(root) {
        if child.kind() == "include_directive" {
            if let Some(lit) = named_children(child).into_iter().find(|n| n.kind() == "string_literal") {
                let raw = text(lit, src);
                let path = raw.trim_start_matches('@').trim_matches('"').to_string();
                out.includes.push(Include { path, range: child.byte_range() });
            }
        }
    }
    collect_items(root, src, "", &mut out.symbols);
    out
}

fn is_decl(kind: &str) -> bool {
    matches!(
        kind,
        "module_definition"
            | "module_import"
            | "class_decl"
            | "trait_decl"
            | "datatype_decl"
            | "datatype_ctor"
            | "newtype_decl"
            | "synonym_type_decl"
            | "iterator_decl"
            | "method_decl"
            | "function_decl"
            | "field_decl"
            | "constant_field_decl"
            | "constructor_decl"
    )
}

/// Collects declarations among the direct children of `parent`. Attributes and
/// modifiers are siblings that precede the declaration they belong to.
fn collect_items(parent: Node, src: &str, prefix: &str, out: &mut Vec<Symbol>) {
    let mut lead: Option<Node> = None;
    let mut modifiers: Vec<String> = Vec::new();
    let kids = children(parent);
    let mut skip_next = false;
    for (i, &child) in kids.iter().enumerate() {
        if std::mem::take(&mut skip_next) {
            continue;
        }
        let kind = child.kind();
        match kind {
            // Error recovery can leave a module as `module M` followed by an
            // ERROR node holding its body.
            "module_definition" if !children(child).iter().any(|c| c.kind() == "module_body") => {
                let first = lead.take().unwrap_or(child);
                let mods = std::mem::take(&mut modifiers);
                let body = kids
                    .get(i + 1)
                    .copied()
                    .filter(|n| n.kind() == "ERROR" && n.child(0).map(|c| c.kind()) == Some("{"));
                skip_next = body.is_some();
                let before = out.len();
                decl_symbols(child, src, prefix, &mods, first.start_byte(), out);
                if let (Some(body), Some(module)) = (body, out.get_mut(before)) {
                    module.range.end = body.end_byte();
                    let qname = module.qname.clone();
                    collect_items(body, src, &qname, &mut module.children);
                }
            }
            "ERROR" => {
                lead = None;
                modifiers.clear();
                collect_items(child, src, prefix, out);
            }
            "attribute" | "decl_modifier" => {
                lead.get_or_insert(child);
                if kind == "decl_modifier" {
                    modifiers.push(text(child, src).to_string());
                }
            }
            "class_member" => {
                let before = out.len();
                collect_items(child, src, prefix, out);
                // Doc comments sit before the class_member node, not inside it.
                if let Some(doc) = doc_comment(child, src) {
                    for sym in &mut out[before..] {
                        sym.doc.get_or_insert_with(|| doc.clone());
                    }
                }
            }
            _ if is_decl(kind) => {
                let first = lead.take().unwrap_or(child);
                let mods = std::mem::take(&mut modifiers);
                let before = out.len();
                decl_symbols(child, src, prefix, &mods, first.start_byte(), out);
                if let Some(doc) = doc_comment(first, src) {
                    for sym in &mut out[before..] {
                        sym.doc.get_or_insert_with(|| doc.clone());
                    }
                }
            }
            _ if is_comment(kind) => {}
            _ => {
                lead = None;
                modifiers.clear();
            }
        }
    }
}

fn qualify(prefix: &str, name: &str) -> String {
    if prefix.is_empty() {
        name.to_string()
    } else {
        format!("{prefix}.{name}")
    }
}

/// Source text from `start` up to the first child whose kind is in `stops`.
fn header(node: Node, src: &str, start: usize, stops: &[&str]) -> String {
    let end = children(node)
        .into_iter()
        .find(|c| stops.contains(&c.kind()))
        .map(|c| c.start_byte())
        .unwrap_or(node.end_byte());
    let sig = tidy_signature(&src[start..end]);
    truncate_lines(&sig, 25)
}

fn truncate_lines(s: &str, max: usize) -> String {
    let lines: Vec<&str> = s.lines().collect();
    if lines.len() <= max {
        s.to_string()
    } else {
        format!("{}\n  ...", lines[..max].join("\n"))
    }
}

fn with_modifiers(mods: &[String], sig: String) -> String {
    if mods.is_empty() {
        sig
    } else {
        format!("{} {}", mods.join(" "), sig)
    }
}

fn formals_params(formals: Node, src: &str) -> Vec<Param> {
    named_children(formals)
        .into_iter()
        .filter(|n| n.kind() == "formal")
        .filter_map(|f| {
            let name = f.child_by_field_name("name")?;
            Some(Param {
                name: text(name, src).to_string(),
                ty: type_after_colon(f, src).unwrap_or_default(),
            })
        })
        .collect()
}

/// Splits a declaration's formals into parameters and the formals after `keyword` (returns/yields).
fn params_and_outs(node: Node, src: &str, keyword: &str) -> (Vec<Param>, Vec<Param>) {
    let mut params = Vec::new();
    let mut outs = Vec::new();
    let mut after_keyword = false;
    for child in children(node) {
        if child.kind() == keyword {
            after_keyword = true;
        } else if child.kind() == "formals" {
            if after_keyword {
                outs = formals_params(child, src);
            } else if params.is_empty() {
                params = formals_params(child, src);
            }
        }
    }
    (params, outs)
}

fn type_names(node: Node, src: &str) -> Vec<String> {
    named_children(node)
        .into_iter()
        .filter(|n| crate::syntax::is_type_node(n.kind()))
        .map(|n| base_type_name(text(n, src)).to_string())
        .collect()
}

/// `M.T<int>?` becomes `M.T`.
pub fn base_type_name(ty: &str) -> &str {
    let ty = ty.trim();
    let end = ty.find(['<', '?', ' ']).unwrap_or(ty.len());
    &ty[..end]
}

fn decl_symbols(node: Node, src: &str, prefix: &str, mods: &[String], start: usize, out: &mut Vec<Symbol>) {
    let range = start..node.end_byte();
    let is_static = mods.iter().any(|m| m == "static");
    let kind = node.kind();
    let name_node = node.child_by_field_name("name");

    let mut sym = match kind {
        "module_definition" => {
            let Some(qn) = name_node else { return };
            let Some(last) = named_children(qn).into_iter().filter(|n| n.kind() == "identifier").last() else {
                return;
            };
            let full = text(qn, src).to_string();
            let mut sym = Symbol::new(text(last, src).to_string(), Kind::Module, last.byte_range(), range);
            sym.qname = qualify(prefix, &full);
            sym.signature = with_modifiers(mods, header(node, src, node.start_byte(), &["module_body"]));
            sym.target = children(node)
                .into_iter()
                .find(|c| c.kind() == "refines_clause")
                .and_then(|c| named_children(c).into_iter().next())
                .map(|q| text(q, src).to_string());
            if let Some(body) = children(node).into_iter().find(|c| c.kind() == "module_body") {
                collect_items(body, src, &sym.qname, &mut sym.children);
            }
            sym
        }
        "module_import" => {
            let Some(path) = named_children(node).into_iter().find(|n| n.kind() == "qualified_name") else {
                return;
            };
            let name = match name_node {
                Some(n) => n,
                None => match named_children(path).into_iter().filter(|n| n.kind() == "identifier").last() {
                    Some(n) => n,
                    None => return,
                },
            };
            let mut sym = Symbol::new(text(name, src).to_string(), Kind::Import, name.byte_range(), range);
            sym.target = Some(text(path, src).to_string());
            sym.opened = children(node).iter().any(|c| c.kind() == "opened");
            sym.signature = tidy_signature(text(node, src));
            sym
        }
        "class_decl" | "trait_decl" => {
            let Some(name) = name_node else { return };
            let kind = if kind == "class_decl" { Kind::Class } else { Kind::Trait };
            let mut sym = Symbol::new(text(name, src).to_string(), kind, name.byte_range(), range);
            sym.qname = qualify(prefix, &sym.name);
            sym.signature = with_modifiers(mods, header(node, src, node.start_byte(), &["{"]));
            if let Some(ext) = children(node).into_iter().find(|c| c.kind() == "extends_clause") {
                sym.extends = type_names(ext, src);
            }
            collect_items(node, src, &sym.qname, &mut sym.children);
            sym
        }
        "datatype_decl" => {
            let Some(name) = name_node else { return };
            let mut sym = Symbol::new(text(name, src).to_string(), Kind::Datatype, name.byte_range(), range);
            sym.qname = qualify(prefix, &sym.name);
            sym.signature = with_modifiers(mods, header(node, src, node.start_byte(), &["{"]));
            if let Some(ext) = children(node).into_iter().find(|c| c.kind() == "extends_clause") {
                sym.extends = type_names(ext, src);
            }
            collect_items(node, src, &sym.qname, &mut sym.children);
            for child in &mut sym.children {
                if child.kind == Kind::Ctor {
                    child.ty = Some(sym.name.clone());
                }
            }
            sym
        }
        "datatype_ctor" => {
            let Some(name) = name_node else { return };
            let mut sym = Symbol::new(text(name, src).to_string(), Kind::Ctor, name.byte_range(), range);
            sym.signature = tidy_signature(text(node, src));
            for formal in named_children(node).into_iter().filter(|n| n.kind() == "datatype_formal") {
                let ty = named_children(formal)
                    .into_iter()
                    .find(|n| crate::syntax::is_type_node(n.kind()))
                    .map(|n| text(n, src).to_string())
                    .unwrap_or_default();
                match formal.child_by_field_name("name") {
                    Some(fname) => {
                        let fname_text = text(fname, src).to_string();
                        let mut d = Symbol::new(fname_text.clone(), Kind::Destructor, fname.byte_range(), formal.byte_range());
                        d.signature = format!("{fname_text}: {ty}");
                        d.ty = Some(ty.clone());
                        sym.children.push(d);
                        sym.params.push(Param { name: fname_text, ty });
                    }
                    None => sym.params.push(Param { name: String::new(), ty }),
                }
            }
            sym
        }
        "newtype_decl" | "synonym_type_decl" => {
            let Some(name) = name_node else { return };
            let k = if kind == "newtype_decl" { Kind::Newtype } else { Kind::TypeSynonym };
            let mut sym = Symbol::new(text(name, src).to_string(), k, name.byte_range(), range);
            sym.qname = qualify(prefix, &sym.name);
            sym.signature = with_modifiers(mods, header(node, src, node.start_byte(), &["{"]));
            // `type T = x: int | P` has a bound variable; `type T = int` is a plain synonym.
            let bound = named_children(node)
                .into_iter()
                .any(|n| n.kind() == "identifier" && Some(n) != name_node);
            sym.ty = named_children(node)
                .into_iter()
                .find(|n| crate::syntax::is_type_node(n.kind()))
                .map(|n| text(n, src).to_string());
            sym.verifiable = k == Kind::Newtype || bound;
            collect_items(node, src, &sym.qname, &mut sym.children);
            sym
        }
        "iterator_decl" => {
            let Some(name) = name_node else { return };
            let mut sym = Symbol::new(text(name, src).to_string(), Kind::Iterator, name.byte_range(), range);
            sym.qname = qualify(prefix, &sym.name);
            sym.signature = with_modifiers(mods, header(node, src, node.start_byte(), &["block_statement"]));
            (sym.params, sym.returns) = params_and_outs(node, src, "yields");
            sym.verifiable = true;
            sym
        }
        "method_decl" => {
            let Some(name) = name_node else { return };
            let words: Vec<&str> = children(node).iter().take(2).map(|c| c.kind()).collect();
            let lemma = words.iter().any(|w| matches!(*w, "lemma" | "colemma"))
                || matches!(words.first(), Some(&"greatest") | Some(&"least") | Some(&"inductive"));
            let k = if lemma { Kind::Lemma } else { Kind::Method };
            let mut sym = Symbol::new(text(name, src).to_string(), k, name.byte_range(), range);
            sym.qname = qualify(prefix, &sym.name);
            sym.signature = with_modifiers(mods, header(node, src, node.start_byte(), &["block_statement"]));
            (sym.params, sym.returns) = params_and_outs(node, src, "returns");
            sym.verifiable = true;
            sym
        }
        "constructor_decl" => {
            let (name, name_range) = match name_node {
                Some(n) => (text(n, src).to_string(), n.byte_range()),
                None => {
                    let kw = children(node).into_iter().next().map(|c| c.byte_range()).unwrap_or(range.clone());
                    ("_ctor".to_string(), kw)
                }
            };
            let mut sym = Symbol::new(name, Kind::Constructor, name_range, range);
            sym.qname = qualify(prefix, &sym.name);
            sym.signature = with_modifiers(mods, header(node, src, node.start_byte(), &["block_statement"]));
            (sym.params, _) = params_and_outs(node, src, "returns");
            sym.verifiable = true;
            sym
        }
        "function_decl" => {
            let Some(name) = name_node else { return };
            let predicate = children(node).iter().any(|c| matches!(c.kind(), "predicate" | "copredicate"));
            let k = if predicate { Kind::Predicate } else { Kind::Function };
            let mut sym = Symbol::new(text(name, src).to_string(), k, name.byte_range(), range);
            sym.qname = qualify(prefix, &sym.name);
            sym.signature = with_modifiers(mods, header(node, src, node.start_byte(), &["function_body"]));
            (sym.params, _) = params_and_outs(node, src, "returns");
            // Result type follows the formals: `: T` or `: (r: T)`.
            let kids = children(node);
            if let Some(fi) = kids.iter().position(|c| c.kind() == "formals") {
                let rest = &kids[fi + 1..];
                if rest.first().map(|c| c.kind()) == Some(":") {
                    let ty = rest.iter().find(|c| crate::syntax::is_type_node(c.kind())).map(|c| text(*c, src).to_string());
                    if let Some(rname) = rest.iter().take(3).find(|c| c.kind() == "identifier") {
                        sym.returns.push(Param { name: text(*rname, src).to_string(), ty: ty.clone().unwrap_or_default() });
                    }
                    sym.ty = ty;
                }
            }
            if predicate && sym.ty.is_none() {
                sym.ty = Some("bool".to_string());
            }
            sym.verifiable = true;
            sym
        }
        "field_decl" => {
            for name in children_by_field(node, "name") {
                let ty = std::iter::successors(name.next_sibling(), |n| n.next_sibling())
                    .find(|n| crate::syntax::is_type_node(n.kind()))
                    .map(|n| text(n, src).to_string())
                    .unwrap_or_default();
                let mut sym = Symbol::new(text(name, src).to_string(), Kind::Field, name.byte_range(), range.clone());
                sym.qname = qualify(prefix, &sym.name);
                sym.signature = with_modifiers(mods, format!("var {}: {}", sym.name, ty));
                sym.ty = Some(ty);
                sym.is_static = is_static;
                out.push(sym);
            }
            return;
        }
        "constant_field_decl" => {
            let Some(name) = name_node else { return };
            let mut sym = Symbol::new(text(name, src).to_string(), Kind::Const, name.byte_range(), range);
            sym.qname = qualify(prefix, &sym.name);
            sym.signature = with_modifiers(mods, truncate_lines(&tidy_signature(text(node, src)), 10));
            sym.ty = type_after_colon(node, src);
            sym.verifiable = children(node).iter().any(|c| c.kind() == ":=");
            sym
        }
        _ => return,
    };
    sym.is_static = is_static;
    if let Some(gp) = children(node).into_iter().find(|c| c.kind() == "generic_parameters") {
        sym.type_params = named_children(gp)
            .into_iter()
            .filter_map(|tp| named_children(tp).into_iter().find(|n| n.kind() == "identifier"))
            .map(|id| text(id, src).to_string())
            .collect();
    }
    out.push(sym);
}

/// Comments directly above `node`, with no blank line in between and not
/// trailing code on the previous line.
fn doc_comment(node: Node, src: &str) -> Option<String> {
    let mut parts = Vec::new();
    let mut next_row = node.start_position().row;
    let mut cur = node.prev_sibling();
    while let Some(c) = cur {
        if !is_comment(c.kind()) || c.end_position().row + 1 < next_row {
            break;
        }
        if let Some(prev) = c.prev_sibling() {
            if !is_comment(prev.kind()) && prev.end_position().row == c.start_position().row {
                break;
            }
        }
        parts.push(clean_comment(text(c, src)));
        next_row = c.start_position().row;
        cur = c.prev_sibling();
    }
    if parts.is_empty() {
        return None;
    }
    parts.reverse();
    let doc = parts.join("\n").trim().to_string();
    (!doc.is_empty()).then_some(doc)
}

fn clean_comment(raw: &str) -> String {
    if let Some(rest) = raw.strip_prefix("//") {
        let rest = rest.trim_start_matches('/');
        return rest.strip_prefix(' ').unwrap_or(rest).trim_end().to_string();
    }
    let inner = raw.trim_start_matches("/*").trim_start_matches('*').trim_end_matches("*/");
    inner
        .lines()
        .map(|l| {
            let t = l.trim_start();
            let t = t.strip_prefix('*').unwrap_or(t);
            t.strip_prefix(' ').unwrap_or(t).trim_end()
        })
        .collect::<Vec<_>>()
        .join("\n")
        .trim()
        .to_string()
}

/// Indices of nested symbols whose range contains `offset`, outermost first.
pub fn path_at(symbols: &[Symbol], offset: usize) -> Vec<usize> {
    let mut path = Vec::new();
    let mut level = symbols;
    loop {
        match level.iter().position(|s| s.range.start <= offset && offset <= s.range.end) {
            Some(i) => {
                path.push(i);
                level = &level[i].children;
            }
            None => return path,
        }
    }
}

/// All symbols that `dafny verify` reports on, depth first.
pub fn verifiables(symbols: &[Symbol]) -> Vec<&Symbol> {
    fn walk<'a>(syms: &'a [Symbol], out: &mut Vec<&'a Symbol>) {
        for s in syms {
            if s.verifiable {
                out.push(s);
            }
            walk(&s.children, out);
        }
    }
    let mut out = Vec::new();
    walk(symbols, &mut out);
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn extract_src(src: &str) -> FileSymbols {
        let tree = crate::syntax::parse(src, None);
        extract(tree.root_node(), src)
    }

    #[test]
    fn extracts_nested_declarations() {
        let src = r#"include "lib.dfy"
module Outer {
  import opened Lib
  // Holds a counter.
  class C extends T {
    var f: int, g: bool
    constructor() { f := 0; }
    ghost method Inc(x: int) returns (y: int)
      ensures y == x + 1
    { y := x + 1; }
  }
  datatype D = A(x: int, nat) | B { function Get(): int { 0 } }
  const K: nat := 3
  function F(n: nat): (r: nat) { n }
  predicate P(n: int) { n > 0 }
  lemma L() {}
  type Small = n: int | 0 <= n < 10
  newtype Pos = n: int | n > 0 witness 1
}
"#;
        let fs = extract_src(src);
        assert_eq!(fs.includes.len(), 1);
        assert_eq!(fs.includes[0].path, "lib.dfy");
        let outer = &fs.symbols[0];
        assert_eq!(outer.kind, Kind::Module);
        let names: Vec<_> = outer.children.iter().map(|s| (s.name.as_str(), s.kind)).collect();
        assert_eq!(
            names,
            vec![
                ("Lib", Kind::Import),
                ("C", Kind::Class),
                ("D", Kind::Datatype),
                ("K", Kind::Const),
                ("F", Kind::Function),
                ("P", Kind::Predicate),
                ("L", Kind::Lemma),
                ("Small", Kind::TypeSynonym),
                ("Pos", Kind::Newtype),
            ]
        );
        let c = &outer.children[1];
        assert_eq!(c.doc.as_deref(), Some("Holds a counter."));
        assert_eq!(c.extends, vec!["T"]);
        let members: Vec<_> = c.children.iter().map(|s| s.qname.as_str()).collect();
        assert_eq!(members, vec!["Outer.C.f", "Outer.C.g", "Outer.C._ctor", "Outer.C.Inc"]);
        let inc = &c.children[3];
        assert_eq!(inc.signature, "ghost method Inc(x: int) returns (y: int)\n  ensures y == x + 1");
        assert_eq!(inc.params, vec![Param { name: "x".into(), ty: "int".into() }]);
        assert_eq!(inc.returns, vec![Param { name: "y".into(), ty: "int".into() }]);
        let d = &outer.children[2];
        let ctor = &d.children[0];
        assert_eq!(ctor.kind, Kind::Ctor);
        assert_eq!(ctor.children[0].name, "x");
        assert_eq!(ctor.params.len(), 2);
        assert_eq!(d.children[2].qname, "Outer.D.Get");
        let f = &outer.children[4];
        assert_eq!(f.ty.as_deref(), Some("nat"));
        assert_eq!(f.returns[0].name, "r");
        assert!(outer.children[7].verifiable);
        let qnames: Vec<_> = verifiables(&fs.symbols).iter().map(|s| s.qname.clone()).collect();
        assert!(qnames.contains(&"Outer.K".to_string()));
        assert!(qnames.contains(&"Outer.C._ctor".to_string()));
    }
}
