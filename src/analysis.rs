//! Scope walking and name resolution on top of the tree-sitter tree.
//!
//! This is an approximation of Dafny's resolver: it knows declarations, scopes,
//! imports and declared types, which covers navigation and completion. Type
//! checking itself is left to `dafny`.

use std::ops::Range;
use std::sync::Arc;

use tree_sitter::Node;

use crate::state::{FileData, State};
use crate::symbols::{self, base_type_name, Kind, Symbol};
use crate::syntax::{ancestors, children, identifier_at, is_type_node, named_children, node_at, text, type_after_colon};

const MAX_DEPTH: u32 = 8;
const MAX_FALLBACK: usize = 10;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LocalKind {
    Param,
    Return,
    Var,
    Bound,
    TypeParam,
    LoopVar,
    Pattern,
}

impl LocalKind {
    pub fn label(self) -> &'static str {
        match self {
            LocalKind::Param => "parameter",
            LocalKind::Return => "out parameter",
            LocalKind::Var => "var",
            LocalKind::Bound => "bound variable",
            LocalKind::TypeParam => "type parameter",
            LocalKind::LoopVar => "loop variable",
            LocalKind::Pattern => "pattern variable",
        }
    }
}

/// The right-hand side that initializes a local, for type inference.
#[derive(Clone, Debug)]
pub struct Init {
    pub range: Range<usize>,
    pub index: usize,
}

#[derive(Clone, Debug)]
pub struct Local {
    pub name: String,
    pub name_range: Range<usize>,
    pub kind: LocalKind,
    pub ty: Option<String>,
    pub init: Option<Init>,
    /// The part of the file where the local is visible.
    pub scope: Range<usize>,
}

/// A symbol identified by its file and its index path in the file's symbol tree.
#[derive(Clone)]
pub struct SymRef {
    pub file: Arc<FileData>,
    pub path: Vec<usize>,
}

impl SymRef {
    pub fn sym(&self) -> &Symbol {
        let mut s = &self.file.syms.symbols[self.path[0]];
        for &i in &self.path[1..] {
            s = &s.children[i];
        }
        s
    }

    pub fn child(&self, i: usize) -> SymRef {
        let mut path = self.path.clone();
        path.push(i);
        SymRef { file: self.file.clone(), path }
    }

    pub fn children(&self) -> Vec<SymRef> {
        (0..self.sym().children.len()).map(|i| self.child(i)).collect()
    }

    pub fn parent(&self) -> Option<SymRef> {
        (self.path.len() > 1).then(|| SymRef { file: self.file.clone(), path: self.path[..self.path.len() - 1].to_vec() })
    }

    pub fn same(&self, other: &SymRef) -> bool {
        self.file.uri == other.file.uri && self.sym().name_range == other.sym().name_range
    }
}

pub fn top_level(file: &Arc<FileData>) -> Vec<SymRef> {
    (0..file.syms.symbols.len()).map(|i| SymRef { file: file.clone(), path: vec![i] }).collect()
}

/// What a name refers to.
#[derive(Clone)]
pub enum Target {
    Local { file: Arc<FileData>, local: Local },
    Sym(SymRef),
}

impl Target {
    pub fn file(&self) -> &Arc<FileData> {
        match self {
            Target::Local { file, .. } => file,
            Target::Sym(s) => &s.file,
        }
    }

    pub fn name_range(&self) -> Range<usize> {
        match self {
            Target::Local { local, .. } => local.name_range.clone(),
            Target::Sym(s) => s.sym().name_range.clone(),
        }
    }

    pub fn name(&self) -> String {
        match self {
            Target::Local { local, .. } => local.name.clone(),
            Target::Sym(s) => s.sym().name.clone(),
        }
    }

    pub fn same(&self, other: &Target) -> bool {
        self.file().uri == other.file().uri && self.name_range() == other.name_range()
    }
}

// ---------------------------------------------------------------------------
// Locals

fn local(node: Node, src: &str, kind: LocalKind, ty: Option<String>, scope: &Range<usize>) -> Local {
    Local {
        name: text(node, src).to_string(),
        name_range: node.byte_range(),
        kind,
        ty,
        init: None,
        scope: scope.clone(),
    }
}

fn next_type_text(node: Node, src: &str) -> Option<String> {
    let mut cur = node.next_sibling();
    while let Some(n) = cur {
        if is_type_node(n.kind()) {
            return Some(text(n, src).to_string());
        }
        if !matches!(n.kind(), ":" | "(") {
            return None;
        }
        cur = n.next_sibling();
    }
    None
}

fn pattern_binders(node: Node, src: &str, kind: LocalKind, scope: &Range<usize>, out: &mut Vec<Local>) {
    match node.kind() {
        "id_pattern" => {
            if let Some(id) = named_children(node).into_iter().find(|n| n.kind() == "identifier") {
                out.push(local(id, src, kind, type_after_colon(node, src), scope));
            }
        }
        "constructor_pattern" => {
            // The first identifier names the constructor.
            for child in named_children(node).into_iter().skip(1) {
                pattern_binders(child, src, kind, scope, out);
            }
        }
        "tuple_pattern" => {
            for child in named_children(node) {
                pattern_binders(child, src, kind, scope, out);
            }
        }
        "case_pattern" => {
            let kids = children(node);
            let first_is_name = kids.first().map(|k| k.kind()) == Some("identifier");
            let is_ctor = kids.get(1).map(|k| k.kind()) == Some("(");
            if first_is_name && !is_ctor {
                out.push(local(kids[0], src, kind, type_after_colon(node, src), scope));
            } else {
                for child in named_children(node) {
                    if child.kind() == "case_pattern" {
                        pattern_binders(child, src, kind, scope, out);
                    }
                }
            }
        }
        _ => {}
    }
}

fn type_params(node: Node, src: &str, scope: &Range<usize>, out: &mut Vec<Local>) {
    for tp in named_children(node) {
        if tp.kind() == "type_parameter" {
            if let Some(id) = named_children(tp).into_iter().find(|n| n.kind() == "identifier") {
                out.push(local(id, src, LocalKind::TypeParam, None, scope));
            }
        }
    }
}

/// Named children that follow one of `starts` and come before `stop`.
fn exprs_between<'t>(kids: &[Node<'t>], starts: &[&str], stop: &str) -> Vec<Node<'t>> {
    let mut on = false;
    let mut out = Vec::new();
    for k in kids {
        if starts.contains(&k.kind()) {
            on = true;
        } else if k.kind() == stop {
            break;
        } else if on && k.is_named() && !crate::syntax::is_comment(k.kind()) {
            out.push(*k);
        }
    }
    out
}

fn var_decl_binders(stmt: Node, src: &str, scope: &Range<usize>, out: &mut Vec<Local>) {
    let kids = children(stmt);
    let decls: Vec<Node> = kids.iter().copied().filter(|c| matches!(c.kind(), "local_var_decl" | "case_pattern")).collect();
    let rhs: Vec<Node> = exprs_between(&kids, &[":=", ":-"], ";").into_iter().filter(|n| n.kind() == "rhs").collect();
    for (i, d) in decls.iter().enumerate() {
        let start = out.len();
        if d.kind() == "local_var_decl" {
            if let Some(n) = d.child_by_field_name("name") {
                out.push(local(n, src, LocalKind::Var, type_after_colon(*d, src), scope));
            }
        } else {
            pattern_binders(*d, src, LocalKind::Var, scope, out);
        }
        let init = if rhs.len() == decls.len() { rhs.get(i) } else { rhs.first() };
        if let (Some(init), true) = (init, out.len() == start + 1) {
            out[start].init = Some(Init { range: init.byte_range(), index: if rhs.len() == decls.len() { 0 } else { i } });
        }
    }
}

/// Variables that `node` introduces for code inside it. Local variable
/// declarations only count when they end before `before`.
pub fn binders(node: Node, src: &str, before: Option<usize>) -> Vec<Local> {
    let mut out = Vec::new();
    let scope = node.byte_range();
    match node.kind() {
        "method_decl" | "function_decl" | "constructor_decl" | "iterator_decl" => {
            let name = node.child_by_field_name("name");
            let mut outs = false;
            for child in children(node) {
                match child.kind() {
                    "returns" | "yields" => outs = true,
                    "formals" => {
                        let kind = if outs { LocalKind::Return } else { LocalKind::Param };
                        for f in named_children(child) {
                            if let (true, Some(n)) = (f.kind() == "formal", f.child_by_field_name("name")) {
                                out.push(local(n, src, kind, type_after_colon(f, src), &scope));
                            }
                        }
                    }
                    "generic_parameters" => type_params(child, src, &scope, &mut out),
                    // Named function result: `function F(): (r: T)`
                    "identifier" if Some(child) != name => {
                        out.push(local(child, src, LocalKind::Return, next_type_text(child, src), &scope));
                    }
                    _ => {}
                }
            }
        }
        "lambda_expression" => {
            for child in children(node) {
                match child.kind() {
                    "=>" => break,
                    "identifier" => out.push(local(child, src, LocalKind::Param, None, &scope)),
                    "formal" => {
                        if let Some(n) = child.child_by_field_name("name") {
                            out.push(local(n, src, LocalKind::Param, type_after_colon(child, src), &scope));
                        }
                    }
                    "case_pattern" => pattern_binders(child, src, LocalKind::Param, &scope, &mut out),
                    _ => {}
                }
            }
        }
        "class_decl" | "trait_decl" | "datatype_decl" | "newtype_decl" | "synonym_type_decl" => {
            let name = node.child_by_field_name("name");
            for child in children(node) {
                match child.kind() {
                    "generic_parameters" => type_params(child, src, &scope, &mut out),
                    // `newtype Pos = n: int | n > 0`
                    "identifier" if Some(child) != name => {
                        out.push(local(child, src, LocalKind::Bound, next_type_text(child, src), &scope));
                    }
                    _ => {}
                }
            }
        }
        "quantifier_expression" | "forall_expression" | "set_comprehension" | "map_comprehension" | "forall_statement" => {
            let scope = node.start_byte()..quantifier_end(node);
            for domain in children(node).into_iter().filter(|c| c.kind() == "quantifier_domain") {
                for qv in named_children(domain).into_iter().filter(|n| n.kind() == "quantifier_var") {
                    if let Some(id) = named_children(qv).into_iter().find(|n| n.kind() == "identifier") {
                        out.push(local(id, src, LocalKind::Bound, type_after_colon(qv, src), &scope));
                    }
                }
            }
        }
        "let_expression" | "let_or_fail_expression" | "fn_let_expression" => {
            let kids = children(node);
            let pats: Vec<Node> = kids.iter().copied().filter(|c| c.kind() == "case_pattern").collect();
            let rhs = exprs_between(&kids, &[":=", ":-"], ";");
            for (i, p) in pats.iter().enumerate() {
                let start = out.len();
                pattern_binders(*p, src, LocalKind::Var, &scope, &mut out);
                let init = if rhs.len() == pats.len() { rhs.get(i) } else { rhs.first() };
                if let (Some(init), true) = (init, out.len() == start + 1) {
                    out[start].init = Some(Init { range: init.byte_range(), index: 0 });
                }
            }
        }
        "for_statement" => {
            if let Some(id) = children(node).into_iter().find(|c| c.kind() == "identifier") {
                out.push(local(id, src, LocalKind::LoopVar, type_after_colon(node, src), &scope));
            }
        }
        // Binding guards: `if x :| P(x) { ... }`
        "if_statement" | "if_case_clause" => {
            for child in children(node).into_iter().filter(|c| c.kind() == "identifier") {
                out.push(local(child, src, LocalKind::Bound, next_type_text(child, src), &scope));
            }
        }
        "case_stmt_clause" | "case_expr_clause" | "fn_case_expr_clause" => {
            for child in named_children(node) {
                pattern_binders(child, src, LocalKind::Pattern, &scope, &mut out);
            }
        }
        // `var x :| P(x);` mentions x in its own constraint.
        "var_decl_statement" if children(node).iter().any(|c| c.kind() == ":|") => {
            var_decl_binders(node, src, &scope, &mut out);
        }
        _ => {}
    }
    for child in children(node) {
        if child.kind() == "var_decl_statement" && before.map_or(true, |b| child.end_byte() <= b) {
            var_decl_binders(child, src, &(child.start_byte()..node.end_byte()), &mut out);
        }
    }
    out
}

/// Locals visible at `offset`, innermost first.
pub fn locals_at(file: &FileData, offset: usize) -> Vec<Local> {
    let src = &file.text;
    let mut out = Vec::new();
    let mut scanned = false;
    for anc in ancestors(node_at(file.root(), offset)) {
        out.extend(binders(anc, src, Some(offset)));
        // Quantifiers the grammar closed too early, so they are not ancestors.
        if !scanned && is_clause(anc.kind()) {
            scanned = true;
            for q in descendants(anc).into_iter().filter(|q| is_quantifier(q.kind())) {
                let inside = q.start_byte() <= offset && offset <= q.end_byte();
                if !inside && q.start_byte() <= offset && offset <= quantifier_end(q) {
                    out.extend(binders(q, src, Some(offset)));
                }
            }
        }
    }
    out
}

fn descendants(node: Node) -> Vec<Node> {
    let mut out = Vec::new();
    let mut stack = vec![node];
    while let Some(n) = stack.pop() {
        out.push(n);
        stack.extend(children(n));
    }
    out
}

/// Nodes that end an expression: specification clauses, statements and bodies.
fn is_clause(kind: &str) -> bool {
    kind.ends_with("_clause")
        || kind.ends_with("_statement")
        || matches!(kind, "function_body" | "calc_line" | "constant_field_decl" | "source_file" | "ERROR")
}

fn is_operator_chain(kind: &str) -> bool {
    matches!(
        kind,
        "equiv_expression"
            | "implies_explies_expression"
            | "implies_expression"
            | "logical_expression"
            | "relational_expression"
            | "shift_term"
            | "term"
            | "factor"
            | "bitvector_factor"
    )
}

fn is_quantifier(kind: &str) -> bool {
    matches!(
        kind,
        "quantifier_expression"
            | "forall_expression"
            | "set_comprehension"
            | "map_comprehension"
            | "lambda_expression"
            | "let_expression"
            | "fn_let_expression"
            | "let_or_fail_expression"
    )
}

/// Where a quantifier body really ends. Dafny extends it as far right as
/// possible: to the closing bracket around it or the end of the clause. The
/// grammar often ends it earlier, at the next `==>`, `&&` or suffix.
fn quantifier_end(q: Node) -> usize {
    let mut end = q.end_byte();
    let mut cur = q;
    while let Some(p) = cur.parent() {
        if is_clause(p.kind()) {
            return p.end_byte();
        }
        match p.kind() {
            "parenthesized_expression" | "tuple_expression" | "seq_display" | "set_display" | "multiset_display"
            | "map_display" | "cardinality_expression" | "actual_binding" | "old_expression" | "fresh_expression"
            | "unchanged_expression" | "multiset_construction" | "seq_construction" => return p.end_byte(),
            // Inside the brackets of `f(...)` or `a[...]`.
            "suffix_expression" | "call_expression" if p.child(0) != Some(cur) => return p.end_byte(),
            "suffix_expression" | "call_expression" | "unary_expression" | "as_expression" => {}
            k if is_operator_chain(k) => {}
            _ => return end,
        }
        end = p.end_byte();
        cur = p;
    }
    end
}

/// The local declared by this identifier, if it is a binding occurrence.
pub fn declared_local(file: &FileData, ident: Node) -> Option<Local> {
    for anc in ancestors(ident) {
        if let Some(l) = binders(anc, &file.text, None).into_iter().find(|l| l.name_range == ident.byte_range()) {
            return Some(l);
        }
    }
    None
}

pub fn symbol_declared_at(file: &Arc<FileData>, range: &Range<usize>) -> Option<SymRef> {
    fn walk(syms: &[Symbol], range: &Range<usize>, path: &mut Vec<usize>) -> bool {
        for (i, s) in syms.iter().enumerate() {
            path.push(i);
            if s.name_range == *range || (s.range.start <= range.start && range.end <= s.range.end && walk(&s.children, range, path)) {
                return true;
            }
            path.pop();
        }
        false
    }
    let mut path = Vec::new();
    walk(&file.syms.symbols, range, &mut path).then(|| SymRef { file: file.clone(), path })
}

// ---------------------------------------------------------------------------
// Symbol scopes

/// Symbols that enclose `offset`, outermost first.
pub fn chain_at(file: &Arc<FileData>, offset: usize) -> Vec<SymRef> {
    let path = symbols::path_at(&file.syms.symbols, offset);
    (1..=path.len()).map(|n| SymRef { file: file.clone(), path: path[..n].to_vec() }).collect()
}

fn push_ctors(s: &SymRef, out: &mut Vec<SymRef>) {
    for c in s.children() {
        if c.sym().kind == Kind::Ctor {
            out.push(c);
        }
    }
}

/// Adds datatype constructors and the members of opened imports, which are
/// visible without qualification.
fn expand(st: &State, syms: Vec<SymRef>, follow_imports: bool, depth: u32) -> Vec<SymRef> {
    let mut out = Vec::with_capacity(syms.len());
    for s in syms {
        let sym = s.sym();
        if sym.kind == Kind::Datatype {
            push_ctors(&s, &mut out);
        } else if sym.kind == Kind::Import && sym.opened && follow_imports {
            if let Some(m) = resolve_import(st, &s, depth + 1) {
                for c in m.children() {
                    if c.sym().kind == Kind::Datatype {
                        push_ctors(&c, &mut out);
                    }
                    if c.sym().kind != Kind::Import {
                        out.push(c);
                    }
                }
            }
        }
        out.push(s);
    }
    out
}

/// Module-level scopes around `offset`, innermost first, ending with the
/// default module (this file, its includes and its project).
fn module_levels(st: &State, file: &Arc<FileData>, offset: usize, follow_imports: bool, depth: u32) -> Vec<Vec<SymRef>> {
    let mut levels = Vec::new();
    for s in chain_at(file, offset).into_iter().rev() {
        if s.sym().kind == Kind::Module {
            levels.push(expand(st, s.children(), follow_imports, depth));
        }
    }
    let mut top = top_level(file);
    for f in st.scope_files(file) {
        top.extend(top_level(&f));
    }
    levels.push(expand(st, top, follow_imports, depth));
    levels
}

/// All scopes around `offset`, innermost first: enclosing type members, then module levels.
pub fn scope_levels(st: &State, file: &Arc<FileData>, offset: usize) -> Vec<Vec<SymRef>> {
    let mut levels = Vec::new();
    for s in chain_at(file, offset).into_iter().rev() {
        if s.sym().kind.is_type() {
            levels.push(members_of(st, &s, 0));
        }
    }
    levels.extend(module_levels(st, file, offset, true, 0));
    levels
}

/// Members of a type, including datatype destructors and inherited trait members.
pub fn members_of(st: &State, t: &SymRef, depth: u32) -> Vec<SymRef> {
    let mut out = Vec::new();
    for c in t.children() {
        if c.sym().kind == Kind::Ctor {
            out.extend(c.children());
        }
        out.push(c);
    }
    if depth < 4 {
        let sym = t.sym();
        let mut parents: Vec<&String> = sym.extends.iter().collect();
        if sym.kind == Kind::TypeSynonym {
            parents.extend(sym.ty.as_ref());
        }
        for p in parents {
            if let Some(p) = resolve_type_name(st, &t.file, sym.range.start, p) {
                if !p.same(t) {
                    out.extend(members_of(st, &p, depth + 1));
                }
            }
        }
    }
    out
}

/// Symbols with this name anywhere in the workspace, shallowest first.
pub fn global_find(st: &State, name: &str, filter: impl Fn(&Symbol) -> bool) -> Vec<SymRef> {
    fn walk(r: SymRef, name: &str, filter: &dyn Fn(&Symbol) -> bool, out: &mut Vec<(usize, SymRef)>) {
        let sym = r.sym();
        if sym.name == name && filter(sym) {
            out.push((r.path.len(), r.clone()));
        }
        for c in r.children() {
            walk(c, name, filter, out);
        }
    }
    let mut found = Vec::new();
    for f in st.all_files() {
        if !f.text.contains(name) {
            continue;
        }
        for r in top_level(&f) {
            walk(r, name, &filter, &mut found);
        }
    }
    found.sort_by_key(|(depth, _)| *depth);
    found.into_iter().map(|(_, r)| r).collect()
}

fn is_builtin_type(name: &str) -> bool {
    matches!(
        name,
        "int" | "nat" | "real" | "bool" | "char" | "string" | "seq" | "set" | "iset" | "multiset" | "map" | "imap"
            | "object" | "object?" | "ORDINAL" | "fp32" | "fp64"
    ) || name.starts_with("array")
        || (name.starts_with("bv") && name[2..].chars().all(|c| c.is_ascii_digit()))
}

/// Resolves a written type such as `M.T<int>?` to its declaration.
pub fn resolve_type_name(st: &State, file: &Arc<FileData>, offset: usize, ty: &str) -> Option<SymRef> {
    let base = base_type_name(ty);
    if base.is_empty() || is_builtin_type(base) {
        return None;
    }
    let segs: Vec<&str> = base.split('.').collect();
    let (last, prefix) = segs.split_last()?;
    if prefix.is_empty() {
        for level in module_levels(st, file, offset, true, 0) {
            if let Some(s) = level.into_iter().find(|s| s.sym().name == *last && s.sym().kind.is_type()) {
                return Some(s);
            }
        }
        return global_find(st, last, |s| s.kind.is_type()).into_iter().next();
    }
    let m = resolve_module_path(st, file, offset, prefix, false, 0)?;
    m.children().into_iter().find(|c| c.sym().name == *last && c.sym().kind.is_type())
}

pub fn resolve_module_path(
    st: &State,
    file: &Arc<FileData>,
    offset: usize,
    segs: &[&str],
    skip_imports: bool,
    depth: u32,
) -> Option<SymRef> {
    if depth > MAX_DEPTH {
        return None;
    }
    let (first, rest) = segs.split_first()?;
    let mut cur = None;
    'levels: for level in module_levels(st, file, offset, false, depth) {
        for s in level.into_iter().filter(|s| s.sym().name == *first) {
            match s.sym().kind {
                Kind::Module => {
                    cur = Some(s);
                    break 'levels;
                }
                Kind::Import if !skip_imports => {
                    if let Some(m) = resolve_import(st, &s, depth + 1) {
                        cur = Some(m);
                        break 'levels;
                    }
                }
                _ => {}
            }
        }
    }
    let mut cur = cur.or_else(|| global_find(st, first, |s| s.kind == Kind::Module).into_iter().next())?;
    for seg in rest {
        let next = cur
            .children()
            .into_iter()
            .find(|c| c.sym().name == *seg && matches!(c.sym().kind, Kind::Module | Kind::Import))?;
        cur = if next.sym().kind == Kind::Import { resolve_import(st, &next, depth + 1)? } else { next };
    }
    Some(cur)
}

/// The module an import statement refers to.
pub fn resolve_import(st: &State, imp: &SymRef, depth: u32) -> Option<SymRef> {
    let target = imp.sym().target.clone()?;
    let segs: Vec<&str> = target.split('.').collect();
    resolve_module_path(st, &imp.file, imp.sym().range.start, &segs, true, depth)
}

fn follow_import(st: &State, s: SymRef) -> SymRef {
    if s.sym().kind == Kind::Import {
        resolve_import(st, &s, 0).unwrap_or(s)
    } else {
        s
    }
}

fn dedup(targets: Vec<Target>) -> Vec<Target> {
    let mut out: Vec<Target> = Vec::new();
    for t in targets {
        if !out.iter().any(|o| o.same(&t)) {
            out.push(t);
        }
    }
    out
}

/// Resolves a name through the symbol scopes only (no locals).
pub fn lookup_symbol(st: &State, file: &Arc<FileData>, offset: usize, name: &str) -> Vec<Target> {
    for level in scope_levels(st, file, offset) {
        let hits: Vec<Target> = level
            .into_iter()
            .filter(|s| s.sym().name == name)
            .map(|s| Target::Sym(follow_import(st, s)))
            .collect();
        if !hits.is_empty() {
            return dedup(hits);
        }
    }
    // A bare discriminator `Cons?` inside a datatype member.
    if let Some(ctor) = name.strip_suffix('?') {
        let hits = ctor_hits(st, file, offset, ctor);
        if !hits.is_empty() {
            return hits;
        }
    }
    global_find(st, name, |_| true).into_iter().take(MAX_FALLBACK).map(Target::Sym).collect()
}

fn ctor_hits(st: &State, file: &Arc<FileData>, offset: usize, name: &str) -> Vec<Target> {
    lookup_symbol(st, file, offset, name)
        .into_iter()
        .filter(|t| matches!(t, Target::Sym(s) if s.sym().kind == Kind::Ctor))
        .collect()
}

/// Resolves a name written in a type position, where only types count.
fn lookup_type(st: &State, file: &Arc<FileData>, offset: usize, name: &str) -> Vec<Target> {
    if let Some(l) = locals_at(file, offset).into_iter().find(|l| l.name == name && l.kind == LocalKind::TypeParam) {
        return vec![Target::Local { file: file.clone(), local: l }];
    }
    for level in scope_levels(st, file, offset) {
        let hits: Vec<Target> = level
            .into_iter()
            .filter(|s| s.sym().name == name && s.sym().kind.is_type())
            .map(Target::Sym)
            .collect();
        if !hits.is_empty() {
            return dedup(hits);
        }
    }
    global_find(st, name, |s| s.kind.is_type()).into_iter().take(MAX_FALLBACK).map(Target::Sym).collect()
}

/// True when the identifier is part of a written type, such as `seq<M.T>`.
fn in_type_position(ident: Node) -> bool {
    ancestors(ident)
        .skip(1)
        .take_while(|a| matches!(a.kind(), "qualified_name" | "generic_instantiation" | "type_arguments") || is_type_node(a.kind()))
        .any(|a| is_type_node(a.kind()))
}

/// `datatype D = D(...)` declares a type and a constructor with the same name.
/// In expressions the constructor is meant, unless a member is accessed (`D.x`).
fn prefer_ctor(hits: Vec<Target>, static_access: bool) -> Vec<Target> {
    let kind = |t: &Target| match t {
        Target::Sym(s) => Some(s.sym().kind),
        _ => None,
    };
    let has_ctor = hits.iter().any(|t| kind(t) == Some(Kind::Ctor));
    let has_type = hits.iter().any(|t| kind(t).is_some_and(Kind::is_type));
    if !(has_ctor && has_type) {
        return hits;
    }
    let keep = |t: &Target| if static_access { kind(t).is_some_and(Kind::is_type) } else { kind(t) == Some(Kind::Ctor) };
    hits.into_iter().filter(keep).collect()
}

/// Resolves an unqualified name at `offset`.
pub fn lookup(st: &State, file: &Arc<FileData>, offset: usize, name: &str) -> Vec<Target> {
    if let Some(l) = locals_at(file, offset).into_iter().find(|l| l.name == name) {
        // In `case Nil =>` the name is a constructor, not a new variable.
        if l.kind == LocalKind::Pattern {
            let ctors = ctor_hits(st, file, offset, name);
            if !ctors.is_empty() {
                return ctors;
            }
        }
        return vec![Target::Local { file: file.clone(), local: l }];
    }
    lookup_symbol(st, file, offset, name)
}

// ---------------------------------------------------------------------------
// Values and types

/// A type as written in the source, with the place it was written so that the
/// names inside it resolve in the right scope.
#[derive(Clone)]
pub struct TypeVal {
    pub text: String,
    pub decl: Option<SymRef>,
    pub file: Arc<FileData>,
    pub offset: usize,
}

/// What an expression denotes, as far as member lookup is concerned.
#[derive(Clone)]
pub enum Val {
    Module(SymRef),
    /// A type name used as a prefix, as in `T.Create()`.
    Static(SymRef),
    /// A value of a type.
    Typed(TypeVal),
    /// A function, method or constructor that has not been applied.
    Callable(SymRef),
    Unknown,
}

fn typed(st: &State, file: &Arc<FileData>, offset: usize, ty: &str) -> Val {
    let text = ty.trim().to_string();
    let decl = resolve_type_name(st, file, offset, &text);
    Val::Typed(TypeVal { text, decl, file: file.clone(), offset })
}

fn builtin(file: &Arc<FileData>, ty: &str) -> Val {
    Val::Typed(TypeVal { text: ty.to_string(), decl: None, file: file.clone(), offset: 0 })
}

fn decl_val(decl: SymRef) -> Val {
    Val::Typed(TypeVal {
        text: decl.sym().name.clone(),
        file: decl.file.clone(),
        offset: decl.sym().range.start,
        decl: Some(decl),
    })
}

fn find_node_with_range<'t>(root: Node<'t>, range: &Range<usize>) -> Option<Node<'t>> {
    let mut node = root.descendant_for_byte_range(range.start, range.end)?;
    while node.byte_range() != *range {
        node = node.parent()?;
        if node.start_byte() < range.start {
            return None;
        }
    }
    Some(node)
}

pub fn classify(st: &State, t: &Target) -> Val {
    match t {
        Target::Local { file, local } => {
            if let Some(ty) = &local.ty {
                return typed(st, file, local.name_range.start, ty);
            }
            if local.kind == LocalKind::Pattern || local.kind == LocalKind::Var {
                if let Some(v) = pattern_type(st, file, local) {
                    return v;
                }
            }
            let Some(init) = &local.init else { return Val::Unknown };
            let Some(node) = find_node_with_range(file.root(), &init.range) else { return Val::Unknown };
            // `var a, b := M();` takes the matching out parameter.
            if init.index > 0 {
                if let Some(call) = as_call(unwrap_expr(node)) {
                    if let Val::Callable(f) = infer(st, file, call, 1) {
                        return call_result(st, file, &f, init.index, &[]);
                    }
                }
            }
            infer(st, file, node, 0)
        }
        Target::Sym(s) => sym_val(st, s),
    }
}

/// Type of a variable bound by a constructor pattern, `case Ctor(x, y) =>`,
/// taken from the constructor's parameter list.
fn pattern_type(st: &State, file: &Arc<FileData>, local: &Local) -> Option<Val> {
    let ident = find_node_with_range(file.root(), &local.name_range)?;
    let mut pat = ident.parent()?;
    if pat.kind() == "id_pattern" {
        pat = pat.parent()?;
    }
    let is_ctor_pattern = pat.kind() == "constructor_pattern"
        || (pat.kind() == "case_pattern" && pat.child(1).map(|c| c.kind()) == Some("("));
    if !is_ctor_pattern {
        return None;
    }
    let ctor_ident = pat.named_child(0).filter(|n| n.kind() == "identifier")?;
    let subpatterns: Vec<Node> = named_children(pat).into_iter().skip(1).collect();
    let index = subpatterns.iter().position(|p| p.start_byte() <= local.name_range.start && local.name_range.end <= p.end_byte())?;
    let ctor = ctor_hits(st, file, ctor_ident.start_byte(), text(ctor_ident, &file.text)).into_iter().next()?;
    let Target::Sym(ctor) = ctor else { return None };
    let param = ctor.sym().params.get(index)?;
    Some(typed(st, &ctor.file, ctor.sym().range.start, &param.ty))
}

fn as_call(node: Node) -> Option<Node> {
    let node = if node.kind() == "rhs" { node.named_child(0)? } else { node };
    let node = unwrap_expr(node);
    if node.kind() == "suffix_expression" && node.child(1).map(|c| c.kind()) == Some("(") {
        node.child(0)
    } else {
        None
    }
}

fn sym_val(st: &State, s: &SymRef) -> Val {
    let sym = s.sym();
    match sym.kind {
        Kind::Module => Val::Module(s.clone()),
        Kind::Import => resolve_import(st, s, 0).map(Val::Module).unwrap_or(Val::Unknown),
        k if k.is_type() => Val::Static(s.clone()),
        Kind::Field | Kind::Const | Kind::Destructor => match &sym.ty {
            Some(ty) => typed(st, &s.file, sym.range.start, ty),
            None => Val::Unknown,
        },
        _ => Val::Callable(s.clone()),
    }
}

/// The type that declares a member: the class or datatype, skipping the constructor for destructors.
fn owner_type(s: &SymRef) -> Option<SymRef> {
    let p = s.parent()?;
    let p = if p.sym().kind == Kind::Ctor { p.parent()? } else { p };
    p.sym().kind.is_type().then_some(p)
}

/// Replaces whole-word occurrences of type parameters. None if nothing changed.
fn subst(ty: &str, bindings: &[(String, String)]) -> Option<String> {
    let mut out = String::new();
    let mut word = String::new();
    let mut changed = false;
    let mut flush = |word: &mut String, out: &mut String| {
        if let Some((_, to)) = bindings.iter().find(|(from, _)| from == word) {
            out.push_str(to);
            changed = true;
        } else {
            out.push_str(word);
        }
        word.clear();
    };
    for c in ty.chars() {
        if c.is_alphanumeric() || c == '_' || c == '\'' {
            word.push(c);
        } else {
            flush(&mut word, &mut out);
            out.push(c);
        }
    }
    flush(&mut word, &mut out);
    changed.then_some(out)
}

/// Binds type parameters by matching a declared type against an actual one,
/// e.g. `seq<T>` against `seq<Host>` gives T = Host.
fn unify(pattern: &str, actual: &str, params: &[String], out: &mut Vec<(String, String)>) {
    let (p, a) = (pattern.trim(), actual.trim());
    if params.iter().any(|t| t == p) {
        if !out.iter().any(|(t, _)| t == p) {
            out.push((p.to_string(), a.to_string()));
        }
        return;
    }
    if base_type_name(p) == base_type_name(a) {
        for (pp, aa) in type_args(p).iter().zip(type_args(a).iter()) {
            unify(pp, aa, params, out);
        }
    }
}

/// The type of a member accessed on `recv`, with the receiver's type
/// arguments substituted: `o.value` on `Option<Host>` is a `Host`.
fn member_val(st: &State, recv: &Val, t: &Target) -> Val {
    let base = classify(st, t);
    let (Val::Typed(rv), Target::Sym(s)) = (recv, t) else { return base };
    let Some(owner) = owner_type(s) else { return base };
    let params = &owner.sym().type_params;
    let Some(ty) = s.sym().ty.as_ref().filter(|_| !params.is_empty() && !s.sym().kind.is_callable()) else { return base };
    let bindings: Vec<(String, String)> = params.iter().cloned().zip(type_args(&rv.text)).collect();
    match subst(ty, &bindings) {
        Some(new) => typed(st, &rv.file, rv.offset, &new),
        None => base,
    }
}

/// Argument expressions of a call node `f(a, b)`.
fn call_args(call: Node) -> Vec<Node> {
    children(call)
        .into_iter()
        .filter(|c| c.kind() == "actual_binding")
        .filter_map(|b| b.named_child(b.named_child_count().saturating_sub(1)))
        .collect()
}

/// Result of calling `f`. Type parameters of a generic function or datatype
/// are bound from the argument types when the arguments are known.
fn call_result(st: &State, file: &Arc<FileData>, f: &SymRef, index: usize, args: &[Node]) -> Val {
    let sym = f.sym();
    let bind = |params: &[String]| -> Vec<(String, String)> {
        let mut out = Vec::new();
        for (formal, arg) in sym.params.iter().zip(args) {
            if let Val::Typed(av) = infer(st, file, *arg, 4) {
                unify(&formal.ty, &av.text, params, &mut out);
            }
        }
        out
    };
    let result = match sym.kind {
        Kind::Function | Kind::Predicate => sym.ty.clone(),
        Kind::Method | Kind::Lemma => sym.returns.get(index).map(|p| p.ty.clone()),
        Kind::Ctor | Kind::Constructor => {
            let Some(owner) = owner_type(f).or_else(|| f.parent()) else { return Val::Unknown };
            let params = &owner.sym().type_params;
            if sym.kind == Kind::Ctor && !params.is_empty() && !args.is_empty() {
                let bindings = bind(params);
                if bindings.len() == params.len() {
                    let actual: Vec<String> = params.iter().map(|p| bindings.iter().find(|(t, _)| t == p).unwrap().1.clone()).collect();
                    let text = format!("{}<{}>", owner.sym().name, actual.join(", "));
                    return Val::Typed(TypeVal { text, file: owner.file.clone(), offset: owner.sym().range.start, decl: Some(owner) });
                }
            }
            return decl_val(owner);
        }
        _ => None,
    };
    let Some(result) = result else { return Val::Unknown };
    if !sym.type_params.is_empty() && !args.is_empty() {
        if let Some(new) = subst(&result, &bind(&sym.type_params)) {
            return typed(st, file, args[0].start_byte(), &new);
        }
    }
    typed(st, &f.file, sym.range.start, &result)
}

pub fn apply_call(st: &State, file: &Arc<FileData>, v: &Val, args: &[Node]) -> Val {
    match v {
        Val::Callable(f) => call_result(st, file, f, 0, args),
        _ => Val::Unknown,
    }
}

/// Splits the type arguments of `seq<T>` or `map<K, V>`.
pub fn type_args(ty: &str) -> Vec<String> {
    let Some(open) = ty.find('<') else { return Vec::new() };
    let mut depth = 0;
    let mut args = Vec::new();
    let mut cur = String::new();
    for c in ty[open + 1..].chars() {
        match c {
            '<' | '(' => {
                depth += 1;
                cur.push(c);
            }
            '>' | ')' if depth == 0 => break,
            '>' | ')' => {
                depth -= 1;
                cur.push(c);
            }
            ',' if depth == 0 => args.push(std::mem::take(&mut cur).trim().to_string()),
            _ => cur.push(c),
        }
    }
    if !cur.trim().is_empty() {
        args.push(cur.trim().to_string());
    }
    args
}

pub fn index_val(st: &State, v: &Val) -> Val {
    let Val::Typed(tv) = v else { return Val::Unknown };
    let args = type_args(&tv.text);
    let elem = match base_type_name(&tv.text) {
        "string" => Some("char".to_string()),
        "map" | "imap" => args.get(1).cloned(),
        b if b == "seq" || b.starts_with("array") || b == "multiset" => args.first().cloned(),
        _ => None,
    };
    match elem {
        Some(e) => typed(st, &tv.file, tv.offset, &e),
        None => Val::Unknown,
    }
}

fn this_type(file: &Arc<FileData>, offset: usize) -> Val {
    match chain_at(file, offset).into_iter().rev().find(|s| s.sym().kind.is_type()) {
        Some(t) => decl_val(t),
        None => Val::Unknown,
    }
}

/// Skips the single-child wrapper nodes the expression grammar produces.
fn unwrap_expr(mut node: Node) -> Node {
    loop {
        let wrapper = matches!(
            node.kind(),
            "equiv_expression"
                | "implies_explies_expression"
                | "implies_expression"
                | "logical_expression"
                | "relational_expression"
                | "shift_term"
                | "term"
                | "factor"
                | "bitvector_factor"
                | "as_expression"
                | "unary_expression"
                | "parenthesized_expression"
        );
        match (wrapper && node.named_child_count() == 1, node.named_child(0)) {
            (true, Some(child)) => node = child,
            _ => return node,
        }
    }
}

/// The grammar sometimes attaches a suffix to a whole `a ==> b` chain or
/// quantifier, while Dafny binds suffixes tightest. The real receiver is the
/// rightmost operand.
pub fn effective_receiver(mut node: Node) -> Node {
    loop {
        let n = unwrap_expr(node);
        let binary = is_operator_chain(n.kind()) && n.named_child_count() > 1;
        if binary || is_quantifier(n.kind()) {
            match n.named_child(n.named_child_count() - 1) {
                Some(last) => node = last,
                None => return n,
            }
        } else {
            return n;
        }
    }
}

/// Approximates what an expression denotes.
pub fn infer(st: &State, file: &Arc<FileData>, node: Node, depth: u32) -> Val {
    if depth > 16 {
        return Val::Unknown;
    }
    let src = &file.text;
    let node = unwrap_expr(node);
    match node.kind() {
        "rhs" => {
            let kids = children(node);
            if kids.first().map(|k| k.kind()) == Some("new") {
                let Some(t) = kids.iter().find(|k| is_type_node(k.kind())) else { return Val::Unknown };
                let ty = text(*t, src);
                if kids.iter().any(|k| k.kind() == "[") {
                    return typed(st, file, node.start_byte(), &format!("array<{ty}>"));
                }
                return typed(st, file, node.start_byte(), ty);
            }
            match kids.into_iter().find(|k| k.is_named()) {
                Some(e) => infer(st, file, e, depth + 1),
                None => Val::Unknown,
            }
        }
        "name_segment" => {
            let Some(id) = node.named_child(0).filter(|n| n.kind() == "identifier") else { return Val::Unknown };
            match lookup(st, file, id.start_byte(), text(id, src)).first() {
                Some(t) => classify(st, t),
                None => Val::Unknown,
            }
        }
        "this_expression" => this_type(file, node.start_byte()),
        "suffix_expression" => {
            let kids = children(node);
            let (Some(recv), Some(op)) = (kids.first(), kids.get(1)) else { return Val::Unknown };
            let recv_val = infer(st, file, effective_receiver(*recv), depth + 1);
            match op.kind() {
                "." => match kids.get(2).filter(|k| k.kind() == "identifier") {
                    Some(m) => match member(st, &recv_val, text(*m, src)).first() {
                        Some(t) => member_val(st, &recv_val, t),
                        None => Val::Unknown,
                    },
                    // Datatype update `d.(f := x)` keeps the type.
                    None => recv_val,
                },
                "(" => apply_call(st, file, &recv_val, &call_args(node)),
                "[" => {
                    if kids.iter().any(|k| k.kind() == "..") {
                        recv_val
                    } else {
                        index_val(st, &recv_val)
                    }
                }
                _ => Val::Unknown,
            }
        }
        "call_expression" => match node.child_by_field_name("function") {
            Some(f) => apply_call(st, file, &infer(st, file, f, depth + 1), &call_args(node)),
            None => Val::Unknown,
        },
        "generic_expression" | "old_expression" => match node.named_child(0) {
            Some(e) => infer(st, file, e, depth + 1),
            None => Val::Unknown,
        },
        "as_expression" => match node.named_child(node.named_child_count().saturating_sub(1)) {
            Some(t) if is_type_node(t.kind()) => typed(st, file, node.start_byte(), text(t, src)),
            _ => Val::Unknown,
        },
        "literal_expression" => {
            let ty = match node.named_child(0).map(|n| n.kind()) {
                Some("integer_literal") => "int",
                Some("real_literal") => "real",
                Some("boolean_literal") => "bool",
                Some("string_literal") => "string",
                Some("char_literal") => "char",
                _ => return Val::Unknown,
            };
            builtin(file, ty)
        }
        "seq_display" | "seq_construction" => builtin(file, "seq"),
        "set_display" | "set_comprehension" => builtin(file, "set"),
        "map_display" | "map_comprehension" => builtin(file, "map"),
        "multiset_display" | "multiset_construction" => builtin(file, "multiset"),
        "cardinality_expression" => builtin(file, "int"),
        _ => Val::Unknown,
    }
}

/// Candidates for `recv.<member>`.
pub fn member_candidates(st: &State, recv: &Val) -> Vec<SymRef> {
    match recv {
        Val::Module(m) => expand(st, m.children(), false, 0),
        Val::Static(t) => members_of(st, t, 0),
        Val::Typed(TypeVal { decl: Some(t), .. }) => members_of(st, t, 0),
        Val::Callable(c) if c.sym().kind == Kind::Ctor => c.parent().map(|p| members_of(st, &p, 0)).unwrap_or_default(),
        _ => Vec::new(),
    }
}

pub fn member(st: &State, recv: &Val, name: &str) -> Vec<Target> {
    let candidates = member_candidates(st, recv);
    let mut hits: Vec<Target> = candidates
        .iter()
        .filter(|s| s.sym().name == name)
        .map(|s| Target::Sym(follow_import(st, s.clone())))
        .collect();
    // Discriminator `d.Cons?` refers to the constructor.
    if hits.is_empty() {
        if let Some(ctor) = name.strip_suffix('?') {
            hits = candidates
                .iter()
                .filter(|s| s.sym().name == ctor && s.sym().kind == Kind::Ctor)
                .map(|s| Target::Sym(s.clone()))
                .collect();
        }
    }
    dedup(hits)
}

/// Members named `name` of any type, used when the receiver type is unknown.
pub fn member_fallback(st: &State, file: &Arc<FileData>, name: &str) -> Vec<Target> {
    let name = name.strip_suffix('?').unwrap_or(name);
    let is_member = |r: &SymRef| r.parent().map_or(false, |p| p.sym().kind.is_type() || p.sym().kind == Kind::Ctor);
    let mut files = vec![file.clone()];
    files.extend(st.scope_files(file));
    let mut hits = Vec::new();
    for f in &files {
        collect_named(&top_level(f), name, &mut hits);
    }
    hits.retain(is_member);
    if hits.is_empty() {
        hits = global_find(st, name, |_| true);
        hits.retain(is_member);
    }
    hits.into_iter().take(MAX_FALLBACK).map(Target::Sym).collect()
}

fn collect_named(syms: &[SymRef], name: &str, out: &mut Vec<SymRef>) {
    for s in syms {
        if s.sym().name == name {
            out.push(s.clone());
        }
        collect_named(&s.children(), name, out);
    }
}

// ---------------------------------------------------------------------------
// Text-based receiver chains, used while typing when the tree is incomplete.

#[derive(Clone, Debug, PartialEq)]
pub enum Seg {
    Name(String),
    Call,
    Index,
}

fn is_ident_byte(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_' || b == b'?' || b == b'\'' || b >= 0x80
}

/// Parses the expression chain that ends right before `end`, e.g. `a.b(x)[i]`.
pub fn chain_before(src: &str, end: usize) -> Vec<Seg> {
    let b = src.as_bytes();
    let mut i = end.min(b.len());
    let mut segs = Vec::new();
    while i > 0 {
        let c = b[i - 1];
        if c == b')' || c == b']' {
            let open = if c == b')' { b'(' } else { b'[' };
            let mut depth = 0i32;
            let mut j = i;
            loop {
                if j == 0 {
                    return Vec::new();
                }
                j -= 1;
                if b[j] == c {
                    depth += 1;
                } else if b[j] == open {
                    depth -= 1;
                    if depth == 0 {
                        break;
                    }
                }
            }
            segs.push(if c == b')' { Seg::Call } else { Seg::Index });
            i = j;
        } else if is_ident_byte(c) {
            let mut j = i;
            while j > 0 && is_ident_byte(b[j - 1]) {
                j -= 1;
            }
            segs.push(Seg::Name(src[j..i].to_string()));
            i = j;
            if i > 0 && b[i - 1] == b'.' && !(i > 1 && b[i - 2] == b'.') {
                i -= 1;
            } else {
                break;
            }
        } else {
            break;
        }
    }
    segs.reverse();
    match segs.first() {
        Some(Seg::Name(n)) if !n.starts_with(|c: char| c.is_ascii_digit()) => segs,
        _ => Vec::new(),
    }
}

pub fn eval_chain(st: &State, file: &Arc<FileData>, offset: usize, segs: &[Seg]) -> Val {
    let mut it = segs.iter();
    let mut val = match it.next() {
        Some(Seg::Name(n)) if n == "this" => this_type(file, offset),
        Some(Seg::Name(n)) => match lookup(st, file, offset, n).first() {
            Some(t) => classify(st, t),
            None => Val::Unknown,
        },
        _ => return Val::Unknown,
    };
    for seg in it {
        val = match seg {
            Seg::Name(m) => match member(st, &val, m).first() {
                Some(t) => member_val(st, &val, t),
                None => Val::Unknown,
            },
            Seg::Call => apply_call(st, file, &val, &[]),
            Seg::Index => index_val(st, &val),
        };
    }
    val
}

/// Resolves the callee written as a chain, e.g. `M.Foo` or `x.Bar`.
pub fn resolve_chain(st: &State, file: &Arc<FileData>, offset: usize, segs: &[Seg]) -> Vec<Target> {
    match segs.split_last() {
        Some((Seg::Name(n), [])) => lookup(st, file, offset, n),
        Some((Seg::Name(n), prefix)) => {
            let recv = eval_chain(st, file, offset, prefix);
            let hits = member(st, &recv, n);
            if hits.is_empty() {
                member_fallback(st, file, n)
            } else {
                hits
            }
        }
        _ => Vec::new(),
    }
}

// ---------------------------------------------------------------------------
// Resolution at a position

pub fn resolve_at(st: &State, file: &Arc<FileData>, offset: usize) -> Vec<Target> {
    match identifier_at(file.root(), offset) {
        Some(ident) => resolve_ident(st, file, ident),
        None => Vec::new(),
    }
}

pub fn resolve_ident(st: &State, file: &Arc<FileData>, ident: Node) -> Vec<Target> {
    let src = &file.text;
    let name = text(ident, src);
    let parent = ident.parent();
    let parent_kind = parent.map(|p| p.kind()).unwrap_or("");

    if let Some(s) = symbol_declared_at(file, &ident.byte_range()) {
        // `import opened Lib`: the name is part of the path, so go to the module.
        if s.sym().kind == Kind::Import && parent_kind == "qualified_name" {
            if let Some(m) = resolve_import(st, &s, 0) {
                return vec![Target::Sym(m)];
            }
        }
        return vec![Target::Sym(s)];
    }
    if let Some(l) = declared_local(file, ident) {
        if l.kind == LocalKind::Pattern {
            let ctors = ctor_hits(st, file, ident.start_byte(), name);
            if !ctors.is_empty() {
                return ctors;
            }
        }
        return vec![Target::Local { file: file.clone(), local: l }];
    }

    let Some(parent) = parent else { return Vec::new() };
    let prev = ident.prev_sibling().map(|p| p.kind());
    let next = ident.next_sibling().map(|p| p.kind());
    match parent_kind {
        "suffix_expression" if prev == Some(".") || next == Some(":=") => {
            let Some(recv) = parent.child(0) else { return Vec::new() };
            let val = infer(st, file, effective_receiver(recv), 0);
            let hits = member(st, &val, name);
            if !hits.is_empty() {
                return hits;
            }
            return member_fallback(st, file, name);
        }
        "qualified_name" => {
            let ids: Vec<Node> = named_children(parent).into_iter().filter(|n| n.kind() == "identifier").collect();
            let pos = ids.iter().position(|n| *n == ident).unwrap_or(0);
            let in_import = ancestors(parent).any(|a| a.kind() == "module_import");
            let in_type = in_type_position(ident);
            if pos > 0 {
                let prefix: Vec<&str> = ids[..pos].iter().map(|n| text(*n, src)).collect();
                if let Some(m) = resolve_module_path(st, file, ident.start_byte(), &prefix, in_import, 0) {
                    let hits: Vec<Target> = expand(st, m.children(), false, 0)
                        .into_iter()
                        .filter(|s| s.sym().name == name && (!in_type || s.sym().kind.is_type()))
                        .map(|s| Target::Sym(follow_import(st, s)))
                        .collect();
                    if !hits.is_empty() {
                        return dedup(hits);
                    }
                }
                // `T.member` in export lists and similar places.
                if let Some(t) = resolve_type_name(st, file, ident.start_byte(), &prefix.join(".")) {
                    let hits = member(st, &Val::Static(t), name);
                    if !hits.is_empty() {
                        return hits;
                    }
                }
                return member_fallback(st, file, name);
            }
            if in_import {
                return resolve_module_path(st, file, ident.start_byte(), &[name], true, 0)
                    .map(|m| vec![Target::Sym(m)])
                    .unwrap_or_default();
            }
        }
        "qualified_member_expression" if prev == Some(".") => {
            if let Some(qn) = parent.named_child(0) {
                if let Some(t) = resolve_type_name(st, file, ident.start_byte(), text(qn, src)) {
                    return member(st, &Val::Static(t), name);
                }
            }
            return member_fallback(st, file, name);
        }
        // `new C.Init(...)`
        "rhs" if prev == Some(".") => {
            if let Some(t) = children(parent).into_iter().find(|k| is_type_node(k.kind())) {
                if let Some(t) = resolve_type_name(st, file, ident.start_byte(), text(t, src)) {
                    return member(st, &Val::Static(t), name);
                }
            }
            return member_fallback(st, file, name);
        }
        "constructor_pattern" if ident.prev_named_sibling().is_none() => {
            return ctor_hits(st, file, ident.start_byte(), name);
        }
        "attribute" => return Vec::new(),
        _ => {}
    }
    if in_type_position(ident) && parent_kind == "qualified_name" {
        let hits = lookup_type(st, file, ident.start_byte(), name);
        if !hits.is_empty() {
            return hits;
        }
    }
    // `D.member` where D names a datatype and its constructor.
    let static_access = parent_kind == "name_segment"
        && parent.next_sibling().map(|n| n.kind()) == Some(".")
        && parent.parent().map(|g| g.kind()) == Some("suffix_expression");
    prefer_ctor(lookup(st, file, ident.start_byte(), name), static_access)
}

/// Identifier nodes in the file whose text is `name`.
pub fn identifiers_named<'t>(root: Node<'t>, src: &str, name: &str) -> Vec<Node<'t>> {
    let mut out = Vec::new();
    let mut cursor = root.walk();
    let mut visited_children = false;
    loop {
        let node = cursor.node();
        if !visited_children {
            if node.kind() == "identifier" && text(node, src) == name {
                out.push(node);
            }
            if cursor.goto_first_child() {
                continue;
            }
        }
        if cursor.goto_next_sibling() {
            visited_children = false;
        } else if cursor.goto_parent() {
            visited_children = true;
        } else {
            break;
        }
    }
    out
}

/// Every occurrence of `target` across the workspace.
pub fn references(st: &State, target: &Target, include_decl: bool) -> Vec<(Arc<FileData>, Range<usize>)> {
    let name = target.name();
    let files = match target {
        Target::Local { file, .. } => vec![file.clone()],
        Target::Sym(s) => {
            let mut files = st.all_files();
            if !files.iter().any(|f| f.uri == s.file.uri) {
                files.push(s.file.clone());
            }
            files
        }
    };
    let mut out = Vec::new();
    for f in files {
        if !f.text.contains(name.as_str()) {
            continue;
        }
        for ident in identifiers_named(f.root(), &f.text, &name) {
            if let Target::Local { local, .. } = target {
                if ident.start_byte() < local.scope.start || ident.end_byte() > local.scope.end {
                    continue;
                }
            }
            let is_decl = f.uri == target.file().uri && ident.byte_range() == target.name_range();
            if is_decl {
                if include_decl {
                    out.push((f.clone(), ident.byte_range()));
                }
                continue;
            }
            if resolve_ident(st, &f, ident).iter().any(|t| t.same(target)) {
                out.push((f.clone(), ident.byte_range()));
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use tower_lsp::lsp_types::Url;

    fn state_with(files: &[(&str, &str)]) -> State {
        let st = State::default();
        for (name, src) in files {
            let uri = Url::parse(&format!("file:///ws/{name}")).unwrap();
            st.put_doc(FileData::new(uri, Some(1), src.to_string(), None, None));
        }
        st
    }

    fn doc(st: &State, name: &str) -> Arc<FileData> {
        st.doc(&Url::parse(&format!("file:///ws/{name}")).unwrap()).unwrap()
    }

    /// Resolves the identifier at the n-th occurrence of `needle` and returns
    /// the target's line (0-based) and name.
    fn resolve(st: &State, file: &str, needle: &str, nth: usize) -> Vec<(String, usize, String)> {
        let f = doc(st, file);
        let off = f.text.match_indices(needle).nth(nth).unwrap().0;
        resolve_at(st, &f, off)
            .into_iter()
            .map(|t| {
                let tf = t.file().clone();
                let line = tf.index.line_of(t.name_range().start);
                (tf.uri.path().trim_start_matches("/ws/").to_string(), line, t.name())
            })
            .collect()
    }

    const SRC: &str = r#"module Lib {
  datatype Option<T> = None | Some(value: T)
  function Twice(x: int): int { 2 * x }
}
module App {
  import opened Lib
  import L = Lib
  class Counter {
    var count: nat
    constructor() { count := 0; }
    method Inc() modifies this { count := count + 1; }
  }
  method Main() {
    var c := new Counter();
    c.Inc();
    var o: Option<int> := Some(3);
    var v := o.value;
    var t := L.Twice(v);
    match o {
      case None =>
      case Some(w) => assert w == w;
    }
    var xs := [1, 2];
    assert forall i :: 0 <= i < |xs| ==> xs[i] > 0;
  }
}
"#;

    #[test]
    fn resolves_locals_members_and_modules() {
        let st = state_with(&[("a.dfy", SRC)]);
        // `c` in `c.Inc()` is the local declared on line 13
        assert_eq!(resolve(&st, "a.dfy", "c.Inc", 0), vec![("a.dfy".into(), 13, "c".into())]);
        // `Inc` resolves through the inferred type of `c`
        assert_eq!(resolve(&st, "a.dfy", "Inc();", 0), vec![("a.dfy".into(), 10, "Inc".into())]);
        // `count` inside the class resolves to the field
        assert_eq!(resolve(&st, "a.dfy", "count + 1", 0), vec![("a.dfy".into(), 8, "count".into())]);
        // `Some` comes from the opened import
        assert_eq!(resolve(&st, "a.dfy", "Some(3)", 0), vec![("a.dfy".into(), 1, "Some".into())]);
        // destructor through a declared generic type
        assert_eq!(resolve(&st, "a.dfy", "value;", 0), vec![("a.dfy".into(), 1, "value".into())]);
        // module alias member
        assert_eq!(resolve(&st, "a.dfy", "Twice(v)", 0), vec![("a.dfy".into(), 2, "Twice".into())]);
        // the alias itself goes to the module
        assert_eq!(resolve(&st, "a.dfy", "L.Twice", 0), vec![("a.dfy".into(), 0, "Lib".into())]);
        // `None` in a case pattern is the constructor
        assert_eq!(resolve(&st, "a.dfy", "None =>", 0), vec![("a.dfy".into(), 1, "None".into())]);
        // `w` is bound by the pattern
        assert_eq!(resolve(&st, "a.dfy", "w == w", 0), vec![("a.dfy".into(), 20, "w".into())]);
        // quantifier variable
        assert_eq!(resolve(&st, "a.dfy", "i] > 0", 0), vec![("a.dfy".into(), 23, "i".into())]);
        // `import opened Lib` goes to the module
        assert_eq!(resolve(&st, "a.dfy", "Lib\n", 0), vec![("a.dfy".into(), 0, "Lib".into())]);
        // type name in a declaration
        assert_eq!(resolve(&st, "a.dfy", "Option<int>", 0), vec![("a.dfy".into(), 1, "Option".into())]);
    }

    #[test]
    fn infers_generic_and_pattern_types() {
        let src = r#"module A { datatype V = V(x: int) }
module B {
  datatype V = V(y: int)
  datatype Option<T> = Some(value: T) | None
  function Last<T>(s: seq<T>): T requires |s| > 0 { s[|s| - 1] }
  method M(vs: seq<V>, o: Option<V>) requires |vs| > 0 {
    var a := Last(vs).y;
    var b := vs[0].y;
    var c := o.value.y;
    match o {
      case Some(w) => var d := w.y;
      case None =>
    }
  }
}
"#;
        let st = state_with(&[("g.dfy", src)]);
        for needle in ["y;\n    var b", "y;\n    var c", "y;\n    match", "y;\n      case None"] {
            assert_eq!(resolve(&st, "g.dfy", needle, 0), vec![("g.dfy".into(), 2, "y".into())], "{needle}");
        }
    }

    #[test]
    fn resolves_across_includes() {
        let st = state_with(&[
            ("lib.dfy", "function Twice(x: int): int { 2 * x }\n"),
            ("main.dfy", "include \"lib.dfy\"\nmethod M() { var y := Twice(2); }\n"),
        ]);
        assert_eq!(resolve(&st, "main.dfy", "Twice", 0), vec![("lib.dfy".into(), 0, "Twice".into())]);
    }

    #[test]
    fn finds_references() {
        let st = state_with(&[("a.dfy", SRC)]);
        let f = doc(&st, "a.dfy");
        let off = f.text.find("Inc()").unwrap();
        let target = resolve_at(&st, &f, off).remove(0);
        let refs = references(&st, &target, true);
        let lines: Vec<usize> = refs.iter().map(|(f, r)| f.index.line_of(r.start)).collect();
        assert_eq!(lines, vec![10, 14]);
        let off = f.text.find("var v").unwrap() + 4;
        let target = resolve_at(&st, &f, off).remove(0);
        assert_eq!(references(&st, &target, true).len(), 2);
    }

    #[test]
    fn parses_receiver_chains() {
        assert_eq!(
            chain_before("x := a.b(c, d)[i]", 17),
            vec![Seg::Name("a".into()), Seg::Name("b".into()), Seg::Call, Seg::Index]
        );
        assert_eq!(chain_before("s[1..n]", 7), vec![Seg::Name("s".into()), Seg::Index]);
        assert!(chain_before("3", 1).is_empty());
        assert_eq!(type_args("map<int, seq<T>>"), vec!["int", "seq<T>"]);
    }
}
