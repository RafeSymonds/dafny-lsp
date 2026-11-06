//! Generates random Dafny programs whose types are known, then drives the
//! dafny-lsp binary over stdio the way an editor does: it opens a program, types
//! a probe line one character at a time, and asks for completions. Every answer
//! is compared with the generator's model, and so is go to definition on every
//! field access the program contains.
//!
//! The programs follow the shape of the course labs: several modules, plain,
//! opened and aliased imports, a module that refines an abstract module and
//! uses its imports, datatypes with the same name in different modules, an
//! included library with `Option<T>`, type synonyms and datatype members.
//!
//! Probes are typed in predicate bodies, lemma bodies (`assert`, `var`) and
//! `requires` clauses, as plain member access, inside an open parenthesis, a
//! quantifier or a match case, and inside a datatype update `v.(f := x, g`.
//!
//! Each probe runs in four editor states:
//!   fresh      the file is opened with the probe already typed
//!   typed      the clean file is opened and the probe is typed a character at a time
//!   broken     like typed, after leaving an unfinished line in another body
//!   autoclose  like typed, with `(` inserting `()` as VS Code does
//!
//! The default run is small. For a real search:
//!   GEN_PROGRAMS=500 cargo test --release --test generated   more programs
//!   GEN_SEED=17 cargo test --test generated                  one program
//!   GEN_DAFNY=1 cargo test --test generated                  also `dafny resolve` each program
//!
//! Failing programs are written to target/tmp/generated-failures/.

use std::collections::{BTreeMap, BTreeSet};
use std::io::{BufRead, BufReader, Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Child, ChildStdin, Command, Stdio};
use std::sync::mpsc::{self, Receiver};
use std::time::Duration;

use serde_json::{json, Value};
use tower_lsp::lsp_types::Url;

// ---------------------------------------------------------------------------
// Random numbers

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self {
        Rng((seed.wrapping_add(1)).wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1)
    }

    fn next(&mut self) -> u64 {
        // xorshift64
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }

    fn range(&mut self, lo: usize, hi: usize) -> usize {
        lo + self.below(hi - lo + 1)
    }

    fn chance(&mut self, percent: u64) -> bool {
        self.next() % 100 < percent
    }

    fn pick<'a, T>(&mut self, xs: &'a [T]) -> &'a T {
        &xs[self.below(xs.len())]
    }

    /// `n` distinct names from `pool` that are not in `taken`.
    fn names(&mut self, pool: &[&str], n: usize, taken: &BTreeSet<String>) -> Vec<String> {
        let mut free: Vec<&str> = pool.iter().copied().filter(|p| !taken.contains(*p)).collect();
        let mut out = Vec::new();
        while out.len() < n && !free.is_empty() {
            out.push(free.remove(self.below(free.len())).to_string());
        }
        out
    }
}

// ---------------------------------------------------------------------------
// The program model

const MODULES: &[&str] = &["Events", "Types", "Primary", "Backup", "Network", "Host", "Spec", "Proto"];
const DATATYPES: &[&str] = &["Variables", "Constants", "Message", "State", "Step", "Config", "Event", "Ballot"];
const CTORS: &[&str] = &["Init", "Run", "Done", "Req", "Resp", "Ack", "Update", "Idle", "Busy", "Leaf", "Node", "Write", "Read"];
const FIELDS: &[&str] = &[
    "value", "backup", "primary", "pending", "network", "count", "items", "next", "isAlive", "isPrimary", "inFlight", "left",
    "right", "owner", "epoch", "ballot", "votes", "leader", "recv", "send",
];
const METHODS: &[&str] = &["Get", "Size", "IsOk", "Sum"];
const ALIASES: &[&str] = &["Vars", "Consts", "Msg", "St"];
const PREDICATES: &[&str] = &["Inv", "Valid", "Safe", "Wf", "Holds", "Check"];
const LEMMAS: &[&str] = &["Lem", "Helper", "Prove", "Advance"];
const PARAMS: &[&str] = &["v", "s", "w", "h", "v'"];
const MODULE_ALIASES: &[&str] = &["P", "B", "N", "Q"];

/// The included library. `Order` is there so that its fields show up if the
/// server falls back to suggesting members of every type.
const LIB: &str = "module Lib {\n  datatype Option<T> = Some(value: T) | None\n  datatype Order = Sandwich(meat: int, cheese: int) | Pizza(meat: int, veggie: int)\n}\n";
const LIB_MODULE: usize = 0;

#[derive(Clone, Debug, PartialEq)]
enum Ty {
    Int,
    Bool,
    Seq,
    Data(usize),
    Opt(Box<Ty>),
    Alias(usize),
    Set(Box<Ty>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum File {
    Main,
    Lib,
}

/// A declaration site: file, line, column.
type Decl = (File, usize, usize);

struct Field {
    name: String,
    ty: Ty,
    decls: Vec<Decl>,
}

struct Datatype {
    module: usize,
    name: String,
    ctors: Vec<String>,
    fields: Vec<Field>,
    /// Indexes into `fields` for each constructor, in parameter order.
    layout: Vec<Vec<usize>>,
    methods: Vec<String>,
}

struct Alias {
    module: usize,
    name: String,
    target: usize,
}

struct Import {
    module: usize,
    opened: bool,
    alias: Option<String>,
}

struct Module {
    name: String,
    imports: Vec<Import>,
    refines: Option<usize>,
    /// Every name the module declares, fixed before any type is written so that
    /// a bare name never picks up a declaration that comes later.
    names: BTreeSet<String>,
}

/// Where a probe line goes, which decides how the line starts.
#[derive(Clone, Copy, Debug, PartialEq)]
enum Site {
    /// A conjunct in a predicate body.
    Expr,
    /// A statement in a lemma body.
    Stmt,
    /// A `requires` clause.
    Requires,
}

impl Site {
    fn prefix(self) -> &'static str {
        match self {
            Site::Expr => "    && ",
            Site::Stmt => "    assert ",
            Site::Requires => "    requires ",
        }
    }
}

struct Probe {
    /// The probe is typed on a new line after this one.
    anchor: usize,
    typed: String,
    expected: BTreeSet<String>,
    context: String,
    place: String,
}

struct DefCheck {
    line: usize,
    col: usize,
    name: String,
    expected: Vec<Decl>,
}

struct Program {
    seed: u64,
    text: String,
    probes: Vec<Probe>,
    defs: Vec<DefCheck>,
    /// Lines that probes and breakage go after.
    anchors: Vec<(usize, Site)>,
}

struct Gen {
    rng: Rng,
    modules: Vec<Module>,
    datatypes: Vec<Datatype>,
    aliases: Vec<Alias>,
    out: String,
    probes: Vec<Probe>,
    defs: Vec<DefCheck>,
    anchors: Vec<(usize, Site)>,
    option_value: Decl,
}

impl Gen {
    fn new(seed: u64) -> Self {
        let mut g = Gen {
            rng: Rng::new(seed),
            modules: Vec::new(),
            datatypes: Vec::new(),
            aliases: Vec::new(),
            out: String::new(),
            probes: Vec::new(),
            defs: Vec::new(),
            anchors: Vec::new(),
            option_value: lib_decl("Some", "value"),
        };
        let names = ["Option", "Some", "None", "Order", "Sandwich", "Pizza"].iter().map(|s| s.to_string()).collect();
        g.modules.push(Module { name: "Lib".into(), imports: Vec::new(), refines: None, names });
        let field = |name: &str, ctors: &[&str]| Field {
            name: name.into(),
            ty: Ty::Int,
            decls: ctors.iter().map(|c| lib_decl(c, name)).collect(),
        };
        g.datatypes.push(Datatype {
            module: LIB_MODULE,
            name: "Order".into(),
            ctors: vec!["Sandwich".into(), "Pizza".into()],
            fields: vec![field("meat", &["Sandwich", "Pizza"]), field("cheese", &["Sandwich"]), field("veggie", &["Pizza"])],
            layout: vec![vec![0, 1], vec![0, 2]],
            methods: Vec::new(),
        });
        g
    }

    fn pos(&self) -> (usize, usize) {
        let line = self.out.matches('\n').count();
        let col = self.out.len() - self.out.rfind('\n').map_or(0, |i| i + 1);
        (line, col)
    }

    fn w(&mut self, s: &str) {
        self.out.push_str(s);
    }

    // --- visibility and names ---

    /// Imports in effect in `m`, including those of the module it refines.
    fn imports_of(&self, m: usize) -> Vec<&Import> {
        let mut out: Vec<&Import> = self.modules[m].imports.iter().collect();
        if let Some(p) = self.modules[m].refines {
            out.extend(self.modules[p].imports.iter());
        }
        out
    }

    fn visible(&self, m: usize, target: usize) -> bool {
        target == m || self.imports_of(m).iter().any(|i| i.module == target)
    }

    /// How module `m` writes the name `name` declared in module `target`.
    fn name_ref(&self, m: usize, target: usize, name: &str) -> String {
        if target == m {
            return name.to_string();
        }
        let imports = self.imports_of(m);
        let imp = imports.iter().find(|i| i.module == target).expect("type from a module that is not imported");
        let clash = self.modules[m].names.contains(name)
            || imports.iter().any(|i| i.opened && i.module != target && self.modules[i.module].names.contains(name));
        if imp.opened && !clash {
            name.to_string()
        } else {
            format!("{}.{}", imp.alias.clone().unwrap_or_else(|| self.modules[target].name.clone()), name)
        }
    }

    fn ty_text(&self, m: usize, ty: &Ty) -> String {
        match ty {
            Ty::Int => "int".into(),
            Ty::Bool => "bool".into(),
            Ty::Seq => "seq<int>".into(),
            Ty::Data(d) => self.name_ref(m, self.datatypes[*d].module, &self.datatypes[*d].name),
            Ty::Alias(a) => self.name_ref(m, self.aliases[*a].module, &self.aliases[*a].name),
            Ty::Opt(t) => format!("{}<{}>", self.name_ref(m, LIB_MODULE, "Option"), self.ty_text(m, t)),
            Ty::Set(t) => format!("set<{}>", self.ty_text(m, t)),
        }
    }

    // --- type queries ---

    fn data_of(&self, ty: &Ty) -> Option<usize> {
        match ty {
            Ty::Data(d) => Some(*d),
            Ty::Alias(a) => Some(self.aliases[*a].target),
            _ => None,
        }
    }

    fn has_members(&self, ty: &Ty) -> bool {
        matches!(ty, Ty::Data(_) | Ty::Alias(_) | Ty::Opt(_))
    }

    /// What `x.` should offer for a value of this type.
    fn members(&self, ty: &Ty) -> BTreeSet<String> {
        if let Ty::Opt(_) = ty {
            return ["value", "Some?", "None?"].iter().map(|s| s.to_string()).collect();
        }
        let dt = &self.datatypes[self.data_of(ty).unwrap()];
        let mut out: BTreeSet<String> = dt.fields.iter().map(|f| f.name.clone()).collect();
        out.extend(dt.methods.iter().cloned());
        out.extend(dt.ctors.iter().map(|c| format!("{c}?")));
        out
    }

    /// What `x.(` should offer.
    fn fields(&self, ty: &Ty) -> Vec<String> {
        match ty {
            Ty::Opt(_) => vec!["value".into()],
            _ => self.datatypes[self.data_of(ty).unwrap()].fields.iter().map(|f| f.name.clone()).collect(),
        }
    }

    fn field(&self, ty: &Ty, name: &str) -> (Ty, Vec<Decl>) {
        match ty {
            Ty::Opt(t) => ((**t).clone(), vec![self.option_value]),
            _ => {
                let f = self.datatypes[self.data_of(ty).unwrap()].fields.iter().find(|f| f.name == name).unwrap();
                (f.ty.clone(), f.decls.clone())
            }
        }
    }

    // --- choosing types ---

    fn visible_types(&self, m: usize, upto: usize) -> Vec<Ty> {
        let mut out = Vec::new();
        for (d, dt) in self.datatypes.iter().enumerate().take(upto) {
            if self.visible(m, dt.module) {
                out.push(Ty::Data(d));
            }
        }
        for (a, al) in self.aliases.iter().enumerate() {
            if self.visible(m, al.module) {
                out.push(Ty::Alias(a));
            }
        }
        out
    }

    fn field_ty(&mut self, m: usize) -> Ty {
        let named = self.visible_types(m, self.datatypes.len());
        let roll = self.rng.below(100);
        if roll < 25 || named.is_empty() {
            self.rng.pick(&[Ty::Int, Ty::Bool, Ty::Seq]).clone()
        } else if roll < 60 {
            self.rng.pick(&named).clone()
        } else if roll < 72 {
            Ty::Set(Box::new(self.rng.pick(&named).clone()))
        } else if self.rng.chance(80) {
            Ty::Opt(Box::new(self.rng.pick(&named).clone()))
        } else {
            Ty::Opt(Box::new(Ty::Int))
        }
    }

    fn param_ty(&mut self, m: usize) -> Ty {
        let named = self.visible_types(m, self.datatypes.len());
        let t = self.rng.pick(&named).clone();
        if self.rng.chance(15) {
            Ty::Opt(Box::new(t))
        } else {
            t
        }
    }

    // --- writing ---

    fn module_header(&mut self, m: usize) {
        let header = match self.modules[m].refines {
            Some(p) => format!("module {} refines {} {{\n", self.modules[m].name, self.modules[p].name),
            None => format!("module {} {{\n", self.modules[m].name),
        };
        self.w(&header);
        for i in 0..self.modules[m].imports.len() {
            let imp = &self.modules[m].imports[i];
            let target = self.modules[imp.module].name.clone();
            let line = match (&imp.alias, imp.opened) {
                (Some(a), true) => format!("  import opened {a} = {target}\n"),
                (Some(a), false) => format!("  import {a} = {target}\n"),
                (None, true) => format!("  import opened {target}\n"),
                (None, false) => format!("  import {target}\n"),
            };
            self.w(&line);
        }
        self.w("\n");
    }

    /// Imports for a new module: always the library, and some earlier modules.
    fn pick_imports(&mut self, upto: usize, want: usize) -> Vec<Import> {
        let mut imports = vec![Import { module: LIB_MODULE, opened: self.rng.chance(60), alias: None }];
        let mut aliases = self.rng.names(MODULE_ALIASES, MODULE_ALIASES.len(), &BTreeSet::new());
        let mut candidates: Vec<usize> = (1..upto).collect();
        while imports.len() <= want && !candidates.is_empty() {
            let module = candidates.remove(self.rng.below(candidates.len()));
            let roll = self.rng.below(100);
            let (opened, alias) = if roll < 40 {
                (true, None)
            } else if roll < 60 {
                (false, aliases.pop())
            } else {
                (false, None)
            };
            imports.push(Import { module, opened, alias });
        }
        imports
    }

    fn datatype(&mut self, m: usize, name: String, ctors: Vec<String>) {
        let taken = BTreeSet::new();
        let n_fields = self.rng.range(1, 4);
        let field_names = self.rng.names(FIELDS, n_fields, &taken);
        let mut fields: Vec<Field> = Vec::new();
        for f in field_names {
            let ty = self.field_ty(m);
            fields.push(Field { name: f, ty, decls: Vec::new() });
        }
        // Every field belongs to at least one constructor. Shared fields have one type.
        let mut layout: Vec<Vec<usize>> = vec![Vec::new(); ctors.len()];
        for f in 0..fields.len() {
            let home = self.rng.below(ctors.len());
            for (c, l) in layout.iter_mut().enumerate() {
                if c == home || self.rng.chance(30) {
                    l.push(f);
                }
            }
        }
        let methods = if self.rng.chance(40) { self.rng.names(METHODS, 1, &taken) } else { Vec::new() };

        self.w(&format!("  datatype {name} ="));
        for (c, ctor) in ctors.iter().enumerate() {
            self.w(if c == 0 { " " } else { " | " });
            self.w(ctor);
            if layout[c].is_empty() {
                continue;
            }
            self.w("(");
            for (k, &f) in layout[c].iter().enumerate() {
                if k > 0 {
                    self.w(", ");
                }
                let (line, col) = self.pos();
                fields[f].decls.push((File::Main, line, col));
                let text = format!("{}: {}", fields[f].name, self.ty_text(m, &fields[f].ty));
                self.w(&text);
            }
            self.w(")");
        }
        if methods.is_empty() {
            self.w("\n");
        } else {
            self.w(" {\n");
            for meth in &methods {
                let body = if meth == "IsOk" { format!("    ghost predicate {meth}() {{ true }}\n") } else { format!("    function {meth}(): int {{ 0 }}\n") };
                self.w(&body);
            }
            self.w("  }\n");
        }
        self.datatypes.push(Datatype { module: m, name, ctors, fields, layout, methods });
    }

    /// A random chain of field accesses from `start`, as (text, type, [(field, decls)]).
    fn walk(&mut self, start: &str, ty: &Ty, max: usize) -> Vec<(String, Ty)> {
        let mut out = vec![(start.to_string(), ty.clone())];
        let (mut text, mut ty) = (start.to_string(), ty.clone());
        for _ in 0..max {
            if !self.has_members(&ty) {
                break;
            }
            let fields = self.fields(&ty);
            let f = self.rng.pick(&fields).clone();
            text = format!("{text}.{f}");
            ty = self.field(&ty, &f).0;
            out.push((text.clone(), ty.clone()));
        }
        out
    }

    /// Writes `    && e == e` for a field chain and records definition checks for the left copy.
    fn access_line(&mut self, root: &str, root_ty: &Ty) {
        let depth = self.rng.range(1, 3);
        let chain = self.walk(root, root_ty, depth);
        if chain.len() < 2 {
            return;
        }
        let full = chain.last().unwrap().0.clone();
        self.w("    && ");
        self.w(root);
        for k in 1..chain.len() {
            let name = chain[k].0.rsplit('.').next().unwrap().to_string();
            self.w(".");
            let (line, col) = self.pos();
            let expected = self.field(&chain[k - 1].1, &name).1;
            self.defs.push(DefCheck { line, col, name: name.clone(), expected });
            self.w(&name);
        }
        self.w(&format!(" == {full}\n"));
    }

    /// `var x0 := v.f;` when the first parameter has a field chain to bind.
    /// The local's type comes only from its initializer.
    fn let_local(&mut self, params: &[(String, Ty)], end: &str) -> Option<(String, Ty)> {
        let (p, pty) = params[0].clone();
        if !self.rng.chance(50) || !self.has_members(&pty) {
            return None;
        }
        let chain = self.walk(&p, &pty, 2);
        let (init, ty) = chain.last().unwrap().clone();
        if !self.has_members(&ty) {
            return None;
        }
        self.w(&format!("    var x0 := {init}{end}\n"));
        Some(("x0".into(), ty))
    }

    fn predicate(&mut self, m: usize, name: &str, params: &[(String, Ty)], sig: &str) {
        self.w(&format!("  ghost predicate {name}({sig})\n  {{\n"));
        let mut roots: Vec<(String, Ty)> = params.to_vec();
        roots.extend(self.let_local(params, ";"));
        let anchor = self.pos().0;
        self.anchors.push((anchor, Site::Expr));
        self.w("    true\n");
        for _ in 0..self.rng.range(1, 3) {
            let (r, t) = self.rng.pick(&roots).clone();
            self.access_line(&r, &t);
        }
        self.w("  }\n\n");
        let place = format!("{}.{}", self.modules[m].name, name);
        self.add_probes(&place, anchor, Site::Expr, &roots);
    }

    /// A lemma whose `requires` clause and body take probes. A lemma in a
    /// refining module only adds a body, as Dafny allows.
    fn lemma(&mut self, m: usize, name: &str, params: &[(String, Ty)], sig: &str, requires: bool) {
        self.w(&format!("  lemma {name}({sig})\n"));
        let place = format!("{}.{}", self.modules[m].name, name);
        if requires {
            let anchor = self.pos().0;
            self.anchors.push((anchor, Site::Requires));
            self.w("    requires true\n");
            self.add_probes(&place, anchor, Site::Requires, params);
        }
        self.w("  {\n");
        let mut roots: Vec<(String, Ty)> = params.to_vec();
        roots.extend(self.let_local(params, ";"));
        let anchor = self.pos().0;
        self.anchors.push((anchor, Site::Stmt));
        self.w("    assert true;\n  }\n\n");
        self.add_probes(&place, anchor, Site::Stmt, &roots);
    }

    /// Probes on receivers reachable from `roots`.
    fn add_probes(&mut self, place: &str, anchor: usize, site: Site, roots: &[(String, Ty)]) {
        let mut receivers: Vec<(String, Ty)> = Vec::new();
        for (r, t) in roots {
            for (text, ty) in self.walk(r, t, 3) {
                if self.has_members(&ty) && !receivers.iter().any(|(x, _)| *x == text) {
                    receivers.push((text, ty));
                }
            }
        }
        for _ in 0..3.min(receivers.len()) {
            let (r, ty) = receivers.remove(self.rng.below(receivers.len()));
            let mut probes = self.probes_for(&r, &ty, site);
            for _ in 0..2.min(probes.len()) {
                let (context, typed, expected) = probes.remove(self.rng.below(probes.len()));
                let context = format!("{context} @{site:?}");
                self.probes.push(Probe { anchor, typed, expected, context, place: place.to_string() });
            }
        }
    }

    fn probes_for(&mut self, r: &str, ty: &Ty, site: Site) -> Vec<(&'static str, String, BTreeSet<String>)> {
        let pre = site.prefix();
        let mut out = vec![
            ("member", format!("{pre}{r}."), self.members(ty)),
            ("member in open paren", format!("{pre}({r} == {r} ==> {r}."), self.members(ty)),
            ("member in forall", format!("{pre}forall k: int :: {r}."), self.members(ty)),
        ];
        if site == Site::Stmt {
            out.push(("var initializer", format!("    var t := {r}."), self.members(ty)));
        }
        // `match r case C(b0, b1) => b1.`: the binder's type comes from the constructor.
        let case = match ty {
            Ty::Opt(t) if self.has_members(t) => Some(("Some".to_string(), vec!["b0".to_string()], 0, (**t).clone())),
            Ty::Opt(_) => None,
            _ => {
                let dt = &self.datatypes[self.data_of(ty).unwrap()];
                let options: Vec<(usize, usize)> = (0..dt.ctors.len())
                    .flat_map(|c| (0..dt.layout[c].len()).map(move |k| (c, k)))
                    .filter(|&(c, k)| self.has_members(&dt.fields[dt.layout[c][k]].ty))
                    .collect();
                (!options.is_empty()).then(|| {
                    let (c, k) = options[self.rng.below(options.len())];
                    let dt = &self.datatypes[self.data_of(ty).unwrap()];
                    let binders = (0..dt.layout[c].len()).map(|i| format!("b{i}")).collect();
                    (dt.ctors[c].clone(), binders, k, dt.fields[dt.layout[c][k]].ty.clone())
                })
            }
        };
        if let Some((ctor, binders, k, bty)) = case {
            out.push(("match binder", format!("{pre}match {r} case {ctor}({}) => b{k}.", binders.join(", ")), self.members(&bty)));
        }
        let fields = self.fields(ty);
        // `forall b | b in r.f :: b.`: an untyped bound variable gets the set's element type.
        let sets: Vec<(String, Ty)> = fields
            .iter()
            .filter_map(|f| match self.field(ty, f).0 {
                Ty::Set(t) if self.has_members(&t) => Some((f.clone(), *t)),
                _ => None,
            })
            .collect();
        if !sets.is_empty() {
            let (f, elem) = self.rng.pick(&sets).clone();
            out.push(("forall binder in range", format!("{pre}forall b0 | b0 in {r}.{f} :: b0."), self.members(&elem)));
            out.push(("forall binder <-", format!("{pre}forall b0 <- {r}.{f} :: b0."), self.members(&elem)));
        }
        out.push(("update", format!("{pre}{r} == {r}.("), fields.iter().cloned().collect()));
        let f = self.rng.pick(&fields).clone();
        let rest: BTreeSet<String> = fields.iter().filter(|x| **x != f).cloned().collect();
        if let Some(next) = rest.iter().next().cloned() {
            out.push(("update after comma", format!("{pre}{r} == {r}.({f} := {r}.{f},"), rest.clone()));
            let first = &next[..1];
            out.push(("update next name", format!("{pre}{r} == {r}.({f} := {r}.{f}, {first}"), rest));
        }
        let (fty, _) = self.field(ty, &f);
        if self.has_members(&fty) {
            out.push(("member in update value", format!("{pre}{r} == {r}.({f} := {r}.{f}."), self.members(&fty)));
        }
        out
    }

    fn generate(mut self, seed: u64) -> Program {
        self.w("include \"lib.dfy\"\n\n");
        let n = self.rng.range(2, 4);
        let module_names = self.rng.names(MODULES, n, &BTreeSet::new());
        for name in module_names {
            let m = self.modules.len();
            let want = self.rng.range(0, 2);
            let imports = self.pick_imports(m, want);
            // Fix every module-level name first.
            let mut names = BTreeSet::new();
            let n_dt = self.rng.range(1, 3);
            let dt_names = self.rng.names(DATATYPES, n_dt, &names);
            names.extend(dt_names.iter().cloned());
            let mut ctor_names = Vec::new();
            for dt in &dt_names {
                let k = self.rng.range(1, 3);
                let ctors = if k == 1 && self.rng.chance(50) { vec![dt.clone()] } else { self.rng.names(CTORS, k, &names) };
                names.extend(ctors.iter().cloned());
                ctor_names.push(ctors);
            }
            let alias_name = if self.rng.chance(40) { self.rng.names(ALIASES, 1, &names).pop() } else { None };
            names.extend(alias_name.iter().cloned());
            let n_preds = self.rng.range(1, 2);
            let preds = self.rng.names(PREDICATES, n_preds, &names);
            names.extend(preds.iter().cloned());
            let lemma = if self.rng.chance(60) { self.rng.names(LEMMAS, 1, &names).pop() } else { None };
            names.extend(lemma.iter().cloned());
            self.modules.push(Module { name, imports, refines: None, names });

            self.module_header(m);
            for (dt, ctors) in dt_names.into_iter().zip(ctor_names) {
                self.datatype(m, dt, ctors);
            }
            if let Some(alias) = alias_name {
                // Only datatypes: an imported alias may name a type from a module `m` cannot see.
                let targets: Vec<usize> = (0..self.datatypes.len()).filter(|d| self.visible(m, self.datatypes[*d].module)).collect();
                let target = *self.rng.pick(&targets);
                let text = self.ty_text(m, &Ty::Data(target));
                self.w(&format!("  type {alias} = {text}\n"));
                self.aliases.push(Alias { module: m, name: alias, target });
            }
            self.w("\n");
            for p in preds {
                let params = self.params(m);
                let sig = params.iter().map(|(n, t)| format!("{n}: {}", self.ty_text(m, t))).collect::<Vec<_>>().join(", ");
                self.predicate(m, &p, &params, &sig);
            }
            if let Some(l) = lemma {
                let params = self.params(m);
                let sig = params.iter().map(|(n, t)| format!("{n}: {}", self.ty_text(m, t))).collect::<Vec<_>>().join(", ");
                self.lemma(m, &l, &params, &sig, true);
            }
            self.w("}\n\n");
        }

        // An abstract module and a module refining it that uses its imports,
        // like RefinementTheorem and RefinementProof in the labs.
        if self.rng.chance(60) {
            let theorem = self.modules.len();
            let want = self.rng.range(1, 2);
            let imports = self.pick_imports(theorem, want);
            let pred = self.rng.pick(PREDICATES).to_string();
            let lemma = self.rng.pick(LEMMAS).to_string();
            let names: BTreeSet<String> = [pred.clone(), lemma.clone()].into_iter().collect();
            self.modules.push(Module { name: "Theorem".into(), imports, refines: None, names: names.clone() });
            if self.visible_types(theorem, self.datatypes.len()).is_empty() {
                self.modules.pop();
            } else {
                let params = self.params(theorem);
                let sig = params.iter().map(|(n, t)| format!("{n}: {}", self.ty_text(theorem, t))).collect::<Vec<_>>().join(", ");
                self.w("abstract ");
                self.module_header(theorem);
                let args = params.iter().map(|(n, _)| n.clone()).collect::<Vec<_>>().join(", ");
                self.w(&format!("  ghost predicate {pred}({sig})\n\n  lemma {lemma}({sig})\n    requires {pred}({args})\n}}\n\n"));

                let proof = self.modules.len();
                // Its own imports, of modules the abstract module does not import. Not
                // opened: that could make a bare name in the inherited signature ambiguous.
                let own: Vec<Import> = if self.rng.chance(50) {
                    let picked = self.pick_imports(theorem, 1);
                    let inherited = &self.modules[theorem].imports;
                    let fresh = |i: &Import| {
                        !inherited.iter().any(|j| j.module == i.module || (j.alias.is_some() && j.alias == i.alias))
                    };
                    picked.into_iter().skip(1).filter(|i| fresh(i)).map(|i| Import { opened: false, ..i }).collect()
                } else {
                    Vec::new()
                };
                self.modules.push(Module { name: "Proof".into(), imports: own, refines: Some(theorem), names });
                self.module_header(proof);
                self.predicate(proof, &pred, &params, &sig);
                self.lemma(proof, &lemma, &params, &sig, false);
                self.w("}\n");
            }
        }
        Program { seed, text: self.out, probes: self.probes, defs: self.defs, anchors: self.anchors }
    }

    fn params(&mut self, m: usize) -> Vec<(String, Ty)> {
        let n = self.rng.range(1, 2);
        let names = self.rng.names(PARAMS, n, &BTreeSet::new());
        names.into_iter().map(|p| (p, self.param_ty(m))).collect()
    }
}

/// Position of the field `field` in the constructor `ctor` of the library.
fn lib_decl(ctor: &str, field: &str) -> Decl {
    for (line, text) in LIB.lines().enumerate() {
        if let Some(c) = text.find(&format!("{ctor}(")) {
            let col = c + text[c..].find(&format!("{field}:")).unwrap();
            return (File::Lib, line, col);
        }
    }
    panic!("no {ctor}.{field} in the library");
}

// ---------------------------------------------------------------------------
// A minimal LSP client

struct Lsp {
    child: Child,
    stdin: ChildStdin,
    rx: Receiver<Value>,
    next_id: i64,
}

impl Lsp {
    fn start(root: &Path) -> Lsp {
        let mut child = Command::new(env!("CARGO_BIN_EXE_dafny-lsp"))
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()
            .expect("start dafny-lsp");
        let stdout = child.stdout.take().unwrap();
        let stdin = child.stdin.take().unwrap();
        let (tx, rx) = mpsc::channel();
        std::thread::spawn(move || {
            let mut r = BufReader::new(stdout);
            loop {
                let mut len = 0;
                loop {
                    let mut line = String::new();
                    if r.read_line(&mut line).unwrap_or(0) == 0 {
                        return;
                    }
                    let line = line.trim_end();
                    if line.is_empty() {
                        break;
                    }
                    if let Some(v) = line.strip_prefix("Content-Length:") {
                        len = v.trim().parse().unwrap();
                    }
                }
                let mut body = vec![0; len];
                if r.read_exact(&mut body).is_err() {
                    return;
                }
                if tx.send(serde_json::from_slice(&body).unwrap()).is_err() {
                    return;
                }
            }
        });
        let mut lsp = Lsp { child, stdin, rx, next_id: 0 };
        let root_uri = Url::from_file_path(root).unwrap();
        lsp.request(
            "initialize",
            json!({"rootUri": root_uri, "capabilities": {}, "initializationOptions": {"diagnostics": false, "verifyOn": "never"}}),
        );
        lsp.notify("initialized", json!({}));
        lsp
    }

    fn send(&mut self, msg: Value) {
        let body = serde_json::to_vec(&msg).unwrap();
        write!(self.stdin, "Content-Length: {}\r\n\r\n", body.len()).unwrap();
        self.stdin.write_all(&body).unwrap();
        self.stdin.flush().unwrap();
    }

    fn notify(&mut self, method: &str, params: Value) {
        self.send(json!({"jsonrpc": "2.0", "method": method, "params": params}));
    }

    fn request(&mut self, method: &str, params: Value) -> Value {
        self.next_id += 1;
        let id = self.next_id;
        self.send(json!({"jsonrpc": "2.0", "id": id, "method": method, "params": params}));
        loop {
            let msg = self.rx.recv_timeout(Duration::from_secs(30)).unwrap_or_else(|_| panic!("no answer to {method}"));
            match (msg.get("id"), msg.get("method")) {
                (Some(i), None) if *i == json!(id) => return msg["result"].clone(),
                // A request from the server, such as workDoneProgress/create.
                (Some(i), Some(_)) => {
                    let i = i.clone();
                    self.send(json!({"jsonrpc": "2.0", "id": i, "result": null}));
                }
                _ => {}
            }
        }
    }
}

impl Drop for Lsp {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

/// One open document, with the edits an editor would send.
struct Doc<'a> {
    lsp: &'a mut Lsp,
    uri: Url,
    lines: Vec<String>,
    version: i32,
}

impl<'a> Doc<'a> {
    fn open(lsp: &'a mut Lsp, uri: &Url, text: &str) -> Doc<'a> {
        lsp.notify("textDocument/didOpen", json!({"textDocument": {"uri": uri, "languageId": "dafny", "version": 1, "text": text}}));
        Doc { lsp, uri: uri.clone(), lines: text.split('\n').map(String::from).collect(), version: 1 }
    }

    fn insert(&mut self, line: usize, col: usize, text: &str) {
        self.version += 1;
        let pos = json!({"line": line, "character": col});
        self.lsp.notify(
            "textDocument/didChange",
            json!({"textDocument": {"uri": self.uri, "version": self.version}, "contentChanges": [{"range": {"start": pos, "end": pos}, "text": text}]}),
        );
        let rest = self.lines[line].split_off(col);
        let mut new: Vec<String> = text.split('\n').map(String::from).collect();
        new[0] = format!("{}{}", self.lines[line], new[0]);
        new.last_mut().unwrap().push_str(&rest);
        self.lines.splice(line..=line, new);
    }

    /// Opens a new line after `line` and types `text` into it a character at a
    /// time. With `autoclose`, an opening bracket also inserts its closer after
    /// the cursor, and typing that closer steps over it, as VS Code does.
    /// Returns the cursor column.
    fn type_line(&mut self, line: usize, text: &str, autoclose: bool) -> usize {
        let end = self.lines[line].len();
        self.insert(line, end, "\n");
        let row = line + 1;
        let mut col = 0;
        for c in text.chars() {
            let next = self.lines[row][col..].chars().next();
            if autoclose && ")]}".contains(c) && next == Some(c) {
                col += 1;
                continue;
            }
            let insert = match (autoclose, c) {
                (true, '(') => "()".to_string(),
                (true, '[') => "[]".to_string(),
                (true, '{') => "{}".to_string(),
                _ => c.to_string(),
            };
            self.insert(row, col, &insert);
            col += c.len_utf8();
        }
        col
    }

    fn complete(&mut self, line: usize, col: usize, last: char) -> Option<BTreeSet<String>> {
        let context = if ".(,".contains(last) { json!({"triggerKind": 2, "triggerCharacter": last.to_string()}) } else { json!({"triggerKind": 1}) };
        let r = self.lsp.request(
            "textDocument/completion",
            json!({"textDocument": {"uri": self.uri}, "position": {"line": line, "character": col}, "context": context}),
        );
        let items = if r.is_array() { r } else { r.get("items")?.clone() };
        Some(items.as_array()?.iter().map(|i| i["label"].as_str().unwrap().to_string()).collect())
    }

    fn definition(&mut self, line: usize, col: usize, lib: &Url) -> Vec<Decl> {
        let r = self.lsp.request(
            "textDocument/definition",
            json!({"textDocument": {"uri": self.uri}, "position": {"line": line, "character": col}}),
        );
        let locs = match r {
            Value::Array(a) => a,
            Value::Null => Vec::new(),
            one => vec![one],
        };
        locs.iter()
            .map(|l| {
                let uri = l.get("uri").or_else(|| l.get("targetUri")).unwrap();
                let range = l.get("range").or_else(|| l.get("targetSelectionRange")).unwrap();
                let file = if *uri == json!(lib) { File::Lib } else { File::Main };
                (file, range["start"]["line"].as_u64().unwrap() as usize, range["start"]["character"].as_u64().unwrap() as usize)
            })
            .collect()
    }

    fn close(self) {
        self.lsp.notify("textDocument/didClose", json!({"textDocument": {"uri": self.uri}}));
    }
}

// ---------------------------------------------------------------------------
// Running the checks

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Scenario {
    Fresh,
    Typed,
    Broken,
    Autoclose,
}

const SCENARIOS: [Scenario; 4] = [Scenario::Fresh, Scenario::Typed, Scenario::Broken, Scenario::Autoclose];

struct Failure {
    seed: u64,
    what: String,
}

fn show(s: &BTreeSet<String>) -> String {
    format!("[{}]", s.iter().cloned().collect::<Vec<_>>().join(", "))
}

fn run_probe(lsp: &mut Lsp, uri: &Url, prog: &Program, probe: &Probe, scenario: Scenario, rng: &mut Rng) -> Option<String> {
    let last = probe.typed.chars().last().unwrap();
    let mut note = String::new();
    let got = if scenario == Scenario::Fresh {
        let mut lines: Vec<&str> = prog.text.split('\n').collect();
        lines.insert(probe.anchor + 1, &probe.typed);
        let mut doc = Doc::open(lsp, uri, &lines.join("\n"));
        let got = doc.complete(probe.anchor + 1, probe.typed.len(), last);
        doc.close();
        got
    } else {
        let mut doc = Doc::open(lsp, uri, &prog.text);
        let mut anchor = probe.anchor;
        if scenario == Scenario::Broken {
            let others: Vec<(usize, Site)> = prog.anchors.iter().copied().filter(|a| a.0 != probe.anchor).collect();
            if others.is_empty() {
                doc.close();
                return None;
            }
            let (other, site) = *rng.pick(&others);
            doc.type_line(other, site.prefix(), false);
            note = format!(" (with `{}` left after line {})", site.prefix().trim(), other + 1);
            if other < anchor {
                anchor += 1;
            }
        }
        let col = doc.type_line(anchor, &probe.typed, scenario == Scenario::Autoclose);
        let got = doc.complete(anchor + 1, col, last);
        doc.close();
        got
    };
    let got = got.unwrap_or_default();
    if got == probe.expected {
        return None;
    }
    let missing: BTreeSet<String> = probe.expected.difference(&got).cloned().collect();
    let extra: BTreeSet<String> = got.difference(&probe.expected).cloned().collect();
    let extra_text = if extra.len() > 12 { format!("{} items", extra.len()) } else { show(&extra) };
    Some(format!(
        "{:?} {} in {} after line {}: `{}`{}\n      want {}\n      missing {} extra {}",
        scenario,
        probe.context,
        probe.place,
        probe.anchor + 1,
        probe.typed.trim(),
        note,
        show(&probe.expected),
        show(&missing),
        extra_text
    ))
}

fn dafny_resolve(dir: &Path, prog: &Program) -> Option<String> {
    let path = dir.join(format!("p{}.dfy", prog.seed));
    std::fs::write(&path, &prog.text).unwrap();
    let out = Command::new("dafny").arg("resolve").arg("--use-basename-for-filename").arg(&path).output().ok()?;
    if out.status.success() {
        let _ = std::fs::remove_file(&path);
        None
    } else {
        Some(String::from_utf8_lossy(&out.stdout).lines().take(4).collect::<Vec<_>>().join("\n      "))
    }
}

fn fresh_dir(name: &str) -> PathBuf {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join(name);
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

#[test]
fn generated_programs() {
    let seeds: Vec<u64> = match std::env::var("GEN_SEED") {
        Ok(s) => vec![s.parse().unwrap()],
        Err(_) => (0..std::env::var("GEN_PROGRAMS").ok().and_then(|n| n.parse().ok()).unwrap_or(4)).collect(),
    };
    let with_dafny = std::env::var("GEN_DAFNY").is_ok();

    let root = fresh_dir("generated");
    let failures_dir = fresh_dir("generated-failures");
    std::fs::write(root.join("lib.dfy"), LIB).unwrap();
    std::fs::write(failures_dir.join("lib.dfy"), LIB).unwrap();
    let lib_uri = Url::from_file_path(root.join("lib.dfy")).unwrap();
    let uri = Url::from_file_path(root.join("main.dfy")).unwrap();
    let mut lsp = Lsp::start(&root);

    let mut failures: Vec<Failure> = Vec::new();
    // check -> per scenario (runs, failed); definitions use the Fresh column.
    let mut counts: BTreeMap<String, BTreeMap<Scenario, (usize, usize)>> = BTreeMap::new();
    let mut tally = |key: String, scenario: Scenario, ok: bool| {
        let e = counts.entry(key).or_default().entry(scenario).or_default();
        e.0 += 1;
        if !ok {
            e.1 += 1;
        }
    };
    let mut invalid = 0;

    for &seed in &seeds {
        let prog = Gen::new(seed).generate(seed);
        let mut rng = Rng::new(seed ^ 0xABCD);
        let before = failures.len();

        if with_dafny {
            if let Some(err) = dafny_resolve(&failures_dir, &prog) {
                invalid += 1;
                failures.push(Failure { seed, what: format!("dafny resolve rejects the program:\n      {err}") });
            }
        }

        let mut doc = Doc::open(&mut lsp, &uri, &prog.text);
        for d in &prog.defs {
            let got = doc.definition(d.line, d.col, &lib_uri);
            let ok = !got.is_empty() && got.iter().all(|g| d.expected.contains(g));
            tally("definition of field".into(), Scenario::Fresh, ok);
            if !ok {
                failures.push(Failure {
                    seed,
                    what: format!("definition of `{}` at {}:{}: want one of {:?}, got {:?}", d.name, d.line + 1, d.col + 1, d.expected, got),
                });
            }
        }
        doc.close();

        for probe in &prog.probes {
            for scenario in SCENARIOS {
                let result = run_probe(&mut lsp, &uri, &prog, probe, scenario, &mut rng);
                tally(probe.context.clone(), scenario, result.is_none());
                if let Some(what) = result {
                    failures.push(Failure { seed, what });
                }
            }
        }
        if failures.len() > before {
            std::fs::write(failures_dir.join(format!("seed{seed}.dfy")), &prog.text).unwrap();
        }
    }

    println!("\n{} programs{}", seeds.len(), if with_dafny { format!(", {invalid} rejected by dafny") } else { String::new() });
    println!("{:<36} {:>11} {:>11} {:>11} {:>11}   (failed/runs)", "check", "fresh", "typed", "broken", "autoclose");
    for (k, by) in &counts {
        let cells: Vec<String> = SCENARIOS
            .iter()
            .map(|sc| by.get(sc).map_or(String::from("-"), |(n, bad)| format!("{bad}/{n}")))
            .collect();
        println!("{k:<36} {:>11} {:>11} {:>11} {:>11}", cells[0], cells[1], cells[2], cells[3]);
    }
    for f in failures.iter().take(40) {
        println!("  seed {}: {}", f.seed, f.what);
    }
    if !failures.is_empty() {
        println!("programs with failures are in {}", failures_dir.display());
    }
    assert!(failures.is_empty(), "{} failures", failures.len());
}
