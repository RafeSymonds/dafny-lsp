//! Parsing `dafny verify --json-output` and tracking verification results per document.

use std::collections::{HashMap, HashSet};
use std::path::PathBuf;

use serde::{Deserialize, Serialize};
use serde_json::Value;
use tower_lsp::lsp_types::{
    notification::Notification, Diagnostic, DiagnosticRelatedInformation, DiagnosticSeverity, Location,
    NumberOrString, Position, Range, Url,
};

use crate::config::Config;
use crate::project::Project;
use crate::state::{normalize, EditSpan, FileData};
use crate::symbols::{self, Symbol};
use crate::text::{column_to_byte, Encoding};

pub const RESOLVE_ONLY_FILTER: &str = "--filter-symbol=__dafny_lsp_resolve_only__.";

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Mode {
    Resolve,
    Verify,
    VerifySymbol(String),
}

/// Command line for checking a document read from stdin. `libraries` are the
/// other files of its project, which Dafny resolves but does not verify.
pub fn build_args(cfg: &Config, mode: &Mode, project: Option<&Project>, libraries: &[PathBuf]) -> Vec<String> {
    let mut args: Vec<String> = vec!["verify".into(), "--json-output".into(), "--stdin".into()];
    match mode {
        Mode::Resolve => args.push(RESOLVE_ONLY_FILTER.into()),
        Mode::Verify => args.push("--progress=Symbol".into()),
        Mode::VerifySymbol(q) => {
            args.push("--progress=Symbol".into());
            args.push(format!("--filter-symbol={q}."));
        }
    }
    if *mode != Mode::Resolve {
        if let Some(limit) = cfg.verification_time_limit {
            args.push(format!("--verification-time-limit={limit}"));
        }
        if let Some(cores) = cfg.cores_arg() {
            args.push(format!("--cores={cores}"));
        }
    }
    if let Some(p) = project {
        args.extend(p.args.iter().cloned());
    }
    for f in libraries {
        args.push(format!("--library={}", f.display()));
    }
    args.extend(cfg.extra_args.iter().cloned());
    args
}

// ---------------------------------------------------------------------------
// JSON output

#[derive(Deserialize)]
struct JsonLine {
    #[serde(rename = "type")]
    kind: String,
    value: Value,
}

#[derive(Deserialize, Clone, Debug)]
pub struct JsonPos {
    pub line: i64,
    pub character: i64,
}

#[derive(Deserialize, Clone, Debug)]
pub struct JsonRange {
    pub start: JsonPos,
    pub end: JsonPos,
}

#[derive(Deserialize, Clone, Debug)]
#[serde(rename_all = "camelCase")]
pub struct JsonLocation {
    #[serde(default)]
    pub file_path: Option<String>,
    #[serde(default)]
    pub uri: Option<String>,
    pub range: JsonRange,
}

#[derive(Deserialize, Clone, Debug)]
#[serde(rename_all = "camelCase")]
struct JsonRelated {
    location: JsonLocation,
    #[serde(default)]
    default_format_message: String,
    #[serde(default)]
    arguments: Vec<Value>,
}

#[derive(Deserialize, Clone, Debug)]
#[serde(rename_all = "camelCase")]
struct JsonDiag {
    location: JsonLocation,
    severity: u8,
    #[serde(default)]
    default_format_message: String,
    #[serde(default)]
    arguments: Vec<Value>,
    #[serde(default)]
    error_id: Option<String>,
    #[serde(default)]
    source: Option<String>,
    #[serde(default)]
    related_information: Vec<JsonRelated>,
}

#[derive(Clone, Debug)]
pub struct Related {
    pub location: JsonLocation,
    pub message: String,
}

/// A diagnostic as reported by Dafny: 1-based lines, UTF-16 columns.
#[derive(Clone, Debug)]
pub struct DafnyDiag {
    pub location: JsonLocation,
    pub severity: u8,
    pub message: String,
    pub code: Option<String>,
    pub source: String,
    pub related: Vec<Related>,
}

impl DafnyDiag {
    pub fn is_verifier(&self) -> bool {
        self.source == "Verifier"
    }
}

#[derive(Clone, Debug)]
pub enum Event {
    Diag(DafnyDiag),
    /// "Verified k/N symbols. Waiting for X to verify."
    Progress { done: usize, total: usize, current: String },
    Status(String),
    Text(String),
}

fn format_message(template: &str, args: &[Value]) -> String {
    let mut out = template.to_string();
    for (i, arg) in args.iter().enumerate() {
        let s = match arg {
            Value::String(s) => s.clone(),
            other => other.to_string(),
        };
        out = out.replace(&format!("{{{i}}}"), &s);
    }
    out
}

fn parse_progress(status: &str) -> Option<(usize, usize, String)> {
    let rest = status.strip_prefix("Verified ")?;
    let (counts, rest) = rest.split_once(" symbols. Waiting for ")?;
    let (done, total) = counts.split_once('/')?;
    let current = rest.strip_suffix(" to verify.")?;
    Some((done.parse().ok()?, total.parse().ok()?, current.to_string()))
}

pub fn parse_line(line: &str) -> Event {
    let Ok(parsed) = serde_json::from_str::<JsonLine>(line) else {
        return Event::Text(line.to_string());
    };
    match parsed.kind.as_str() {
        "diagnostic" => match serde_json::from_value::<JsonDiag>(parsed.value) {
            Ok(d) => Event::Diag(DafnyDiag {
                message: format_message(&d.default_format_message, &d.arguments),
                location: d.location,
                severity: d.severity,
                code: d.error_id.filter(|c| !c.is_empty()),
                source: d.source.unwrap_or_default(),
                related: d
                    .related_information
                    .into_iter()
                    .map(|r| Related { message: format_message(&r.default_format_message, &r.arguments), location: r.location })
                    .collect(),
            }),
            Err(_) => Event::Text(line.to_string()),
        },
        "status" => {
            let s = parsed.value.as_str().unwrap_or_default().trim().to_string();
            match parse_progress(&s) {
                Some((done, total, current)) => Event::Progress { done, total, current },
                None => Event::Status(s),
            }
        }
        _ => Event::Text(line.to_string()),
    }
}

// ---------------------------------------------------------------------------
// Converting Dafny positions into editor positions

fn is_stdin(loc: &JsonLocation) -> bool {
    loc.uri.as_deref() == Some("stdin:///") || loc.file_path.as_deref() == Some("<stdin>")
}

fn loc_path(loc: &JsonLocation) -> Option<std::path::PathBuf> {
    let uri = Url::parse(loc.uri.as_deref()?).ok()?;
    uri.to_file_path().ok().map(|p| normalize(&p))
}

/// Byte offset in `file` of a 1-based line and UTF-16 column.
fn byte_offset(file: &FileData, line: i64, character: i64) -> usize {
    if line < 1 {
        return 0;
    }
    let line = (line - 1) as usize;
    if line >= file.index.line_count() {
        return file.text.len();
    }
    let start = file.index.line_start(line);
    let end = file.index.line_end(&file.text, line);
    start + column_to_byte(&file.text[start..end], character.max(0) as usize, Encoding::Utf16)
}

fn local_range(file: &FileData, r: &JsonRange, enc: Encoding) -> (Range, usize) {
    let start = byte_offset(file, r.start.line, r.start.character);
    let end = byte_offset(file, r.end.line, r.end.character).max(start);
    (file.range(&(start..end), enc), start)
}

fn external_range(r: &JsonRange) -> Range {
    let pos = |p: &JsonPos| Position::new((p.line - 1).max(0) as u32, p.character.max(0) as u32);
    Range::new(pos(&r.start), pos(&r.end))
}

/// A diagnostic converted for the document that was checked, plus the byte
/// offset it starts at in that document's text.
pub struct Converted {
    pub diag: Diagnostic,
    pub offset: Option<usize>,
}

/// Converts a Dafny diagnostic into one for `file`. Problems in other files
/// are shown on the include directive that pulls them in.
pub fn convert(d: &DafnyDiag, file: &FileData, enc: Encoding) -> Option<Converted> {
    if d.code.as_deref() == Some("UnverifiedLibrary") {
        return None;
    }
    let severity = match d.severity {
        1 => DiagnosticSeverity::ERROR,
        2 => DiagnosticSeverity::WARNING,
        3 => DiagnosticSeverity::INFORMATION,
        _ => DiagnosticSeverity::HINT,
    };
    let here = is_stdin(&d.location) || (file.path.is_some() && loc_path(&d.location) == file.path);
    let (range, offset, message) = if here {
        let (range, start) = local_range(file, &d.location.range, enc);
        (range, Some(start), d.message.clone())
    } else if d.location.range.start.line < 1 {
        (Range::default(), None, d.message.clone())
    } else {
        if severity != DiagnosticSeverity::ERROR {
            return None;
        }
        let other = loc_path(&d.location);
        let name = other
            .as_deref()
            .and_then(|p| p.file_name())
            .map(|n| n.to_string_lossy().into_owned())
            .unwrap_or_else(|| d.location.file_path.clone().unwrap_or_default());
        let include = file.syms.includes.iter().find(|inc| {
            let target = file.dir().map(|dir| normalize(&dir.join(&inc.path)));
            target.is_some() && target == other
        });
        let include = include.or(file.syms.includes.first());
        let range = include.map(|i| file.range(&i.range, enc)).unwrap_or_default();
        let msg = format!("{}({},{}): {}", name, d.location.range.start.line, d.location.range.start.character + 1, d.message);
        (range, None, msg)
    };
    let related: Vec<DiagnosticRelatedInformation> = d
        .related
        .iter()
        .filter_map(|r| {
            let location = if is_stdin(&r.location) {
                Location::new(file.uri.clone(), local_range(file, &r.location.range, enc).0)
            } else {
                let uri = Url::parse(r.location.uri.as_deref()?).ok()?;
                if Some(&uri) == Some(&file.uri) {
                    Location::new(file.uri.clone(), local_range(file, &r.location.range, enc).0)
                } else {
                    Location::new(uri, external_range(&r.location.range))
                }
            };
            Some(DiagnosticRelatedInformation { location, message: r.message.clone() })
        })
        .collect();
    Some(Converted {
        diag: Diagnostic {
            range,
            severity: Some(severity),
            code: d.code.clone().map(NumberOrString::String),
            source: Some("dafny".to_string()),
            message,
            related_information: (!related.is_empty()).then_some(related),
            ..Default::default()
        },
        offset,
    })
}

// ---------------------------------------------------------------------------
// Per-document verification state

/// Matches `PublishedVerificationStatus` in the Dafny language server.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Status {
    Stale = 0,
    Queued = 1,
    Running = 2,
    Error = 4,
    Correct = 5,
}

#[derive(Default)]
pub struct DocVerification {
    /// Parse and resolution diagnostics from the newest run.
    pub resolve: Vec<Diagnostic>,
    pub resolve_version: Option<i32>,
    /// Verifier diagnostics, with the qualified name of the symbol they belong to.
    pub verify: Vec<(Diagnostic, String)>,
    pub statuses: HashMap<String, Status>,
    /// Symbols edited since they were last verified.
    pub dirty: HashSet<String>,
    /// Edits by document version, used to move results that arrive after the text changed.
    pub edits: Vec<(i32, EditSpan)>,
}

fn overlaps(r: &Range, span: &EditSpan) -> bool {
    r.start.line <= span.old_end_line && r.end.line >= span.start_line
}

fn shift_range(r: &mut Range, delta: i64) {
    r.start.line = (r.start.line as i64 + delta).max(0) as u32;
    r.end.line = (r.end.line as i64 + delta).max(0) as u32;
}

/// Moves diagnostics below an edit and drops the ones on edited lines.
fn shift_diags<T>(diags: &mut Vec<T>, span: &EditSpan, get: impl Fn(&mut T) -> &mut Diagnostic) {
    diags.retain_mut(|d| !overlaps(&get(d).range, span));
    let delta = span.line_delta();
    if delta != 0 {
        for d in diags.iter_mut() {
            let diag = get(d);
            if diag.range.start.line > span.old_end_line {
                shift_range(&mut diag.range, delta);
            }
        }
    }
}

/// Innermost verifiable symbol containing `offset`.
pub fn symbol_at<'a>(symbols: &'a [Symbol], offset: usize) -> Option<&'a Symbol> {
    symbols::verifiables(symbols)
        .into_iter()
        .filter(|s| s.range.start <= offset && offset <= s.range.end)
        .last()
}

impl DocVerification {
    /// Records an edit: moves stored diagnostics and marks edited symbols dirty.
    pub fn on_edit(&mut self, old: &FileData, version: i32, spans: &[EditSpan]) {
        for span in spans {
            shift_diags(&mut self.verify, span, |(d, _)| d);
            shift_diags(&mut self.resolve, span, |d| d);
            for s in symbols::verifiables(&old.syms.symbols) {
                if s.range.start <= span.old_bytes.end && span.old_bytes.start <= s.range.end {
                    self.dirty.insert(s.qname.clone());
                }
            }
            self.edits.push((version, span.clone()));
        }
        if self.edits.len() > 500 {
            self.edits.drain(..self.edits.len() - 500);
        }
    }

    /// Moves diagnostics computed on an older version to the current text.
    pub fn catch_up<T>(&self, since: Option<i32>, diags: &mut Vec<T>, get: impl Fn(&mut T) -> &mut Diagnostic + Copy) {
        let Some(since) = since else { return };
        for (version, span) in &self.edits {
            if *version > since {
                shift_diags(diags, span, get);
            }
        }
    }

    pub fn status(&self, qname: &str) -> Status {
        if self.dirty.contains(qname) {
            Status::Stale
        } else {
            self.statuses.get(qname).copied().unwrap_or(Status::Stale)
        }
    }

    pub fn diagnostics(&self) -> Vec<Diagnostic> {
        let mut out = self.resolve.clone();
        out.extend(self.verify.iter().map(|(d, _)| d.clone()));
        out
    }

    /// One `LineVerificationStatus` per line, as the gutter notification expects.
    pub fn gutter(&self, doc: &FileData) -> Vec<i32> {
        let n = doc.index.line_count();
        let mut lines = vec![0i32; n];
        let obsolete = |v: i32, dirty: bool| if dirty && v >= 200 { v + 1 } else { v };
        for s in symbols::verifiables(&doc.syms.symbols) {
            let dirty = self.dirty.contains(&s.qname);
            let base = match self.statuses.get(&s.qname).copied().unwrap_or(Status::Stale) {
                Status::Correct => 200,
                Status::Error => 300,
                Status::Running => 2,
                Status::Queued => 1,
                Status::Stale => continue,
            };
            let first = doc.index.line_of(s.range.start);
            let last = doc.index.line_of(s.range.end).min(n - 1);
            for l in &mut lines[first..=last] {
                *l = obsolete(base, dirty);
            }
        }
        let mark = |lines: &mut Vec<i32>, r: &Range, v: i32| {
            for l in r.start.line as usize..=(r.end.line as usize).min(n.saturating_sub(1)) {
                if l < n {
                    lines[l] = v;
                }
            }
        };
        for (d, qname) in &self.verify {
            let v = obsolete(400, self.dirty.contains(qname));
            mark(&mut lines, &d.range, v);
            for r in d.related_information.iter().flatten() {
                if r.location.uri == doc.uri {
                    mark(&mut lines, &r.location.range, v);
                }
            }
        }
        for d in &self.resolve {
            if d.severity == Some(DiagnosticSeverity::ERROR) && d.range != Range::default() {
                mark(&mut lines, &d.range, 500);
            }
        }
        lines
    }
}

// ---------------------------------------------------------------------------
// Notifications understood by dafny-verify.nvim and the VS Code extension

#[derive(Serialize, Deserialize, Debug)]
#[serde(rename_all = "camelCase")]
pub struct NamedVerifiable {
    pub name_range: Range,
    pub status: u8,
}

#[derive(Serialize, Deserialize, Debug)]
#[serde(rename_all = "camelCase")]
pub struct SymbolStatusParams {
    pub uri: Url,
    pub version: Option<i32>,
    pub named_verifiables: Vec<NamedVerifiable>,
}

pub enum SymbolStatusNotification {}

impl Notification for SymbolStatusNotification {
    type Params = SymbolStatusParams;
    const METHOD: &'static str = "dafny/textDocument/symbolStatus";
}

#[derive(Serialize, Deserialize, Debug)]
#[serde(rename_all = "camelCase")]
pub struct GutterStatusParams {
    pub uri: Url,
    pub version: Option<i32>,
    pub per_line_status: Vec<i32>,
}

pub enum GutterStatusNotification {}

impl Notification for GutterStatusNotification {
    type Params = GutterStatusParams;
    const METHOD: &'static str = "dafny/verification/status/gutter";
}

pub fn symbol_status_params(doc: &FileData, dv: &DocVerification, enc: Encoding) -> SymbolStatusParams {
    SymbolStatusParams {
        uri: doc.uri.clone(),
        version: doc.version,
        named_verifiables: symbols::verifiables(&doc.syms.symbols)
            .into_iter()
            .map(|s| NamedVerifiable { name_range: doc.range(&s.name_range, enc), status: dv.status(&s.qname) as u8 })
            .collect(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const DIAG: &str = r#"{"type":"diagnostic","value":{"location":{"filename":"","filePath":"<stdin>","uri":"stdin:///","range":{"start":{"pos":112,"line":2,"character":2},"end":{"pos":118,"line":2,"character":8}}},"severity":1,"arguments":["int","bool"],"defaultFormatMessage":"RHS (of type {1}) not assignable to LHS (of type {0})","errorId":null,"source":"Resolver","relatedInformation":[]}}"#;

    #[test]
    fn parses_diagnostics_and_progress() {
        let Event::Diag(d) = parse_line(DIAG) else { panic!() };
        assert_eq!(d.message, "RHS (of type bool) not assignable to LHS (of type int)");
        assert_eq!(d.location.range.start.line, 2);
        let p = parse_line(r#"{"type":"status","value":"Verified 1/4 symbols. Waiting for M.Bad to verify."}"#);
        assert!(matches!(p, Event::Progress { done: 1, total: 4, ref current } if current == "M.Bad"));
        assert!(matches!(parse_line("CLI: Error: bad"), Event::Text(_)));
    }

    #[test]
    fn converts_positions_to_editor_coordinates() {
        let uri = Url::parse("file:///ws/a.dfy").unwrap();
        let file = FileData::new(uri, Some(1), "method M() {\n  assert false;\n}\n".into(), None, None);
        let Event::Diag(d) = parse_line(DIAG) else { panic!() };
        let c = convert(&d, &file, Encoding::Utf16).unwrap();
        assert_eq!(c.diag.range, Range::new(Position::new(1, 2), Position::new(1, 8)));
        assert_eq!(&file.text[c.offset.unwrap()..c.offset.unwrap() + 6], "assert");
    }

    #[test]
    fn edits_shift_and_drop_diagnostics() {
        let uri = Url::parse("file:///ws/a.dfy").unwrap();
        let file = FileData::new(uri, Some(1), "method A() {}\nmethod B() {}\nmethod C() {}\n".into(), None, None);
        let mut dv = DocVerification::default();
        let diag = |line| Diagnostic { range: Range::new(Position::new(line, 0), Position::new(line, 3)), ..Default::default() };
        dv.verify = vec![(diag(0), "A".into()), (diag(2), "C".into())];
        dv.statuses.insert("A".into(), Status::Error);
        // insert a line inside B
        let span = EditSpan { old_bytes: 25..25, start_line: 1, old_end_line: 1, new_end_line: 2 };
        dv.on_edit(&file, 2, &[span]);
        let lines: Vec<u32> = dv.verify.iter().map(|(d, _)| d.range.start.line).collect();
        assert_eq!(lines, vec![0, 3]);
        assert!(dv.dirty.contains("B"));
        assert_eq!(dv.status("B"), Status::Stale);
        assert_eq!(dv.status("A"), Status::Error);
    }
}
