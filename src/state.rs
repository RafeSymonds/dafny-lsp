use std::collections::{HashMap, HashSet};
use std::ops::Range;
use std::path::{Component, Path, PathBuf};
use std::sync::{Arc, Mutex, RwLock};
use std::time::{Duration, Instant, SystemTime};

use tower_lsp::lsp_types::{self as lsp, TextDocumentContentChangeEvent, Url};
use tree_sitter::{InputEdit, Node, Point, Tree};

use crate::config::Config;
use crate::project::{self, Project};
use crate::symbols::{self, FileSymbols};
use crate::syntax;
use crate::text::{Encoding, LineIndex};

const MAX_WORKSPACE_FILES: usize = 3000;
const MAX_FILE_BYTES: u64 = 10 * 1024 * 1024;
const FILE_LIST_TTL: Duration = Duration::from_secs(5);

/// A parsed Dafny file: either an open editor buffer or a file read from disk.
pub struct FileData {
    pub uri: Url,
    pub path: Option<PathBuf>,
    pub version: Option<i32>,
    pub text: String,
    pub index: LineIndex,
    /// Tree used for analysis. When the text has syntax errors this may be a
    /// parse of the text with the edited lines blanked out (see `repair`).
    pub tree: Tree,
    /// Parse of the actual text, kept for incremental reparsing.
    pub raw_tree: Tree,
    pub syms: FileSymbols,
    pub mtime: Option<SystemTime>,
}

impl FileData {
    pub fn new(uri: Url, version: Option<i32>, text: String, old_tree: Option<&Tree>, mtime: Option<SystemTime>) -> Self {
        let path = uri.to_file_path().ok().map(|p| normalize(&p));
        let raw_tree = syntax::parse(&text, old_tree);
        let syms = symbols::extract(raw_tree.root_node(), &text);
        FileData { uri, path, version, index: LineIndex::new(&text), text, tree: raw_tree.clone(), raw_tree, syms, mtime }
    }

    pub fn root(&self) -> Node<'_> {
        self.tree.root_node()
    }

    pub fn has_syntax_errors(&self) -> bool {
        self.raw_tree.root_node().has_error()
    }

    /// Uses `tree` for analysis if it parses cleanly. Returns false otherwise.
    fn adopt(&mut self, tree: Tree) -> bool {
        if tree.root_node().has_error() {
            return false;
        }
        self.syms = symbols::extract(tree.root_node(), &self.text);
        self.tree = tree;
        true
    }

    /// While the user types, the text usually has a syntax error on the lines
    /// being edited, and tree-sitter's recovery can wrap a whole module in an
    /// ERROR node. This blanks the lines that differ from the last version
    /// that parsed cleanly (keeping byte offsets) and analyses that instead.
    pub fn repair(&mut self, last_good: &FileData) {
        if !self.has_syntax_errors() {
            return;
        }
        let Some(lines) = changed_lines(&last_good.text, &self.text) else { return };
        let blanked = blank_lines(&self.text, &self.index, lines);
        let tree = syntax::parse(&blanked, None);
        self.adopt(tree);
    }

    /// A copy of this file analysed with one more line blanked, if that makes
    /// the analysis tree parse cleanly. Used for completion on a half-typed line.
    pub fn without_line(&self, line: usize) -> Option<FileData> {
        if !self.tree.root_node().has_error() {
            return None;
        }
        let blanked = blank_lines(&self.text, &self.index, line..line + 1);
        let mut copy = FileData {
            uri: self.uri.clone(),
            path: self.path.clone(),
            version: self.version,
            text: self.text.clone(),
            index: self.index.clone(),
            tree: self.tree.clone(),
            raw_tree: self.raw_tree.clone(),
            syms: self.syms.clone(),
            mtime: self.mtime,
        };
        copy.adopt(syntax::parse(&blanked, None)).then_some(copy)
    }

    pub fn pos(&self, offset: usize, enc: Encoding) -> lsp::Position {
        self.index.position(&self.text, offset, enc)
    }

    pub fn range(&self, r: &Range<usize>, enc: Encoding) -> lsp::Range {
        lsp::Range::new(self.pos(r.start, enc), self.pos(r.end, enc))
    }

    pub fn offset(&self, pos: lsp::Position, enc: Encoding) -> usize {
        self.index.offset(&self.text, pos, enc)
    }

    pub fn dir(&self) -> Option<&Path> {
        self.path.as_deref().and_then(Path::parent)
    }
}

/// Lines of `new` that differ from `old`, found by trimming the common
/// leading and trailing lines. None when there is no change or most of the file changed.
fn changed_lines(old: &str, new: &str) -> Option<Range<usize>> {
    let old_lines: Vec<&str> = old.split('\n').collect();
    let new_lines: Vec<&str> = new.split('\n').collect();
    let prefix = old_lines.iter().zip(&new_lines).take_while(|(a, b)| a == b).count();
    let max_suffix = old_lines.len().min(new_lines.len()) - prefix;
    let suffix = old_lines
        .iter()
        .rev()
        .zip(new_lines.iter().rev())
        .take(max_suffix)
        .take_while(|(a, b)| a == b)
        .count();
    let end = new_lines.len() - suffix;
    if prefix >= end || (end - prefix) * 2 > new_lines.len().max(20) {
        return None;
    }
    Some(prefix..end)
}

/// Replaces every byte on the given lines with a space, keeping line breaks and offsets.
fn blank_lines(text: &str, index: &LineIndex, lines: Range<usize>) -> String {
    let mut bytes = text.as_bytes().to_vec();
    for line in lines {
        if line >= index.line_count() {
            break;
        }
        let start = index.line_start(line);
        let end = index.line_end(text, line);
        for b in &mut bytes[start..end] {
            *b = b' ';
        }
    }
    String::from_utf8(bytes).expect("only ASCII spaces were written")
}

/// Where an edit happened, in lines of the text before the edit.
#[derive(Clone, Debug)]
pub struct EditSpan {
    pub old_bytes: Range<usize>,
    pub start_line: u32,
    pub old_end_line: u32,
    pub new_end_line: u32,
}

impl EditSpan {
    pub fn line_delta(&self) -> i64 {
        self.new_end_line as i64 - self.old_end_line as i64
    }
}

fn point_after(start: Point, inserted: &str) -> Point {
    match inserted.rfind('\n') {
        Some(last) => Point::new(start.row + inserted.matches('\n').count(), inserted.len() - last - 1),
        None => Point::new(start.row, start.column + inserted.len()),
    }
}

/// Applies LSP content changes to a document and reparses it incrementally.
pub fn apply_changes(
    old: &FileData,
    changes: &[TextDocumentContentChangeEvent],
    version: i32,
    enc: Encoding,
) -> (FileData, Vec<EditSpan>) {
    let mut text = old.text.clone();
    let mut tree = Some(old.raw_tree.clone());
    let mut spans = Vec::new();
    for change in changes {
        match change.range {
            Some(range) => {
                let index = LineIndex::new(&text);
                let start = index.offset(&text, range.start, enc);
                let end = index.offset(&text, range.end, enc).max(start);
                let start_position = index.point(start);
                let old_end_position = index.point(end);
                let new_end_position = point_after(start_position, &change.text);
                text.replace_range(start..end, &change.text);
                if let Some(tree) = tree.as_mut() {
                    tree.edit(&InputEdit {
                        start_byte: start,
                        old_end_byte: end,
                        new_end_byte: start + change.text.len(),
                        start_position,
                        old_end_position,
                        new_end_position,
                    });
                }
                spans.push(EditSpan {
                    old_bytes: start..end,
                    start_line: start_position.row as u32,
                    old_end_line: old_end_position.row as u32,
                    new_end_line: new_end_position.row as u32,
                });
            }
            None => {
                let old_lines = LineIndex::new(&text).line_count() as u32;
                spans.push(EditSpan {
                    old_bytes: 0..text.len(),
                    start_line: 0,
                    old_end_line: old_lines,
                    new_end_line: LineIndex::new(&change.text).line_count() as u32,
                });
                text = change.text.clone();
                tree = None;
            }
        }
    }
    (FileData::new(old.uri.clone(), Some(version), text, tree.as_ref(), None), spans)
}

/// Removes `.` and `..` components without touching the file system.
pub fn normalize(p: &Path) -> PathBuf {
    let mut out = PathBuf::new();
    for c in p.components() {
        match c {
            Component::CurDir => {}
            Component::ParentDir => {
                out.pop();
            }
            other => out.push(other),
        }
    }
    out
}

pub struct State {
    docs: RwLock<HashMap<Url, Arc<FileData>>>,
    disk: Mutex<HashMap<PathBuf, Arc<FileData>>>,
    roots: RwLock<Vec<PathBuf>>,
    file_list: Mutex<Option<(Instant, Arc<Vec<PathBuf>>)>>,
    project_files: Mutex<HashMap<PathBuf, (Instant, Option<PathBuf>)>>,
    projects: Mutex<HashMap<PathBuf, (Option<SystemTime>, Option<Arc<Project>>)>>,
    /// Newest version of each open document that parsed without syntax errors.
    last_good: Mutex<HashMap<Url, Arc<FileData>>>,
    pub encoding: RwLock<Encoding>,
    pub config: RwLock<Config>,
}

impl Default for State {
    fn default() -> Self {
        State {
            docs: RwLock::new(HashMap::new()),
            disk: Mutex::new(HashMap::new()),
            roots: RwLock::new(Vec::new()),
            file_list: Mutex::new(None),
            project_files: Mutex::new(HashMap::new()),
            projects: Mutex::new(HashMap::new()),
            last_good: Mutex::new(HashMap::new()),
            encoding: RwLock::new(Encoding::Utf16),
            config: RwLock::new(Config::default()),
        }
    }
}

impl State {
    pub fn encoding(&self) -> Encoding {
        *self.encoding.read().unwrap()
    }

    pub fn config(&self) -> Config {
        self.config.read().unwrap().clone()
    }

    pub fn set_roots(&self, roots: Vec<PathBuf>) {
        *self.roots.write().unwrap() = roots.iter().map(|r| normalize(r)).collect();
        self.invalidate_file_list();
    }

    pub fn doc(&self, uri: &Url) -> Option<Arc<FileData>> {
        self.docs.read().unwrap().get(uri).cloned()
    }

    /// Stores an open document, repairing its analysis tree if it has syntax errors.
    pub fn put_doc(&self, mut doc: FileData) -> Arc<FileData> {
        let mut last_good = self.last_good.lock().unwrap();
        if let Some(good) = last_good.get(&doc.uri) {
            doc.repair(good);
        }
        let doc = Arc::new(doc);
        if !doc.has_syntax_errors() {
            last_good.insert(doc.uri.clone(), doc.clone());
        }
        self.docs.write().unwrap().insert(doc.uri.clone(), doc.clone());
        doc
    }

    pub fn remove_doc(&self, uri: &Url) {
        self.docs.write().unwrap().remove(uri);
        self.last_good.lock().unwrap().remove(uri);
    }

    pub fn open_docs(&self) -> Vec<Arc<FileData>> {
        self.docs.read().unwrap().values().cloned().collect()
    }

    pub fn invalidate_path(&self, path: &Path) {
        self.disk.lock().unwrap().remove(&normalize(path));
    }

    pub fn invalidate_file_list(&self) {
        *self.file_list.lock().unwrap() = None;
        self.project_files.lock().unwrap().clear();
    }

    /// The open buffer for `path` if there is one, otherwise the file on disk.
    pub fn file_by_path(&self, path: &Path) -> Option<Arc<FileData>> {
        let path = normalize(path);
        if let Some(doc) = self.docs.read().unwrap().values().find(|d| d.path.as_deref() == Some(path.as_path())) {
            return Some(doc.clone());
        }
        let meta = std::fs::metadata(&path).ok()?;
        if !meta.is_file() || meta.len() > MAX_FILE_BYTES {
            return None;
        }
        let mtime = meta.modified().ok();
        if let Some(cached) = self.disk.lock().unwrap().get(&path) {
            if cached.mtime == mtime {
                return Some(cached.clone());
            }
        }
        let bytes = std::fs::read(&path).ok()?;
        let text = String::from_utf8_lossy(&bytes).into_owned();
        let uri = Url::from_file_path(&path).ok()?;
        let file = Arc::new(FileData::new(uri, None, text, None, mtime));
        self.disk.lock().unwrap().insert(path, file.clone());
        Some(file)
    }

    /// Paths of all .dfy files under the workspace roots, cached for a few seconds.
    pub fn workspace_paths(&self) -> Arc<Vec<PathBuf>> {
        if let Some((at, list)) = self.file_list.lock().unwrap().as_ref() {
            if at.elapsed() < FILE_LIST_TTL {
                return list.clone();
            }
        }
        let mut roots = self.roots.read().unwrap().clone();
        let mut shallow = false;
        if roots.is_empty() {
            roots = self.open_docs().iter().filter_map(|d| d.dir().map(Path::to_path_buf)).collect();
            roots.sort();
            roots.dedup();
            shallow = true;
        }
        let home = std::env::var_os("HOME").map(PathBuf::from);
        let mut paths = Vec::new();
        'roots: for root in roots {
            // Walking a home directory or the file system root would take far too long.
            let too_broad = root.parent().is_none() || Some(&root) == home.as_ref();
            let mut builder = ignore::WalkBuilder::new(&root);
            if shallow || too_broad {
                builder.max_depth(Some(1));
            }
            for entry in builder.build().flatten() {
                if entry.path().extension().and_then(|e| e.to_str()) == Some("dfy") {
                    paths.push(normalize(entry.path()));
                    if paths.len() >= MAX_WORKSPACE_FILES {
                        break 'roots;
                    }
                }
            }
        }
        paths.sort();
        paths.dedup();
        let list = Arc::new(paths);
        *self.file_list.lock().unwrap() = Some((Instant::now(), list.clone()));
        list
    }

    /// Every known file: open buffers plus the workspace files on disk.
    pub fn all_files(&self) -> Vec<Arc<FileData>> {
        let mut out = self.open_docs();
        let mut seen: HashSet<PathBuf> = out.iter().filter_map(|d| d.path.clone()).collect();
        for path in self.workspace_paths().iter() {
            if seen.insert(path.clone()) {
                if let Some(f) = self.file_by_path(path) {
                    out.push(f);
                }
            }
        }
        out
    }

    /// Files whose top-level declarations are visible from `file`: its includes
    /// (transitively) and the other members of its dfyconfig.toml project.
    pub fn scope_files(&self, file: &Arc<FileData>) -> Vec<Arc<FileData>> {
        let mut seen: HashSet<Url> = HashSet::from([file.uri.clone()]);
        let mut out = Vec::new();
        let mut queue = vec![file.clone()];
        if let Some(proj) = file.path.as_deref().and_then(|p| self.project_for(p)) {
            for p in &proj.files {
                if let Some(f) = self.file_by_path(p) {
                    if seen.insert(f.uri.clone()) {
                        out.push(f.clone());
                        queue.push(f);
                    }
                }
            }
        }
        while let Some(f) = queue.pop() {
            let Some(dir) = f.dir().map(Path::to_path_buf) else { continue };
            for inc in &f.syms.includes {
                if let Some(target) = self.file_by_path(&dir.join(&inc.path)) {
                    if seen.insert(target.uri.clone()) {
                        out.push(target.clone());
                        queue.push(target);
                    }
                }
            }
            if out.len() > 1000 {
                break;
            }
        }
        out
    }

    /// True when `from` includes `target`, directly or through other includes.
    pub fn includes_transitively(&self, from: &Path, target: &Path) -> bool {
        let mut seen = HashSet::new();
        let mut stack = vec![normalize(from)];
        while let Some(path) = stack.pop() {
            if !seen.insert(path.clone()) || seen.len() > 1000 {
                continue;
            }
            let Some(file) = self.file_by_path(&path) else { continue };
            let Some(dir) = file.dir() else { continue };
            for inc in &file.syms.includes {
                let next = normalize(&dir.join(&inc.path));
                if next == target {
                    return true;
                }
                stack.push(next);
            }
        }
        false
    }

    pub fn project_for(&self, file_path: &Path) -> Option<Arc<Project>> {
        let dir = file_path.parent()?.to_path_buf();
        let config_path = {
            let mut cache = self.project_files.lock().unwrap();
            match cache.get(&dir) {
                Some((at, found)) if at.elapsed() < FILE_LIST_TTL => found.clone(),
                _ => {
                    let found = project::find_project_file(&dir);
                    cache.insert(dir, (Instant::now(), found.clone()));
                    found
                }
            }
        }?;
        let mtime = std::fs::metadata(&config_path).and_then(|m| m.modified()).ok();
        let mut projects = self.projects.lock().unwrap();
        if let Some((cached_mtime, proj)) = projects.get(&config_path) {
            if *cached_mtime == mtime {
                return proj.clone();
            }
        }
        let proj = project::load(&config_path).ok().map(Arc::new);
        projects.insert(config_path, (mtime, proj.clone()));
        proj
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn change(sl: u32, sc: u32, el: u32, ec: u32, text: &str) -> TextDocumentContentChangeEvent {
        TextDocumentContentChangeEvent {
            range: Some(lsp::Range::new(lsp::Position::new(sl, sc), lsp::Position::new(el, ec))),
            range_length: None,
            text: text.to_string(),
        }
    }

    #[test]
    fn incremental_edits_match_full_parse() {
        let uri = Url::parse("file:///tmp/x.dfy").unwrap();
        let doc = FileData::new(uri, Some(1), "method A() {}\nmethod B() {}\n".to_string(), None, None);
        let (doc, spans) = apply_changes(
            &doc,
            &[change(0, 7, 0, 8, "Alpha"), change(1, 13, 1, 13, "\nlemma C() {}")],
            2,
            Encoding::Utf16,
        );
        assert_eq!(doc.text, "method Alpha() {}\nmethod B() {}\nlemma C() {}\n");
        let names: Vec<_> = doc.syms.symbols.iter().map(|s| s.name.as_str()).collect();
        assert_eq!(names, vec!["Alpha", "B", "C"]);
        let fresh = syntax::parse(&doc.text, None);
        assert_eq!(doc.tree.root_node().to_sexp(), fresh.root_node().to_sexp());
        assert_eq!(spans[1].line_delta(), 1);
    }

    #[test]
    fn normalize_resolves_dots() {
        assert_eq!(normalize(Path::new("/a/b/../c/./d.dfy")), PathBuf::from("/a/c/d.dfy"));
    }
}
