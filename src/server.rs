use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::process::Stdio;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{Arc, Mutex, RwLock};
use std::time::Duration;

use serde_json::Value;
use tokio::io::{AsyncBufReadExt, AsyncReadExt, AsyncWriteExt, BufReader};
use tokio::task::JoinHandle;
use tower_lsp::jsonrpc::{Error as RpcError, Result};
use tower_lsp::lsp_types::notification::Progress;
use tower_lsp::lsp_types::request::WorkDoneProgressCreate;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer};

use crate::config::{Config, VerifyOn};
use crate::state::{apply_changes, FileData, State};
use crate::symbols;
use crate::text::Encoding;
use crate::verify::{self, DocVerification, Event, GutterStatusNotification, GutterStatusParams, Mode, Status, SymbolStatusNotification};
use crate::{analysis, completion, info, navigation};

pub const COMMANDS: &[&str] = &["dafny-lsp.verify", "dafny-lsp.verifySymbol", "dafny-lsp.verifyAt", "dafny-lsp.cancel"];

#[derive(Default)]
struct ClientCaps {
    snippets: bool,
    progress: bool,
    watch_files: bool,
}

#[derive(Default)]
struct Slots {
    resolve: Option<JoinHandle<()>>,
    verify: Option<JoinHandle<()>>,
}

struct Inner {
    st: State,
    caps: RwLock<ClientCaps>,
    verif: Mutex<HashMap<Url, DocVerification>>,
    tasks: Mutex<HashMap<Url, Slots>>,
    progress_ids: AtomicU64,
    spawn_error_shown: AtomicBool,
}

#[derive(Clone)]
pub struct Backend {
    client: Client,
    inner: Arc<Inner>,
}

/// Ends a work-done progress when dropped, so cancelled runs do not leave a spinner behind.
struct ProgressGuard {
    client: Client,
    token: NumberOrString,
    ended: bool,
}

impl ProgressGuard {
    async fn report(&self, message: String, percentage: Option<u32>) {
        let value = WorkDoneProgress::Report(WorkDoneProgressReport { cancellable: None, message: Some(message), percentage });
        self.client
            .send_notification::<Progress>(ProgressParams { token: self.token.clone(), value: ProgressParamsValue::WorkDone(value) })
            .await;
    }

    async fn end(mut self, message: String) {
        self.ended = true;
        let value = WorkDoneProgress::End(WorkDoneProgressEnd { message: Some(message) });
        self.client
            .send_notification::<Progress>(ProgressParams { token: self.token.clone(), value: ProgressParamsValue::WorkDone(value) })
            .await;
    }
}

impl Drop for ProgressGuard {
    fn drop(&mut self) {
        if self.ended {
            return;
        }
        let client = self.client.clone();
        let token = self.token.clone();
        tokio::spawn(async move {
            let value = WorkDoneProgress::End(WorkDoneProgressEnd { message: Some("cancelled".into()) });
            client.send_notification::<Progress>(ProgressParams { token, value: ProgressParamsValue::WorkDone(value) }).await;
        });
    }
}

/// Finds the dafny executable. GUI editors on macOS often start without the
/// Homebrew directories on PATH, so a few common locations are tried too.
fn find_dafny(configured: &str) -> PathBuf {
    if configured.contains('/') {
        return PathBuf::from(configured);
    }
    if let Some(paths) = std::env::var_os("PATH") {
        for dir in std::env::split_paths(&paths) {
            let candidate = dir.join(configured);
            if candidate.is_file() {
                return candidate;
            }
        }
    }
    let home = std::env::var("HOME").unwrap_or_default();
    for candidate in [
        "/opt/homebrew/bin/dafny".to_string(),
        "/usr/local/bin/dafny".to_string(),
        format!("{home}/.dotnet/tools/dafny"),
    ] {
        if configured == "dafny" && Path::new(&candidate).is_file() {
            return PathBuf::from(candidate);
        }
    }
    PathBuf::from(configured)
}

/// Maps a name from Dafny's progress output to one of the document's
/// verifiable symbols. Iterators report extra members such as `Gen.MoveNext`.
fn map_name(name: &str, qnames: &[String]) -> Option<String> {
    if qnames.iter().any(|q| q == name) {
        return Some(name.to_string());
    }
    qnames
        .iter()
        .filter(|q| name.starts_with(&format!("{q}.")))
        .max_by_key(|q| q.len())
        .cloned()
}

/// Parses "Dafny program verifier finished with 2 verified, 1 error".
fn parse_summary(s: &str) -> Option<(usize, usize)> {
    let rest = s.split("finished with ").nth(1)?;
    let mut nums = rest.split(|c: char| !c.is_ascii_digit()).filter(|p| !p.is_empty()).map(|p| p.parse::<usize>().ok());
    Some((nums.next()??, nums.next()??))
}

/// For requests made while typing: if the line under the cursor is what breaks
/// the parse, analyse the document without that line.
fn typing_view(doc: Arc<FileData>, offset: usize) -> Arc<FileData> {
    match doc.without_line(doc.index.line_of(offset)) {
        Some(view) => Arc::new(view),
        None => doc,
    }
}

fn uri_arg(args: &[Value], i: usize) -> Option<Url> {
    args.get(i).and_then(Value::as_str).and_then(|s| Url::parse(s).ok())
}

impl Backend {
    pub fn new(client: Client) -> Self {
        Backend {
            client,
            inner: Arc::new(Inner {
                st: State::default(),
                caps: RwLock::new(ClientCaps::default()),
                verif: Mutex::new(HashMap::new()),
                tasks: Mutex::new(HashMap::new()),
                progress_ids: AtomicU64::new(0),
                spawn_error_shown: AtomicBool::new(false),
            }),
        }
    }

    fn st(&self) -> &State {
        &self.inner.st
    }

    fn enc(&self) -> Encoding {
        self.inner.st.encoding()
    }

    /// Sends diagnostics and the verification status notifications for a document.
    async fn publish(&self, uri: &Url) {
        let Some(doc) = self.st().doc(uri) else { return };
        let enc = self.enc();
        let (diags, symbol_params, gutter) = {
            let mut verif = self.inner.verif.lock().unwrap();
            let dv = verif.entry(uri.clone()).or_default();
            (dv.diagnostics(), verify::symbol_status_params(&doc, dv, enc), dv.gutter(&doc))
        };
        self.client.publish_diagnostics(uri.clone(), diags, doc.version).await;
        self.client.send_notification::<SymbolStatusNotification>(symbol_params).await;
        self.client
            .send_notification::<GutterStatusNotification>(GutterStatusParams {
                uri: uri.clone(),
                version: doc.version,
                per_line_status: gutter,
            })
            .await;
    }

    /// Starts a dafny run after `delay`, replacing any pending or running run of the same kind.
    fn schedule(&self, uri: Url, mode: Mode, delay: Duration) {
        let this = self.clone();
        let mut tasks = self.inner.tasks.lock().unwrap();
        let slots = tasks.entry(uri.clone()).or_default();
        let slot = if mode == Mode::Resolve { &mut slots.resolve } else { &mut slots.verify };
        if let Some(handle) = slot.take() {
            handle.abort();
        }
        *slot = Some(tokio::spawn(async move {
            if !delay.is_zero() {
                tokio::time::sleep(delay).await;
            }
            this.run(uri, mode).await;
        }));
    }

    fn schedule_on_change(&self, uri: Url) {
        let cfg = self.st().config();
        let delay = Duration::from_millis(cfg.debounce_ms);
        match cfg.verify_on {
            VerifyOn::Change => self.schedule(uri, Mode::Verify, delay),
            VerifyOn::Save | VerifyOn::Never => self.schedule(uri, Mode::Resolve, delay),
        }
    }

    fn cancel(&self, uri: &Url) {
        if let Some(slots) = self.inner.tasks.lock().unwrap().get_mut(uri) {
            for handle in [slots.resolve.take(), slots.verify.take()].into_iter().flatten() {
                handle.abort();
            }
        }
    }

    async fn begin_progress(&self, doc: &FileData) -> Option<ProgressGuard> {
        if !self.inner.caps.read().unwrap().progress {
            return None;
        }
        let id = self.inner.progress_ids.fetch_add(1, Ordering::Relaxed);
        let token = NumberOrString::String(format!("dafny-lsp/verify/{id}"));
        let create = self.client.send_request::<WorkDoneProgressCreate>(WorkDoneProgressCreateParams { token: token.clone() });
        match tokio::time::timeout(Duration::from_secs(2), create).await {
            Ok(Ok(())) => {}
            _ => return None,
        }
        let name = doc
            .path
            .as_deref()
            .and_then(|p| p.file_name())
            .map(|n| n.to_string_lossy().into_owned())
            .unwrap_or_else(|| doc.uri.to_string());
        let begin = WorkDoneProgress::Begin(WorkDoneProgressBegin {
            title: "Verifying".to_string(),
            cancellable: Some(false),
            message: Some(name),
            percentage: Some(0),
        });
        self.client
            .send_notification::<Progress>(ProgressParams { token: token.clone(), value: ProgressParamsValue::WorkDone(begin) })
            .await;
        Some(ProgressGuard { client: self.client.clone(), token, ended: false })
    }

    async fn report_spawn_error(&self, dafny: &Path, err: std::io::Error) {
        if !self.inner.spawn_error_shown.swap(true, Ordering::Relaxed) {
            let msg = format!(
                "dafny-lsp could not start `{}`: {}. Set `dafnyPath` in the server settings.",
                dafny.display(),
                err
            );
            self.client.show_message(MessageType::ERROR, msg).await;
        }
    }

    /// Runs `dafny verify` on the current text of a document and records the results.
    async fn run(&self, uri: Url, mode: Mode) {
        let st = self.st();
        let Some(doc) = st.doc(&uri) else { return };
        let cfg: Config = st.config();
        let enc = self.enc();
        let project = doc.path.as_deref().and_then(|p| st.project_for(p));
        // A project file that includes this document would load it a second time from disk.
        let libraries: Vec<PathBuf> = match (&project, &doc.path) {
            (Some(p), Some(this)) => p.files.iter().filter(|f| *f != this && !st.includes_transitively(f, this)).cloned().collect(),
            (Some(p), None) => p.files.clone(),
            _ => Vec::new(),
        };
        let args = verify::build_args(&cfg, &mode, project.as_deref(), &libraries);
        let cwd = doc.dir().map(Path::to_path_buf).or_else(|| project.as_ref().map(|p| p.dir.clone()));
        let qnames: Vec<String> = symbols::verifiables(&doc.syms.symbols).iter().map(|s| s.qname.clone()).collect();
        let targets: Vec<String> = match &mode {
            Mode::Resolve => Vec::new(),
            Mode::Verify => qnames.clone(),
            Mode::VerifySymbol(q) => vec![q.clone()],
        };

        if mode != Mode::Resolve {
            {
                let mut verif = self.inner.verif.lock().unwrap();
                let dv = verif.entry(uri.clone()).or_default();
                for q in &targets {
                    dv.statuses.insert(q.clone(), Status::Queued);
                    dv.dirty.remove(q);
                }
            }
            self.publish(&uri).await;
        }
        let progress = if mode != Mode::Resolve { self.begin_progress(&doc).await } else { None };

        let dafny = find_dafny(&cfg.dafny_path);
        let mut cmd = tokio::process::Command::new(&dafny);
        cmd.args(&args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .kill_on_drop(true);
        if let Some(cwd) = &cwd {
            cmd.current_dir(cwd);
        }
        let mut child = match cmd.spawn() {
            Ok(c) => c,
            Err(e) => {
                self.report_spawn_error(&dafny, e).await;
                let mut verif = self.inner.verif.lock().unwrap();
                let dv = verif.entry(uri.clone()).or_default();
                for q in &targets {
                    dv.statuses.insert(q.clone(), Status::Stale);
                }
                return;
            }
        };
        if let Some(mut stdin) = child.stdin.take() {
            let text = doc.text.clone();
            tokio::spawn(async move {
                let _ = stdin.write_all(text.as_bytes()).await;
                let _ = stdin.shutdown().await;
            });
        }
        let stderr_task = child.stderr.take().map(|mut err| {
            tokio::spawn(async move {
                let mut s = String::new();
                let _ = err.read_to_string(&mut s).await;
                s
            })
        });
        let Some(stdout) = child.stdout.take() else { return };
        let mut lines = BufReader::new(stdout).lines();

        let mut resolve_diags = Vec::new();
        let mut verify_diags: Vec<(Diagnostic, String)> = Vec::new();
        let mut other_text = Vec::new();
        let mut summary = None;
        let mut announced: Vec<String> = Vec::new();

        while let Ok(Some(line)) = lines.next_line().await {
            match verify::parse_line(&line) {
                Event::Diag(d) => {
                    let Some(c) = verify::convert(&d, &doc, enc) else { continue };
                    if d.is_verifier() {
                        let q = c
                            .offset
                            .and_then(|o| verify::symbol_at(&doc.syms.symbols, o))
                            .map(|s| s.qname.clone())
                            .unwrap_or_default();
                        verify_diags.push((c.diag, q));
                    } else {
                        resolve_diags.push(c.diag);
                    }
                }
                Event::Progress { done, total, current } => {
                    // Dafny names the first symbol that is not done yet, so
                    // every symbol it named before has finished.
                    let finished: Vec<String> = announced.drain(..).filter(|n| *n != current).collect();
                    {
                        let mut verif = self.inner.verif.lock().unwrap();
                        let dv = verif.entry(uri.clone()).or_default();
                        for name in finished {
                            let Some(q) = map_name(&name, &qnames) else { continue };
                            let mut mine: Vec<(Diagnostic, String)> =
                                verify_diags.iter().filter(|(_, dq)| *dq == q).cloned().collect();
                            dv.statuses.insert(q.clone(), if mine.is_empty() { Status::Correct } else { Status::Error });
                            dv.catch_up(doc.version, &mut mine, |(d, _)| d);
                            dv.verify.retain(|(_, dq)| *dq != q);
                            dv.verify.extend(mine);
                        }
                        if let Some(q) = map_name(&current, &qnames) {
                            dv.statuses.insert(q, Status::Running);
                        }
                    }
                    announced.push(current.clone());
                    if let Some(p) = &progress {
                        let pct = (done * 100).checked_div(total).map(|p| p as u32);
                        p.report(format!("{current} ({done}/{total})"), pct).await;
                    }
                    self.publish(&uri).await;
                }
                Event::Status(s) => {
                    if s.contains("finished with") {
                        summary = Some(s);
                    }
                }
                Event::Text(t) => other_text.push(t),
            }
        }
        let exit = child.wait().await.ok().and_then(|s| s.code());
        let stderr = match stderr_task {
            Some(t) => t.await.unwrap_or_default(),
            None => String::new(),
        };

        // Exit code 1 with nothing parsed means dafny rejected the command line.
        if exit == Some(1) && resolve_diags.is_empty() && verify_diags.is_empty() {
            let mut msg: Vec<String> = other_text.iter().map(|s| s.trim().to_string()).filter(|s| !s.is_empty()).collect();
            msg.extend(stderr.lines().map(|s| s.trim().to_string()).filter(|s| !s.is_empty()));
            let msg = msg.into_iter().take(5).collect::<Vec<_>>().join("\n");
            self.client.log_message(MessageType::ERROR, format!("dafny {}: {}", args.join(" "), msg)).await;
            resolve_diags.push(Diagnostic {
                range: Range::default(),
                severity: Some(DiagnosticSeverity::ERROR),
                source: Some("dafny-lsp".into()),
                message: format!("dafny failed: {msg}"),
                ..Default::default()
            });
        }

        let resolution_failed = resolve_diags.iter().any(|d| d.severity == Some(DiagnosticSeverity::ERROR));
        let counts = summary.as_deref().and_then(parse_summary);
        {
            let mut verif = self.inner.verif.lock().unwrap();
            let dv = verif.entry(uri.clone()).or_default();
            let newer_known = matches!((dv.resolve_version, doc.version), (Some(have), Some(this)) if have > this);
            if !newer_known {
                dv.catch_up(doc.version, &mut resolve_diags, |d| d);
                dv.resolve = resolve_diags;
                dv.resolve_version = doc.version;
            }
            let verified_nothing = counts == Some((0, 0));
            match &mode {
                Mode::Resolve => {}
                _ if resolution_failed || (verified_nothing && matches!(mode, Mode::VerifySymbol(_))) => {
                    for q in &targets {
                        dv.statuses.insert(q.clone(), Status::Stale);
                    }
                }
                Mode::Verify => {
                    dv.catch_up(doc.version, &mut verify_diags, |(d, _)| d);
                    for q in &qnames {
                        let failed = verify_diags.iter().any(|(_, dq)| dq == q);
                        dv.statuses.insert(q.clone(), if failed { Status::Error } else { Status::Correct });
                    }
                    dv.verify = verify_diags;
                }
                Mode::VerifySymbol(q) => {
                    dv.catch_up(doc.version, &mut verify_diags, |(d, _)| d);
                    let failed = verify_diags.iter().any(|(_, dq)| dq == q);
                    dv.statuses.insert(q.clone(), if failed { Status::Error } else { Status::Correct });
                    dv.verify.retain(|(_, dq)| dq != q);
                    dv.verify.extend(verify_diags);
                }
            }
        }
        self.publish(&uri).await;
        if let Some(p) = progress {
            let msg = match counts {
                Some((ok, errors)) => format!("{ok} verified, {errors} errors"),
                None if resolution_failed => "resolution errors".to_string(),
                None => "done".to_string(),
            };
            p.end(msg).await;
        }
    }

    /// Re-checks open documents that see `path` through includes or a project.
    fn recheck_dependents(&self, path: &Path) {
        for doc in self.st().open_docs() {
            if doc.path.as_deref() == Some(path) {
                continue;
            }
            if self.st().scope_files(&doc).iter().any(|f| f.path.as_deref() == Some(path)) {
                self.schedule_on_change(doc.uri.clone());
            }
        }
    }

    fn doc_and_offset(&self, uri: &Url, pos: Position) -> Option<(Arc<FileData>, usize)> {
        let doc = self.st().doc(uri)?;
        let offset = doc.offset(pos, self.enc());
        Some((doc, offset))
    }

    /// Runs a workspace-wide query on the blocking thread pool.
    async fn blocking<T: Send + 'static>(&self, f: impl FnOnce(&State) -> T + Send + 'static) -> Result<T> {
        let inner = self.inner.clone();
        tokio::task::spawn_blocking(move || f(&inner.st)).await.map_err(|_| RpcError::internal_error())
    }
}

#[tower_lsp::async_trait]
impl LanguageServer for Backend {
    async fn initialize(&self, params: InitializeParams) -> Result<InitializeResult> {
        let caps = &params.capabilities;
        let utf8 = caps
            .general
            .as_ref()
            .and_then(|g| g.position_encodings.as_ref())
            .is_some_and(|encs| encs.contains(&PositionEncodingKind::UTF8));
        *self.st().encoding.write().unwrap() = if utf8 { Encoding::Utf8 } else { Encoding::Utf16 };
        {
            let mut c = self.inner.caps.write().unwrap();
            c.snippets = caps
                .text_document
                .as_ref()
                .and_then(|t| t.completion.as_ref())
                .and_then(|c| c.completion_item.as_ref())
                .and_then(|i| i.snippet_support)
                .unwrap_or(false);
            c.progress = caps.window.as_ref().and_then(|w| w.work_done_progress).unwrap_or(false);
            c.watch_files = caps
                .workspace
                .as_ref()
                .and_then(|w| w.did_change_watched_files.as_ref())
                .and_then(|d| d.dynamic_registration)
                .unwrap_or(false);
        }

        let mut roots: Vec<PathBuf> = params
            .workspace_folders
            .iter()
            .flatten()
            .filter_map(|f| f.uri.to_file_path().ok())
            .collect();
        #[allow(deprecated)]
        if roots.is_empty() {
            roots.extend(params.root_uri.as_ref().and_then(|u| u.to_file_path().ok()));
        }
        self.st().set_roots(roots);

        if let Some(opts) = &params.initialization_options {
            match Config::from_value(opts) {
                Some(Ok(cfg)) => *self.st().config.write().unwrap() = cfg,
                Some(Err(e)) => {
                    self.client.show_message(MessageType::WARNING, format!("dafny-lsp: invalid settings: {e}")).await;
                }
                None => {}
            }
        }

        Ok(InitializeResult {
            server_info: Some(ServerInfo { name: "dafny-lsp".into(), version: Some(env!("CARGO_PKG_VERSION").into()) }),
            capabilities: ServerCapabilities {
                position_encoding: Some(if utf8 { PositionEncodingKind::UTF8 } else { PositionEncodingKind::UTF16 }),
                text_document_sync: Some(TextDocumentSyncCapability::Options(TextDocumentSyncOptions {
                    open_close: Some(true),
                    change: Some(TextDocumentSyncKind::INCREMENTAL),
                    save: Some(TextDocumentSyncSaveOptions::SaveOptions(SaveOptions { include_text: Some(false) })),
                    ..Default::default()
                })),
                completion_provider: Some(CompletionOptions {
                    trigger_characters: Some(vec![".".into()]),
                    ..Default::default()
                }),
                hover_provider: Some(HoverProviderCapability::Simple(true)),
                signature_help_provider: Some(SignatureHelpOptions {
                    trigger_characters: Some(vec!["(".into(), ",".into()]),
                    retrigger_characters: Some(vec![",".into()]),
                    work_done_progress_options: Default::default(),
                }),
                definition_provider: Some(OneOf::Left(true)),
                references_provider: Some(OneOf::Left(true)),
                document_highlight_provider: Some(OneOf::Left(true)),
                document_symbol_provider: Some(OneOf::Left(true)),
                workspace_symbol_provider: Some(OneOf::Left(true)),
                rename_provider: Some(OneOf::Right(RenameOptions {
                    prepare_provider: Some(true),
                    work_done_progress_options: Default::default(),
                })),
                execute_command_provider: Some(ExecuteCommandOptions {
                    commands: COMMANDS.iter().map(|c| c.to_string()).collect(),
                    work_done_progress_options: Default::default(),
                }),
                ..Default::default()
            },
        })
    }

    async fn initialized(&self, _: InitializedParams) {
        if self.inner.caps.read().unwrap().watch_files {
            let options = serde_json::json!({
                "watchers": [{ "globPattern": "**/*.dfy" }, { "globPattern": "**/dfyconfig.toml" }]
            });
            let registration = Registration {
                id: "dafny-lsp-watch".into(),
                method: "workspace/didChangeWatchedFiles".into(),
                register_options: Some(options),
            };
            let _ = self.client.register_capability(vec![registration]).await;
        }
    }

    async fn shutdown(&self) -> Result<()> {
        for (_, slots) in self.inner.tasks.lock().unwrap().drain() {
            for handle in [slots.resolve, slots.verify].into_iter().flatten() {
                handle.abort();
            }
        }
        Ok(())
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        let td = params.text_document;
        let doc = self.st().put_doc(FileData::new(td.uri.clone(), Some(td.version), td.text, None, None));
        if let Some(path) = &doc.path {
            if !self.st().workspace_paths().contains(path) {
                self.st().invalidate_file_list();
            }
        }
        self.inner.verif.lock().unwrap().entry(td.uri.clone()).or_default();
        match self.st().config().verify_on {
            VerifyOn::Change | VerifyOn::Save => self.schedule(td.uri, Mode::Verify, Duration::ZERO),
            VerifyOn::Never => self.schedule(td.uri, Mode::Resolve, Duration::ZERO),
        }
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        let uri = params.text_document.uri;
        let Some(old) = self.st().doc(&uri) else { return };
        let version = params.text_document.version;
        let (new, spans) = apply_changes(&old, &params.content_changes, version, self.enc());
        self.st().put_doc(new);
        self.inner.verif.lock().unwrap().entry(uri.clone()).or_default().on_edit(&old, version, &spans);
        self.schedule_on_change(uri.clone());
        self.publish(&uri).await;
    }

    async fn did_save(&self, params: DidSaveTextDocumentParams) {
        let uri = params.text_document.uri;
        if let Ok(path) = uri.to_file_path() {
            self.st().invalidate_path(&path);
            self.recheck_dependents(&crate::state::normalize(&path));
        }
        if self.st().config().verify_on == VerifyOn::Save {
            self.schedule(uri, Mode::Verify, Duration::ZERO);
        }
    }

    async fn did_close(&self, params: DidCloseTextDocumentParams) {
        let uri = params.text_document.uri;
        self.cancel(&uri);
        self.inner.tasks.lock().unwrap().remove(&uri);
        self.inner.verif.lock().unwrap().remove(&uri);
        self.st().remove_doc(&uri);
        self.client.publish_diagnostics(uri, Vec::new(), None).await;
    }

    async fn did_change_configuration(&self, params: DidChangeConfigurationParams) {
        match Config::from_value(&params.settings) {
            Some(Ok(cfg)) => *self.st().config.write().unwrap() = cfg,
            Some(Err(e)) => {
                self.client.show_message(MessageType::WARNING, format!("dafny-lsp: invalid settings: {e}")).await;
            }
            None => {}
        }
    }

    async fn did_change_watched_files(&self, params: DidChangeWatchedFilesParams) {
        for change in params.changes {
            if let Ok(path) = change.uri.to_file_path() {
                self.st().invalidate_path(&path);
            }
        }
        self.st().invalidate_file_list();
    }

    async fn completion(&self, params: CompletionParams) -> Result<Option<CompletionResponse>> {
        let tdp = params.text_document_position;
        let Some((doc, offset)) = self.doc_and_offset(&tdp.text_document.uri, tdp.position) else { return Ok(None) };
        let doc = typing_view(doc, offset);
        let snippets = self.inner.caps.read().unwrap().snippets;
        let items = self.blocking(move |st| completion::complete(st, &doc, offset, snippets)).await?;
        Ok(Some(CompletionResponse::Array(items)))
    }

    async fn hover(&self, params: HoverParams) -> Result<Option<Hover>> {
        let tdp = params.text_document_position_params;
        let Some((doc, offset)) = self.doc_and_offset(&tdp.text_document.uri, tdp.position) else { return Ok(None) };
        let enc = self.enc();
        self.blocking(move |st| {
            let ident = crate::syntax::identifier_at(doc.root(), offset)?;
            let target = analysis::resolve_ident(st, &doc, ident).into_iter().next()?;
            Some(Hover {
                contents: HoverContents::Markup(MarkupContent {
                    kind: MarkupKind::Markdown,
                    value: info::hover_markdown(st, &target, &doc),
                }),
                range: Some(doc.range(&ident.byte_range(), enc)),
            })
        })
        .await
    }

    async fn signature_help(&self, params: SignatureHelpParams) -> Result<Option<SignatureHelp>> {
        let tdp = params.text_document_position_params;
        let Some((doc, offset)) = self.doc_and_offset(&tdp.text_document.uri, tdp.position) else { return Ok(None) };
        let doc = typing_view(doc, offset);
        self.blocking(move |st| info::signature_help(st, &doc, offset)).await
    }

    async fn goto_definition(&self, params: GotoDefinitionParams) -> Result<Option<GotoDefinitionResponse>> {
        let tdp = params.text_document_position_params;
        let Some((doc, offset)) = self.doc_and_offset(&tdp.text_document.uri, tdp.position) else { return Ok(None) };
        let enc = self.enc();
        let locs = self.blocking(move |st| navigation::definition(st, &doc, offset, enc)).await?;
        Ok(match locs.len() {
            0 => None,
            1 => Some(GotoDefinitionResponse::Scalar(locs.into_iter().next().unwrap())),
            _ => Some(GotoDefinitionResponse::Array(locs)),
        })
    }

    async fn references(&self, params: ReferenceParams) -> Result<Option<Vec<Location>>> {
        let tdp = params.text_document_position;
        let Some((doc, offset)) = self.doc_and_offset(&tdp.text_document.uri, tdp.position) else { return Ok(None) };
        let enc = self.enc();
        let include_decl = params.context.include_declaration;
        let locs = self.blocking(move |st| navigation::references(st, &doc, offset, include_decl, enc)).await?;
        Ok(Some(locs))
    }

    async fn document_highlight(&self, params: DocumentHighlightParams) -> Result<Option<Vec<DocumentHighlight>>> {
        let tdp = params.text_document_position_params;
        let Some((doc, offset)) = self.doc_and_offset(&tdp.text_document.uri, tdp.position) else { return Ok(None) };
        let enc = self.enc();
        let hl = self.blocking(move |st| navigation::highlights(st, &doc, offset, enc)).await?;
        Ok(Some(hl))
    }

    async fn prepare_rename(&self, params: TextDocumentPositionParams) -> Result<Option<PrepareRenameResponse>> {
        let Some((doc, offset)) = self.doc_and_offset(&params.text_document.uri, params.position) else { return Ok(None) };
        let enc = self.enc();
        let range = self.blocking(move |st| navigation::prepare_rename(st, &doc, offset, enc)).await?;
        Ok(range.map(PrepareRenameResponse::Range))
    }

    async fn rename(&self, params: RenameParams) -> Result<Option<WorkspaceEdit>> {
        let tdp = params.text_document_position;
        let Some((doc, offset)) = self.doc_and_offset(&tdp.text_document.uri, tdp.position) else { return Ok(None) };
        let enc = self.enc();
        let new_name = params.new_name;
        self.blocking(move |st| navigation::rename(st, &doc, offset, &new_name, enc))
            .await?
            .map_err(RpcError::invalid_params)
    }

    async fn document_symbol(&self, params: DocumentSymbolParams) -> Result<Option<DocumentSymbolResponse>> {
        let Some(doc) = self.st().doc(&params.text_document.uri) else { return Ok(None) };
        Ok(Some(DocumentSymbolResponse::Nested(navigation::document_symbols(&doc, self.enc()))))
    }

    async fn symbol(&self, params: WorkspaceSymbolParams) -> Result<Option<Vec<SymbolInformation>>> {
        let enc = self.enc();
        let query = params.query;
        Ok(Some(self.blocking(move |st| navigation::workspace_symbols(st, &query, enc)).await?))
    }

    async fn execute_command(&self, params: ExecuteCommandParams) -> Result<Option<Value>> {
        let args = params.arguments;
        let Some(uri) = uri_arg(&args, 0) else {
            return Err(RpcError::invalid_params("expected a document URI as the first argument"));
        };
        if self.st().doc(&uri).is_none() {
            return Err(RpcError::invalid_params(format!("{uri} is not open")));
        }
        match params.command.as_str() {
            "dafny-lsp.verify" => self.schedule(uri, Mode::Verify, Duration::ZERO),
            "dafny-lsp.verifySymbol" => {
                let Some(q) = args.get(1).and_then(Value::as_str) else {
                    return Err(RpcError::invalid_params("expected a symbol name as the second argument"));
                };
                self.schedule(uri, Mode::VerifySymbol(q.to_string()), Duration::ZERO);
            }
            "dafny-lsp.verifyAt" => {
                let pos: Position = args
                    .get(1)
                    .and_then(|v| serde_json::from_value(v.clone()).ok())
                    .ok_or_else(|| RpcError::invalid_params("expected a position as the second argument"))?;
                let (doc, offset) = self.doc_and_offset(&uri, pos).expect("checked above");
                let mode = match verify::symbol_at(&doc.syms.symbols, offset) {
                    Some(s) => Mode::VerifySymbol(s.qname.clone()),
                    None => Mode::Verify,
                };
                self.schedule(uri, mode, Duration::ZERO);
            }
            "dafny-lsp.cancel" => {
                if let Some(handle) = self.inner.tasks.lock().unwrap().get_mut(&uri).and_then(|s| s.verify.take()) {
                    handle.abort();
                }
                {
                    let mut verif = self.inner.verif.lock().unwrap();
                    let dv = verif.entry(uri.clone()).or_default();
                    let pending: HashSet<String> = dv
                        .statuses
                        .iter()
                        .filter(|(_, s)| matches!(s, Status::Queued | Status::Running))
                        .map(|(q, _)| q.clone())
                        .collect();
                    for q in pending {
                        dv.statuses.insert(q, Status::Stale);
                    }
                }
                self.publish(&uri).await;
            }
            other => return Err(RpcError::invalid_params(format!("unknown command {other}"))),
        }
        Ok(None)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn maps_progress_names() {
        let qnames = vec!["Gen".to_string(), "M.Abs".to_string()];
        assert_eq!(map_name("Gen.MoveNext", &qnames).as_deref(), Some("Gen"));
        assert_eq!(map_name("M.Abs", &qnames).as_deref(), Some("M.Abs"));
        assert_eq!(map_name("Other", &qnames), None);
        assert_eq!(parse_summary("Dafny program verifier finished with 2 verified, 1 error"), Some((2, 1)));
    }
}
