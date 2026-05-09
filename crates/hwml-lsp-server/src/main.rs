use crossbeam_channel::{Receiver, Sender};
use hwml_db::db::HwmlDatabase;
use hwml_vfs::LspVfs;
use lsp_server::{
    Connection, Message, Notification as TNotification, Request as TRequest, RequestId,
    Response as TResponse,
};
use lsp_types::{
    notification::*, request::*, Diagnostic, DidChangeTextDocumentParams,
    DidOpenTextDocumentParams, InitializeParams, OneOf, PublishDiagnosticsParams,
    SaveOptions, ServerCapabilities, TextDocumentContentChangeEvent, TextDocumentSyncCapability,
    TextDocumentSyncKind, TextDocumentSyncOptions, Uri,
};
use std::{error::Error, path::PathBuf, time::Instant};

pub(crate) type ResponseHandler = fn(&mut Server, TResponse);
type ReqQueue = lsp_server::ReqQueue<(String, Instant), ResponseHandler>;

struct Server {
    sender: Sender<Message>,
    vfs: LspVfs,
    db: HwmlDatabase,
    req_queue: ReqQueue,
    /// Workspace root directory (from LSP initialization)
    workspace_root: Option<PathBuf>,
    /// Path to hwml.toml manifest (if found)
    workspace_manifest: Option<PathBuf>,
}

impl Server {
    fn new(sender: Sender<Message>, workspace_root: Option<PathBuf>) -> Self {
        Self {
            sender,
            vfs: LspVfs::new(),
            db: HwmlDatabase::new(),
            req_queue: ReqQueue::default(),
            workspace_root,
            workspace_manifest: None,
        }
    }

    /// Find hwml.toml in the workspace root directory
    fn find_workspace_manifest(root: &PathBuf) -> Option<PathBuf> {
        let manifest = root.join("hwml.toml");
        if manifest.exists() {
            Some(manifest)
        } else {
            None
        }
    }

    /// Initialize workspace by finding and loading hwml.toml
    fn initialize_workspace(&mut self) {
        if let Some(ref root) = self.workspace_root {
            if let Some(manifest) = Self::find_workspace_manifest(root) {
                eprintln!("Found workspace manifest: {}", manifest.display());
                self.workspace_manifest = Some(manifest.clone());
                self.reload_workspace();
            } else {
                eprintln!("No hwml.toml found in workspace root: {}", root.display());
            }
        } else {
            eprintln!("No workspace root provided");
        }
    }

    /// Reload workspace declarations from hwml.toml
    /// This is called on initialization and when files change
    ///
    /// Note: The actual workspace_declarations() call would happen here,
    /// but it returns StubTable<'db> which we can't easily store.
    /// Instead, we'll call workspace_declarations() on-demand when
    /// implementing language features like go-to-definition.
    fn reload_workspace(&mut self) {
        if let Some(ref manifest) = self.workspace_manifest {
            eprintln!("Workspace manifest ready: {}", manifest.display());
            eprintln!("  (workspace_declarations will be loaded on-demand for language features)");
        }
    }

    fn server_capabilities() -> ServerCapabilities {
        ServerCapabilities {
            definition_provider: Some(OneOf::Left(true)),
            text_document_sync: Some(TextDocumentSyncCapability::Options(
                TextDocumentSyncOptions {
                    open_close: Some(true),
                    change: Some(TextDocumentSyncKind::INCREMENTAL),
                    will_save: None,
                    will_save_wait_until: None,
                    save: Some(SaveOptions::default().into()),
                },
            )),
            ..Default::default()
        }
    }

    fn apply_document_edits(
        vfs: &mut LspVfs,
        db: &mut HwmlDatabase,
        uri: &Uri,
        edits: &[TextDocumentContentChangeEvent],
    ) {
        // Get the current file from VFS
        let Some(file) = vfs.get_by_uri(uri) else {
            eprintln!("Warning: Trying to edit unopened document: {uri:?}");
            return;
        };

        for edit in edits {
            if let Some(range) = edit.range {
                // Incremental edit - apply to specific range
                let mut text = file.text(db).to_string();
                let line_info = hwml_db::db::get_line_info(db, file);
                let start =
                    line_info.offset((range.start.line as usize, range.start.character as usize));
                let end = line_info.offset((range.end.line as usize, range.end.character as usize));
                text.replace_range(start..end, edit.text.as_str());

                // Update via VFS (triggers Salsa invalidation)
                vfs.update_document(db, uri, text)
                    .expect("Failed to update document");
            } else {
                // Whole document replace
                vfs.update_document(db, uri, edit.text.clone())
                    .expect("Failed to update document");
            }
        }
    }

    fn recv_did_open_text_document(&mut self, params: DidOpenTextDocumentParams) {
        let text_document = params.text_document;
        let uri = text_document.uri;
        let text: String = text_document.text;

        // Convert URI to file path (simple conversion for now)
        // URI format: "file:///path/to/file.hwml"
        let path = PathBuf::from(uri.as_str().trim_start_matches("file://"));

        // Open document in VFS
        let file = self.vfs.open_document(&self.db, uri.clone(), path, text);

        // Compile the newly opened file
        self.compile_file(&self.db, &uri, file);

        // Reload workspace declarations (file opening triggers Salsa invalidation)
        if self.workspace_manifest.is_some() {
            self.reload_workspace();
        }
    }

    fn recv_did_change_text_document(&mut self, params: DidChangeTextDocumentParams) {
        let text_document = params.text_document;
        let uri = text_document.uri;
        let edits = params.content_changes;

        // Apply edits via VFS
        Self::apply_document_edits(&mut self.vfs, &mut self.db, &uri, edits.as_slice());

        // Recompile after changes
        if let Some(file) = self.vfs.get_by_uri(&uri) {
            self.compile_file(&self.db, &uri, file);
        }

        // Reload workspace declarations (edits trigger Salsa invalidation)
        if self.workspace_manifest.is_some() {
            self.reload_workspace();
        }
    }

    fn on_notification<F, P>(&mut self, n: TNotification, f: F)
    where
        F: FnOnce(&mut Server, P) -> (),
        P: serde::de::DeserializeOwned,
    {
        match serde_json::from_value(n.params) {
            Ok(params) => f(self, params),
            Err(e) => {
                eprintln!("error decoding params for request: {e}");
            }
        }
    }

    fn recv_notification(&mut self, n: TNotification) -> Result<(), Box<dyn Error + Sync + Send>> {
        match n.method.as_str() {
            DidOpenTextDocument::METHOD => {
                self.on_notification(n, Self::recv_did_open_text_document)
            }
            DidChangeTextDocument::METHOD => {
                self.on_notification(n, Self::recv_did_change_text_document)
            }
            _ => {
                eprintln!("unhandled notification: {n:?}");
                ()
            }
        };
        Ok(())
    }

    fn on_request<F, P>(&mut self, n: TRequest, f: F)
    where
        F: FnOnce(&mut Server, RequestId, P) -> (),
        P: serde::de::DeserializeOwned,
    {
        match serde_json::from_value(n.params) {
            Ok(params) => f(self, n.id, params),
            Err(e) => {
                eprintln!("error decoding params for request: {e}");
            }
        }
    }

    fn recv_request(&mut self, r: TRequest) -> Result<(), Box<dyn Error + Sync + Send>> {
        let now = Instant::now();
        // Register this incomming request.
        self.req_queue
            .incoming
            .register(r.id.clone(), (r.method.clone(), now));
        // Dispatch to the handler.
        match r.method.as_str() {
            Initialize::METHOD => (),
            Shutdown::METHOD => (),
            _ => {
                eprintln!("unhandled request: {r:?}");
                ()
            }
        }
        Ok(())
    }

    fn recv_response(&mut self, r: TResponse) -> Result<(), Box<dyn Error + Sync + Send>> {
        let handler = self
            .req_queue
            .outgoing
            .complete(r.id.clone())
            .expect("received response for unknown request");
        handler(self, r);
        Ok(())
    }

    fn recv_message(&mut self, msg: Message) -> Result<(), Box<dyn Error + Sync + Send>> {
        match msg {
            Message::Notification(n) => self.recv_notification(n),
            Message::Request(r) => self.recv_request(r),
            Message::Response(r) => self.recv_response(r),
        }
    }

    pub(crate) fn send_notification<N: lsp_types::notification::Notification>(
        &self,
        params: N::Params,
    ) {
        let not = lsp_server::Notification::new(N::METHOD.to_owned(), params);
        self.send(not.into());
    }

    pub(crate) fn send_request<R: lsp_types::request::Request>(
        &mut self,
        params: R::Params,
        handler: ResponseHandler,
    ) {
        let request = self
            .req_queue
            .outgoing
            .register(R::METHOD.to_owned(), params, handler);
        self.send(request.into());
    }

    pub(crate) fn is_completed(&self, request: &TRequest) -> bool {
        self.req_queue.incoming.is_completed(&request.id)
    }

    fn send_response(&mut self, response: TResponse) -> Result<(), Box<dyn Error + Sync + Send>> {
        if let Some((method, start)) = self.req_queue.incoming.complete(&response.id) {
            let duration = start.elapsed();
            self.send(response.into());
        }
        Ok(())
    }

    pub(crate) fn send_cancel(&mut self, request_id: RequestId) {
        if let Some(response) = self.req_queue.incoming.cancel(request_id) {
            self.send(response.into());
        }
    }

    fn send(&self, message: lsp_server::Message) {
        self.sender.send(message).unwrap();
    }

    fn send_diagnostics(&self, uri: Uri, diagnostics: Vec<Diagnostic>) {
        let version = None;
        self.send_notification::<PublishDiagnostics>(PublishDiagnosticsParams {
            uri,
            diagnostics,
            version,
        });
    }

    fn compile_file(&self, db: &HwmlDatabase, uri: &Uri, file: hwml_db::db::SourceFile) {
        // Collect parse errors from Salsa query
        let diagnostics = hwml_db::diagnostics::file_diagnostics(db, file);
        let mut all_diagnostics: Vec<hwml_diagnostic::Diagnostic> = diagnostics.iter().cloned().collect();

        // Also collect elaboration errors (type checking)
        // This is done outside the Salsa query because elaboration requires &HwmlDatabase
        let parse_result = hwml_db::workspace::parse_surface_program_with_errors(db, file);
        if let Some(ref program) = parse_result.program {
            // Create source identifier
            let library_name_word = hwml_core::Word::new(db, file.library_name(db).as_str());
            let path_str = file.path(db).to_str().unwrap_or("unknown");
            let path_word = hwml_core::Word::new(db, path_str);
            let source_file_id = hwml_core::SourceFileId::new(db, library_name_word, path_word);
            let source_info = hwml_core::SourceInfo::File(source_file_id);
            let file_source = hwml_core::Source::new(db, source_info);

            // Run elaboration
            let mut global = hwml_core::val::GlobalEnv::new();
            let elab_result = hwml_elab::program::elab_program_with_source(db, &mut global, program, Some(file_source));

            // Convert elaboration errors to diagnostics
            let text = file.text(db);
            for elab_error in &elab_result.errors {
                if let Some(diag) = hwml_db::diagnostics::convert_elab_error_to_diagnostic(db, file, elab_error) {
                    all_diagnostics.push(diag);
                }
            }
        }

        let lsp_diagnostics: Vec<Diagnostic> = all_diagnostics
            .iter()
            .map(|diag| hwml_diagnostic::lsp::diagnostic_to_lsp(diag, uri, Some("hwml")))
            .collect();

        self.send_diagnostics(uri.clone(), lsp_diagnostics);
    }

    fn run(&mut self, receiver: Receiver<Message>) -> Result<(), Box<dyn Error + Sync + Send>> {
        for msg in receiver {
            self.recv_message(msg)?;
        }
        Ok(())
    }
}

fn main() -> Result<(), Box<dyn Error + Sync + Send>> {
    eprintln!("STARTING");

    let (connection, io_threads) = Connection::stdio();

    let server_capabilities = serde_json::to_value(Server::server_capabilities()).unwrap();
    let initialization_params = match connection.initialize(server_capabilities) {
        Ok(it) => it,
        Err(e) => {
            return Err(e.into());
        }
    };

    let params: InitializeParams = serde_json::from_value(initialization_params)?;

    // Extract workspace root from initialization parameters
    // Use workspace_folders if available (modern), otherwise fall back to root_uri
    let workspace_root = params
        .workspace_folders
        .as_ref()
        .and_then(|folders| folders.first())
        .and_then(|folder| {
            // Convert URI to file path
            // URI format: "file:///path/to/workspace"
            let uri_str = folder.uri.as_str();
            if uri_str.starts_with("file://") {
                Some(PathBuf::from(&uri_str[7..])) // Skip "file://"
            } else {
                None
            }
        })
        .or_else(|| {
            // Fallback to root_uri (older LSP spec)
            #[allow(deprecated)]
            params.root_uri.as_ref().and_then(|uri| {
                let uri_str = uri.as_str();
                if uri_str.starts_with("file://") {
                    Some(PathBuf::from(&uri_str[7..])) // Skip "file://"
                } else {
                    None
                }
            })
        })
        .or_else(|| {
            // Last fallback to root_path (very old LSP spec)
            #[allow(deprecated)]
            params.root_path.as_ref().map(PathBuf::from)
        });

    if let Some(ref root) = workspace_root {
        eprintln!("LSP workspace root: {}", root.display());
    } else {
        eprintln!("LSP started without workspace root");
    }

    let mut server = Server::new(connection.sender, workspace_root);

    // Initialize workspace (find and load hwml.toml)
    server.initialize_workspace();

    server.run(connection.receiver)?;

    // Run the server and wait for the two threads to end (typically by trigger LSP Exit event).
    io_threads.join()?;

    // Shut down gracefully.
    eprintln!("shutting down server");
    Ok(())
}
