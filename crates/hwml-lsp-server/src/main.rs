use crossbeam_channel::{Receiver, Sender};
use hwml_db::{
    db::{File, HwmlDatabase},
    *,
};
use lsp_server::{
    Connection, Message, Notification as TNotification, Request as TRequest, RequestId,
    Response as TResponse,
};
use lsp_types::{
    notification::*, request::*, Diagnostic, DidChangeTextDocumentParams,
    DidOpenTextDocumentParams, InitializeParams, OneOf, Position, PublishDiagnosticsParams, Range,
    SaveOptions, ServerCapabilities, TextDocumentContentChangeEvent, TextDocumentSyncCapability,
    TextDocumentSyncKind, TextDocumentSyncOptions, Uri,
};
use salsa::Setter;
use std::{collections::HashMap, error::Error, time::Instant};

struct DocumentInfo {
    version: Option<i32>,
    file: db::File,
}

pub(crate) type ResponseHandler = fn(&mut Server, TResponse);
type ReqQueue = lsp_server::ReqQueue<(String, Instant), ResponseHandler>;

struct Server {
    sender: Sender<Message>,
    documents: HashMap<Uri, DocumentInfo>,
    db: HwmlDatabase,
    req_queue: ReqQueue,
}

impl Server {
    fn new(sender: Sender<Message>) -> Self {
        Self {
            sender,
            documents: HashMap::new(),
            db: HwmlDatabase::new(),
            req_queue: ReqQueue::default(),
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
        db: &mut HwmlDatabase,
        document: &DocumentInfo,
        edits: &[TextDocumentContentChangeEvent],
    ) {
        let file = document.file;
        for edit in edits {
            if let Some(range) = edit.range {
                let mut text = file.text(db);
                let line_info = db::get_line_info(db, file);
                let start =
                    line_info.offset((range.start.line as usize, range.start.character as usize));
                let end = line_info.offset((range.end.line as usize, range.end.character as usize));
                text.replace_range(start..end, edit.text.as_str());
                file.set_text(db).to(text);
            } else {
                // Whole document replace.
                file.set_text(db).to(edit.text.clone());
            }
        }
    }

    fn recv_did_open_text_document(&mut self, params: DidOpenTextDocumentParams) {
        let text_document = params.text_document;
        let uri = text_document.uri;
        let text: String = text_document.text;
        let file = File::new(&self.db, text);
        self.documents.insert(
            uri.clone(),
            DocumentInfo {
                file,
                version: None,
            },
        );
        let document = self.documents.get(&uri).unwrap();
        self.compile_file(&self.db, &uri, &document);
    }

    fn recv_did_change_text_document(&mut self, params: DidChangeTextDocumentParams) {
        let text_document = params.text_document;
        let uri = text_document.uri;
        let edits = params.content_changes;
        if let Some(document) = self.documents.get(&uri) {
            Self::apply_document_edits(&mut self.db, document, edits.as_slice());
            self.compile_file(&self.db, &uri, document);
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
        if let Some((_method, _start)) = self.req_queue.incoming.complete(&response.id) {
            let _duration = _start.elapsed();
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

    fn to_position((line, column): (usize, usize)) -> Position {
        Position {
            line: line as u32,
            character: column as u32,
        }
    }

    fn compile_file(&self, db: &HwmlDatabase, uri: &Uri, document: &DocumentInfo) {
        let _program = db::parse_program(&*db, document.file);
        let diagnostics = db::parse_program::accumulated::<db::Diagnostics>(db, document.file);
        if diagnostics.len() > 0 {
            let line_info = db::get_line_info(db, document.file);
            let lsp_diagnostics = diagnostics
                .into_iter()
                .map(|diagnostic| {
                    let start = Self::to_position(line_info.loc(diagnostic.0.span.start));
                    let end = Self::to_position(line_info.loc(diagnostic.0.span.start));
                    Diagnostic {
                        range: Range { start, end },
                        message: diagnostic.0.message,
                        ..Default::default()
                    }
                })
                .collect::<Vec<_>>();
            self.send_diagnostics(uri.clone(), lsp_diagnostics);
        }
        // If there are no diagnostics, clear them for this file.
        self.send_diagnostics(uri.clone(), vec![]);
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

    let _params: InitializeParams = serde_json::from_value(initialization_params)?;

    let mut server = Server::new(connection.sender);
    server.run(connection.receiver)?;

    // Run the server and wait for the two threads to end (typically by trigger LSP Exit event).
    io_threads.join()?;

    // Shut down gracefully.
    eprintln!("shutting down server");
    Ok(())
}
