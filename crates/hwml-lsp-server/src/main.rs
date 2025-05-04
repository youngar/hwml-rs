use crossbeam_channel::{Receiver, Sender};
use hwml_db::{
    db::{File, HwmlDatabase},
    *,
};
use lsp_server::{
    Connection, Message, Notification as TNotification, Request as TRequest, RequestId, Response,
};
use lsp_types::{
    notification::*, request::*, Diagnostic, DidChangeTextDocumentParams,
    DidOpenTextDocumentParams, InitializeParams, OneOf, Position, PublishDiagnosticsParams, Range,
    SaveOptions, ServerCapabilities, TextDocumentContentChangeEvent, TextDocumentSyncCapability,
    TextDocumentSyncKind, TextDocumentSyncOptions, Uri,
};
use salsa::Setter;
use std::{collections::HashMap, error::Error};

struct DocumentInfo {
    version: Option<i32>,
    file: db::File,
}

struct Server {
    sender: Sender<Message>,
    documents: HashMap<Uri, DocumentInfo>,
    db: HwmlDatabase,
}

impl Server {
    fn new(sender: Sender<Message>) -> Self {
        Self {
            sender,
            documents: HashMap::new(),
            db: HwmlDatabase::new(),
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

    fn handle_did_open_text_document(&mut self, params: DidOpenTextDocumentParams) {
        let text_document = params.text_document;
        let uri = text_document.uri;
        let text = text_document.text;
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

    fn handle_did_change_text_document(&mut self, params: DidChangeTextDocumentParams) {
        let text_document = params.text_document;
        let uri = text_document.uri;
        let edits = params.content_changes;
        if let Some(document) = self.documents.get(&uri) {
            Self::apply_document_edits(&mut self.db, document, edits.as_slice());
            self.compile_file(&self.db, &uri, document);
        }
    }

    fn handle_notification<F, P>(&mut self, n: TNotification, f: F)
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

    fn handle_notifications(
        &mut self,
        n: TNotification,
    ) -> Result<(), Box<dyn Error + Sync + Send>> {
        match n.method.as_str() {
            DidOpenTextDocument::METHOD => {
                self.handle_notification(n, Self::handle_did_open_text_document)
            }
            DidChangeTextDocument::METHOD => {
                self.handle_notification(n, Self::handle_did_change_text_document)
            }
            _ => {
                eprintln!("unhandled notification: {n:?}");
                ()
            }
        };
        Ok(())
    }

    fn handle_requests(&self, r: TRequest) -> Result<(), Box<dyn Error + Sync + Send>> {
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

    fn handle_responses(&self, _response: Response) -> Result<(), Box<dyn Error + Sync + Send>> {
        Ok(())
    }

    fn send(&self, message: lsp_server::Message) {
        self.sender.send(message).unwrap();
    }

    pub(crate) fn send_notification<N>(&self, params: N::Params)
    where
        N: Notification,
    {
        let n = lsp_server::Notification::new(N::METHOD.to_owned(), params);
        self.send(n.into());
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

    fn handle_message(&mut self, msg: Message) -> Result<(), Box<dyn Error + Sync + Send>> {
        match msg {
            Message::Request(r) => self.handle_requests(r),
            Message::Response(r) => self.handle_responses(r),
            Message::Notification(n) => self.handle_notifications(n),
        }
    }

    fn run(&mut self, receiver: Receiver<Message>) -> Result<(), Box<dyn Error + Sync + Send>> {
        for msg in receiver {
            self.handle_message(msg)?;
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
