#![allow(unreachable_patterns)]

use dashmap::{DashMap, Entry};
use eyre::{Context, Result};
use lalrpop_util::lexer::Token;
use lalrpop_util::ParseError;
use lalrpop_util::ParseError::*;
use std::convert::From;
use std::path::PathBuf;
use std::sync::{Arc, Mutex};

use crate::ir::Program;
use hwml_support::line_info::LineInfo;

#[salsa::input]
pub struct File {
    pub text: String,
}

#[salsa::db]
#[derive(Clone)]
pub struct HwmlDatabase {
    storage: salsa::Storage<Self>,
    // Maps a Url to its current contents.
    files: DashMap<PathBuf, File>,
    // The logs are only used for testing and demonstrating reuse:
    logs: Arc<Mutex<Option<Vec<String>>>>,
}

impl HwmlDatabase {
    /// Enable logging of each salsa event.
    #[cfg(test)]
    pub fn enable_logging(&self) {
        let mut logs = self.logs.lock().unwrap();
        if logs.is_none() {
            *logs = Some(vec![]);
        }
    }

    #[cfg(test)]
    pub fn take_logs(&self) -> Vec<String> {
        let mut logs = self.logs.lock().unwrap();
        if let Some(logs) = &mut *logs {
            std::mem::take(logs)
        } else {
            vec![]
        }
    }

    pub fn new() -> Self {
        Self {
            storage: Default::default(),
            logs: Default::default(),
            files: DashMap::new(),
        }
    }

    pub fn input(&self, path: PathBuf) -> Result<File> {
        let path = path
            .canonicalize()
            .wrap_err_with(|| format!("Failed to read {}", path.display()))?;
        Ok(match self.files.entry(path.clone()) {
            // If the file already exists in our cache then just return it.
            Entry::Occupied(entry) => *entry.get(),
            // If we haven't read this file yet set up the watch, read the
            // contents, store it in the cache, and return it.
            Entry::Vacant(entry) => {
                let contents = std::fs::read_to_string(&path)
                    .wrap_err_with(|| format!("Failed to read {}", path.display()))?;
                *entry.insert(File::new(self, contents))
            }
        })
    }
}

#[salsa::db]
impl salsa::Database for HwmlDatabase {
    fn salsa_event(&self, event: &dyn Fn() -> salsa::Event) {
        let event = event();
        eprintln!("Event: {event:?}");
        // Log interesting events, if logging is enabled
        if let Some(logs) = &mut *self.logs.lock().unwrap() {
            // only log interesting events
            if let salsa::EventKind::WillExecute { .. } = event.kind {
                logs.push(format!("Event: {event:?}"));
            }
        }
    }
}

// Diagnostics
pub struct FileLineColLoc {}

#[derive(Debug, Clone)]
pub struct Diagnostic {
    pub message: String,
    pub span: std::ops::Range<usize>,
}

#[salsa::accumulator]
pub struct Diagnostics(pub Diagnostic);

#[salsa::tracked]
pub fn gather_diagnostics(db: &dyn salsa::Database, text_doc: File) {
    compile(db, text_doc);
}

#[salsa::tracked]
pub fn compile(db: &dyn salsa::Database, text_doc: File) {
    let _program = parse_program(db, text_doc);
}

impl From<&ParseError<usize, Token<'_>, &str>> for Diagnostic {
    fn from(error: &ParseError<usize, Token<'_>, &str>) -> Self {
        match error {
            User { ref error } => Diagnostic {
                message: error.to_string(),
                span: 0..0,
            },
            InvalidToken { ref location } => Diagnostic {
                message: "invalid token".to_string(),
                span: *location..*location,
            },
            UnrecognizedEof {
                ref location,
                expected: _,
            } => Diagnostic {
                message: "unrecognized end of file".to_string(),
                span: *location..*location,
            },
            UnrecognizedToken {
                token: (ref start, ref token, ref end),
                expected: _,
            } => Diagnostic {
                message: format!("unrecognized token: {token:?}"),
                span: *start..*end,
            },
            ExtraToken {
                token: (ref start, ref token, ref end),
            } => Diagnostic {
                message: format!("extra token: {token:?}"),
                span: *start..*end,
            },
        }
    }
}

#[salsa::tracked]
pub fn get_line_info(db: &dyn salsa::Database, source_program: File) -> LineInfo {
    LineInfo::from_bytes(source_program.text(db).as_bytes())
}

#[salsa::tracked]
pub fn parse_program(db: &dyn salsa::Database, _source_program: File) -> Program<'_> {
    // let mut errors = Vec::new();
    // let text = source_program.text(db);
    // let result = hwml_parser::grammar::ProgramParser::new().parse(&mut errors, &text);
    // if let Err(ref error) = result {
    //     Diagnostics(error.into()).accumulate(db);
    // }
    // for error in errors {
    //     Diagnostics((&error.error).into()).accumulate(db);
    // }
    // if let Result::Ok(_) = result {
    //     //Program::new(db, program.statements)
    //     Program::new(db, vec![])
    // } else {
    //     Program::new(db, vec![])
    // }
    Program::new(db, vec![])
}
