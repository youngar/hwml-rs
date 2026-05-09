#![allow(unreachable_patterns)]

use lalrpop_util::lexer::Token;
use lalrpop_util::ParseError;
use lalrpop_util::ParseError::*;
use std::collections::HashMap;
use std::convert::From;
use std::path::PathBuf;
use std::sync::{Arc, Mutex};

use crate::ir::Program;
use hwml_support::line_info::LineInfo;

#[salsa::input]
pub struct SourceFile {
    /// Canonical absolute path to the file
    #[return_ref]
    pub path: PathBuf,

    /// File content as UTF-8 string
    #[return_ref] // Critical: avoid cloning strings on every query
    pub text: String,

    /// Library name for this file (used to create SourceFileId)
    #[return_ref]
    pub library_name: String,
}

impl SourceFile {
    /// Get the SourceFileId for this file (computed on demand, interned)
    pub fn file_id<'db>(&self, db: &'db dyn salsa::Database) -> hwml_core::SourceFileId<'db> {
        let canonical_path_str = self.path(db).to_str().unwrap_or_else(|| {
            eprintln!(
                "Warning: Non-UTF8 path encountered: {:?} (using 'unknown' as fallback)",
                self.path(db)
            );
            "unknown"
        });
        let canonical_path_word = hwml_core::Word::new(db, canonical_path_str);
        let library_name_word = hwml_core::Word::new(db, self.library_name(db).as_str());
        hwml_core::SourceFileId::new(db, library_name_word, canonical_path_word)
    }
}

/// VfsFileMap tracks all known files in the workspace.
/// This is a Salsa input that gets updated when files are added/removed.
/// Module resolution queries use this for pure lookup (no IO).
#[salsa::input]
pub struct VfsFileMap {
    /// Map of canonical PathBuf → SourceFile
    /// Using Arc for cheap cloning when updating
    /// Note: We use PathBuf keys internally because Salsa input structs can't use
    /// interned types with lifetimes. Lookups by SourceFileId are supported via helper methods.
    #[return_ref]
    pub files: Arc<HashMap<PathBuf, SourceFile>>,
}

impl VfsFileMap {
    /// Lookup a SourceFile by its SourceFileId
    ///
    /// Note: This is a convenience method. The VfsFileMap internally uses PathBuf keys,
    /// so we convert the SourceFileId to a PathBuf for lookup.
    pub fn get_by_file_id<'db>(
        &self,
        db: &'db dyn salsa::Database,
        file_id: hwml_core::SourceFileId<'db>,
    ) -> Option<SourceFile> {
        // Convert SourceFileId to PathBuf
        let canonical_path_str: &str = file_id.canonical_path(db).text(db);
        let path_buf = PathBuf::from(canonical_path_str);
        self.files(db).get(&path_buf).copied()
    }
}

/// Manifest path as a Salsa input for workspace loading.
/// This allows Salsa to track when the manifest changes.
#[salsa::input]
pub struct ManifestPath {
    /// Canonical absolute path to hwml.toml
    #[return_ref]
    pub path: PathBuf,
}

#[salsa::db]
#[derive(Clone)]
pub struct HwmlDatabase {
    storage: salsa::Storage<Self>,
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
        }
    }
}

#[salsa::db]
impl salsa::Database for HwmlDatabase {
    fn salsa_event(&self, event: &dyn Fn() -> salsa::Event) {
        let event = event();
        // eprintln!("Event: {event:?}");  // Disabled: too noisy for production
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
pub fn gather_diagnostics(db: &dyn salsa::Database, text_doc: SourceFile) {
    compile(db, text_doc);
}

#[salsa::tracked]
pub fn compile(db: &dyn salsa::Database, text_doc: SourceFile) {
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
pub fn get_line_info(db: &dyn salsa::Database, source_program: SourceFile) -> LineInfo {
    LineInfo::from_bytes(source_program.text(db).as_bytes())
}

#[salsa::tracked]
pub fn parse_program(db: &dyn salsa::Database, _source_program: SourceFile) -> Program<'_> {
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
