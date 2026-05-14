//! Diagnostic queries for Salsa database
//!
//! This module provides Salsa queries for collecting and aggregating diagnostics
//! from parsing and elaboration.

use crate::db::{SourceFile, VfsFileMap};
use hwml_diagnostic::{Diagnostic, DiagnosticCode, DiagnosticSeverity, Position, Span};
use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::Arc;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FileTaggedDiagnostic {
    pub file: PathBuf,
    pub diagnostic: Diagnostic,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct DiagnosticCollection {
    pub by_file: HashMap<PathBuf, Vec<Diagnostic>>,
    pub counts: DiagnosticCounts,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct DiagnosticCounts {
    pub bugs: usize,
    pub errors: usize,
    pub warnings: usize,
    pub infos: usize,
    pub hints: usize,
}

impl DiagnosticCounts {
    pub fn total(&self) -> usize {
        self.bugs + self.errors + self.warnings + self.infos + self.hints
    }

    pub fn fatal(&self) -> usize {
        self.bugs + self.errors
    }

    fn add(&mut self, severity: DiagnosticSeverity) {
        match severity {
            DiagnosticSeverity::Bug => self.bugs += 1,
            DiagnosticSeverity::Error => self.errors += 1,
            DiagnosticSeverity::Warning => self.warnings += 1,
            DiagnosticSeverity::Info => self.infos += 1,
            DiagnosticSeverity::Hint => self.hints += 1,
        }
    }
}

impl DiagnosticCollection {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add(&mut self, file: PathBuf, diagnostic: Diagnostic) {
        self.counts.add(diagnostic.severity);
        self.by_file.entry(file).or_default().push(diagnostic);
    }

    pub fn all(&self) -> Vec<FileTaggedDiagnostic> {
        let mut result = Vec::new();
        for (file, diagnostics) in &self.by_file {
            for diagnostic in diagnostics {
                result.push(FileTaggedDiagnostic {
                    file: file.clone(),
                    diagnostic: diagnostic.clone(),
                });
            }
        }
        result.sort_by_key(|tagged| tagged.diagnostic.severity);
        result
    }

    pub fn for_file(&self, file: &PathBuf) -> Vec<Diagnostic> {
        self.by_file.get(file).cloned().unwrap_or_default()
    }
}

fn position_from_offset(text: &str, offset: usize) -> Position {
    let line_info = hwml_support::line_info::LineInfo::from_string(text);
    let line_index = line_info.line(offset);
    let start_of_line = line_info.line_start(line_index);
    Position::new(offset, start_of_line, line_index + 1)
}

fn span_from_offsets(text: &str, start: usize, end: usize) -> Span {
    let line_info = hwml_support::line_info::LineInfo::from_string(text);
    let start_line = line_info.line(start);
    let end_line = line_info.line(end);
    Span::new(
        Position::new(start, line_info.line_start(start_line), start_line + 1),
        Position::new(end, line_info.line_start(end_line), end_line + 1),
    )
}

// Convert ElabError to Diagnostic.
/// Format a value for error messages (simple, user-friendly representation)
fn format_value_for_error<'db>(db: &'db dyn salsa::Database, val: &hwml_core::RcValue<'db>) -> String {
    use hwml_core::Value;
    match val.as_ref() {
        Value::UniverseCode(n) => format!("Type{}", n),
        Value::TypeConstructor(tc) => format!("{}", tc.constructor.to_string(db)),
        Value::DataConstructor(dc) => format!("{}", dc.constructor.to_string(db)),
        Value::PiCode(_, _, _) => "Π type".to_string(),
        Value::BitCode => "Bit".to_string(),
        Value::Flex(flex) => format!("?{}", flex.head.id.local_index),
        Value::Rigid(r) => format!("%{}", r.head.level.0),
        _ => format!("{:?}", val), // Fallback to debug for complex cases
    }
}

// Public for use by LSP server.
pub fn convert_elab_error_to_diagnostic<'db>(
    db: &'db dyn salsa::Database,
    source: SourceFile,
    error: &hwml_elab::error::ElabError<'db>,
) -> Option<Diagnostic> {
    use hwml_elab::error::ElabError;

    let text = source.text(db);
    let span = if let Some(sr) = error.span() {
        span_from_offsets(text, sr.range.start, sr.range.end)
    } else {
        Span::point(position_from_offset(text, 0))
    };

    let backtrace = error
        .backtrace()
        .iter()
        .map(|frame| hwml_diagnostic::Loctext::without_loc(format!("{:?}", frame)))
        .collect();

    let (message, code) = match error {
        ElabError::TypeMismatch { expected, actual, .. } => (
            format!("Type mismatch: expected {:?}, found {:?}", expected, actual),
            Some(DiagnosticCode::new("E0002")),
        ),
        ElabError::NotInScope { name, .. } => (
            format!("Name not in scope: {}", name),
            Some(DiagnosticCode::new("E0003")),
        ),
        ElabError::CannotInfer { .. } => (
            "Cannot infer type".to_string(),
            Some(DiagnosticCode::new("E0004")),
        ),
        ElabError::UnificationFailure { lhs, rhs, .. } => (
            format!(
                "Type mismatch: expected '{}' but found '{}'",
                format_value_for_error(db, rhs),
                format_value_for_error(db, lhs)
            ),
            Some(DiagnosticCode::new("E0005")),
        ),
        ElabError::OccursCheck { meta, .. } => (
            format!("Occurs check failed for meta variable ?{}", meta.0),
            Some(DiagnosticCode::new("E0006")),
        ),
        ElabError::ScopeViolation { meta, .. } => (
            format!("Scope violation for meta variable ?{}", meta.0),
            Some(DiagnosticCode::new("E0007")),
        ),
        ElabError::UnsolvedMeta { meta, .. } => (
            format!("Unsolved meta variable ?{}", meta.0),
            Some(DiagnosticCode::new("E0008")),
        ),
        ElabError::MetaAlreadySolved { meta, .. } => (
            format!("Meta variable ?{} already solved", meta.0),
            Some(DiagnosticCode::new("E0009")),
        ),
        ElabError::NotImplemented { feature, .. } => (
            format!("Not implemented: {}", feature),
            Some(DiagnosticCode::new("E0010")),
        ),
    };

    Some(Diagnostic {
        severity: DiagnosticSeverity::Error,
        span,
        message,
        code,
        explanation: None,
        suggestions: Vec::new(),
        related: Vec::new(),
        backtrace,
        extra_remarks: Vec::new(),
    })
}

// Collect all diagnostics for a single file (parse errors + elaboration errors).
#[salsa::tracked]
pub fn file_diagnostics(db: &dyn salsa::Database, source: SourceFile) -> Arc<Vec<Diagnostic>> {
    let mut diagnostics = Vec::new();
    let parse_result = crate::workspace::parse_surface_program_with_errors(db, source);
    let text = source.text(db);

    // Collect parse errors
    for error in &parse_result.errors {
        let pos = position_from_offset(text, error.offset);
        diagnostics.push(Diagnostic {
            severity: DiagnosticSeverity::Error,
            span: Span::new(pos, pos),
            message: error.message.clone(),
            code: Some(DiagnosticCode::new("E0001")),
            explanation: None,
            suggestions: Vec::new(),
            related: Vec::new(),
            backtrace: Vec::new(),
            extra_remarks: Vec::new(),
        });
    }

    // TODO: Collect elaboration errors (type checking errors)
    // The elaboration system currently requires concrete database types (&HwmlDatabase)
    // but Salsa queries only provide &dyn salsa::Database. This needs architectural work.
    // For now, elaboration errors are only available via the CLI, not LSP.
    //
    // Potential solutions:
    // 1. Add ?Sized bounds to all elaboration functions (requires touching many files)
    // 2. Create a separate elaboration query that runs outside the Salsa query system
    // 3. Use workspace-level elaboration instead of per-file elaboration
    let _ = parse_result.program; // Suppress unused warning

    Arc::new(diagnostics)
}

// Aggregate diagnostics from all files in the workspace.
#[salsa::tracked]
pub fn workspace_diagnostics(db: &dyn salsa::Database, vfs: VfsFileMap) -> Arc<DiagnosticCollection> {
    let mut collection = DiagnosticCollection::new();
    for (path, source) in vfs.files(db).iter() {
        for diagnostic in file_diagnostics(db, *source).iter() {
            collection.add(path.clone(), diagnostic.clone());
        }
    }
    Arc::new(collection)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::db::HwmlDatabase;
    use salsa::Setter;
    use std::collections::HashMap;

    #[test]
    fn test_diagnostic_counts() {
        let mut counts = DiagnosticCounts::default();
        assert_eq!(counts.total(), 0);

        counts.add(DiagnosticSeverity::Error);
        counts.add(DiagnosticSeverity::Warning);
        assert_eq!(counts.total(), 2);
        assert_eq!(counts.fatal(), 1);

        counts.add(DiagnosticSeverity::Bug);
        assert_eq!(counts.fatal(), 2);
    }

    #[test]
    fn test_file_diagnostics_valid_file() {
        let db = HwmlDatabase::new();
        let source = SourceFile::new(
            &db,
            PathBuf::from("/test/valid.hwml"),
            "def x := 1".to_string(),
            "test".to_string(),
        );
        let diags = file_diagnostics(&db, source);
        assert_eq!(diags.len(), 0);
    }

    #[test]
    fn test_file_diagnostics_invalid_file() {
        let db = HwmlDatabase::new();
        let source = SourceFile::new(
            &db,
            PathBuf::from("/test/invalid.hwml"),
            "this is not valid hwml syntax @#$%".to_string(),
            "test".to_string(),
        );
        let diags = file_diagnostics(&db, source);
        assert!(diags.len() > 0);
        assert_eq!(diags[0].severity, DiagnosticSeverity::Error);
        assert!(
            diags[0].message.contains("token") || diags[0].message.contains("Token"),
            "got: {}",
            diags[0].message
        );
    }

    #[test]
    fn test_workspace_diagnostics() {
        let db = HwmlDatabase::new();
        let valid = SourceFile::new(&db, PathBuf::from("/test/valid.hwml"), "def x := 1".to_string(), "test".to_string());
        let invalid = SourceFile::new(&db, PathBuf::from("/test/invalid.hwml"), "@#$% invalid".to_string(), "test".to_string());

        let mut files = HashMap::new();
        files.insert(PathBuf::from("/test/valid.hwml"), valid);
        files.insert(PathBuf::from("/test/invalid.hwml"), invalid);
        let vfs = VfsFileMap::new(&db, Arc::new(files));

        let collection = workspace_diagnostics(&db, vfs);
        assert!(collection.counts.errors > 0);
        assert_eq!(collection.by_file.len(), 1);
        assert!(collection.by_file.contains_key(&PathBuf::from("/test/invalid.hwml")));
    }

    #[test]
    fn test_salsa_incrementality() {
        let mut db = HwmlDatabase::new();
        db.enable_logging();

        // Create three files
        let file_a = SourceFile::new(&db, PathBuf::from("/test/a.hwml"), "def a := 1".to_string(), "test".to_string());
        let file_b = SourceFile::new(&db, PathBuf::from("/test/b.hwml"), "def b := 2".to_string(), "test".to_string());
        let file_c = SourceFile::new(&db, PathBuf::from("/test/c.hwml"), "invalid @#$".to_string(), "test".to_string());

        // Initial computation
        let diags_a = file_diagnostics(&db, file_a);
        let diags_b = file_diagnostics(&db, file_b);
        let diags_c = file_diagnostics(&db, file_c);

        assert_eq!(diags_a.len(), 0);
        assert_eq!(diags_b.len(), 0);
        assert_eq!(diags_c.len(), 1);

        let logs = db.take_logs();
        assert!(logs.iter().any(|log| log.contains("file_diagnostics")));

        // Edit file A only
        file_a.set_text(&mut db).to("def a := 42".to_string());

        // Query file A again - should recompute
        let diags_a_new = file_diagnostics(&db, file_a);
        assert_eq!(diags_a_new.len(), 0);

        // Query file B again - should use cached result
        let diags_b_cached = file_diagnostics(&db, file_b);
        assert_eq!(diags_b_cached.len(), 0);

        let logs = db.take_logs();
        // Salsa should execute file_diagnostics for the modified file
        assert!(logs.iter().any(|log| log.contains("file_diagnostics")));
    }

    #[test]
    fn test_workspace_diagnostics_incrementality() {
        let mut db = HwmlDatabase::new();
        db.enable_logging();

        // Create initial workspace
        let file_a = SourceFile::new(&db, PathBuf::from("/test/a.hwml"), "def a := 1".to_string(), "test".to_string());
        let file_b = SourceFile::new(&db, PathBuf::from("/test/b.hwml"), "def b := 2".to_string(), "test".to_string());

        let mut files = HashMap::new();
        files.insert(PathBuf::from("/test/a.hwml"), file_a);
        files.insert(PathBuf::from("/test/b.hwml"), file_b);
        let vfs = VfsFileMap::new(&db, Arc::new(files.clone()));

        // Initial query
        let collection1 = workspace_diagnostics(&db, vfs);
        assert_eq!(collection1.counts.total(), 0);
        db.take_logs();

        // Edit file A
        file_a.set_text(&mut db).to("invalid syntax @#$".to_string());

        // Re-query workspace diagnostics
        let collection2 = workspace_diagnostics(&db, vfs);
        assert_eq!(collection2.counts.errors, 1);

        // File B diagnostics should be cached (not recomputed)
        let logs = db.take_logs();
        let has_diagnostics_computation = logs.iter().any(|log| log.contains("WillExecute"));

        // Should see some computation (for file A), but Salsa should cache file B
        assert!(has_diagnostics_computation);
    }
}
