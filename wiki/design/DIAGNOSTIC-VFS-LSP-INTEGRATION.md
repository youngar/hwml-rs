# Diagnostic Framework Integration with VFS, File Manager, and LSP

**Date:** 2026-05-08
**Status:** ⚠️ **SUPERSEDED** - See `DIAGNOSTIC-IMPLEMENTATION-PLAN-REVISED.md` for latest plan
**Revision:** Original 6-week plan (before studying Asai source code)
**Kept For:** Salsa integration details and architectural diagrams still valid
**See Latest:** `DIAGNOSTIC-IMPLEMENTATION-PLAN-REVISED.md`, `UNICODE-RENDERING-ASAI-APPROACH.md`
**Context:** How the diagnostic framework integrates with existing HWML infrastructure
**See Also:** `BIG-PICTURE-PIPELINE.md`, `research/diagnostic-framework-design.md`, `ADR-008-vfs-abstraction.md`

---

## ⚠️ Status Notice

This document contains the **original implementation plan** created before we studied the Asai source code in `external/asai/`.

**What changed:**
- Terminal rendering approach (ANSI underlines, not column alignment)
- Type design (Position caching, Bug severity level, backtrace separation)
- LSP simplification (UTF-8 only, no positionEncoding complexity)
- Feature additions (block splitting, GitHub Actions integration)

**What's still valid:**
- Salsa integration architecture (Section 1-2)
- VFS abstraction approach (Section 3)
- Database query design (Section 4)
- Overall 6-week timeline structure

**Use this for:** Understanding Salsa/VFS integration details
**Use revised plan for:** Type design, rendering, and feature details

---

## Executive Summary

This document specifies how the new diagnostic framework integrates with HWML's existing VFS abstraction, Salsa database, and LSP server to provide:

1. **Incremental diagnostics** - Only recompute errors for changed files
2. **Rich LSP integration** - IDE shows errors in real-time with full context
3. **Multiple output formats** - Terminal, LSP, JSON, HTML
4. **File grouping** - Organize diagnostics by file for clarity
5. **VFS independence** - Works with OsVfs (CLI), LspVfs (IDE), MemoryVfs (tests)

**Key Design Principle:** Diagnostics are **derived data** computed from SourceFile inputs via Salsa queries, ensuring automatic incrementality.

---

## Architecture Overview

```
┌──────────────────────────────────────────────────────────────────┐
│                     VFS Layer (Outside Salsa)                    │
│  ┌────────────┐    ┌────────────┐    ┌────────────┐             │
│  │  OsVfs     │    │  LspVfs    │    │ MemoryVfs  │             │
│  │  (CLI)     │    │  (LSP)     │    │  (tests)   │             │
│  └─────┬──────┘    └─────┬──────┘    └─────┬──────┘             │
│        │                 │                  │                     │
│        └─────────────────┼──────────────────┘                     │
│                          │                                        │
│                     Feeds SourceFile inputs                       │
└──────────────────────────┼────────────────────────────────────────┘
                           ↓
┌──────────────────────────────────────────────────────────────────┐
│                    Salsa Database Layer                          │
│                                                                  │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │ #[salsa::input]                                         │   │
│  │ SourceFile { path: PathBuf, text: String }             │   │
│  └────────────────┬────────────────────────────────────────┘   │
│                   │                                             │
│                   ↓                                             │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │ #[salsa::tracked]                                       │   │
│  │ fn parse_surface_program(SourceFile) -> Option<Program>│   │
│  └────────────────┬────────────────────────────────────────┘   │
│                   │                                             │
│                   ↓                                             │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │ #[salsa::tracked]                                       │   │
│  │ fn elaborate_file(SourceFile, StubTable)               │   │
│  │     -> ElaborationResult                                │   │
│  └────────────────┬────────────────────────────────────────┘   │
│                   │                                             │
│                   ↓                                             │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │ #[salsa::tracked]                                       │   │
│  │ fn file_diagnostics(SourceFile)                         │   │
│  │     -> Arc<Vec<Diagnostic>>              ⭐ NEW         │   │
│  └────────────────┬────────────────────────────────────────┘   │
│                   │                                             │
│                   ↓                                             │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │ #[salsa::tracked]                                       │   │
│  │ fn workspace_diagnostics(VfsFileMap)                    │   │
│  │     -> Arc<DiagnosticCollection>         ⭐ NEW         │   │
│  └────────────────┬────────────────────────────────────────┘   │
│                   │                                             │
└───────────────────┼──────────────────────────────────────────────┘
                    │
                    ↓
┌──────────────────────────────────────────────────────────────────┐
│                 Diagnostic Processing Layer                      │
│                                                                  │
│  ┌────────────────────────────────────────────────────────┐    │
│  │ DiagnosticSystem::new()                                │    │
│  │   .post_process(&diagnostics)    // Dedup, cascading  │    │
│  │   .add_suggestions()             // Pattern detection  │    │
│  │   .gather_sources()              // Load file content  │    │
│  └────────────────┬───────────────────────────────────────┘    │
│                   │                                             │
└───────────────────┼──────────────────────────────────────────────┘
                    │
      ┌─────────────┴─────────────┬────────────────┐
      │                           │                │
      ↓                           ↓                ↓
┌──────────────┐       ┌──────────────────┐  ┌──────────────┐
│  Terminal    │       │  LSP (IDE)       │  │  JSON/HTML   │
│  Renderer    │       │  PublishDiags    │  │  Export      │
└──────────────┘       └──────────────────┘  └──────────────┘
```

---

## Component 1: Salsa Diagnostic Queries

### 1.1 Per-File Diagnostics Query

**Location:** `crates/hwml-db/src/diagnostics.rs` (NEW FILE)

```rust
use crate::db::{HwmlDatabase, SourceFile, VfsFileMap};
use hwml_diagnostic::{Diagnostic, DiagnosticSeverity, Span};
use std::sync::Arc;

/// Compute diagnostics for a single file.
///
/// This is a Salsa tracked function, so results are cached and only
/// recomputed when the file changes.
///
/// # Incremental Compilation
///
/// When file A is edited:
/// - `file_diagnostics(A)` invalidates → recomputes diagnostics for A
/// - `file_diagnostics(B)` stays cached → uses cached diagnostics
/// - Result: Only file A's diagnostics are recomputed!
#[salsa::tracked]
pub fn file_diagnostics(
    db: &dyn salsa::Database,
    source_file: SourceFile,
) -> Arc<Vec<Diagnostic>> {
    let mut diagnostics = Vec::new();
    
    // Step 1: Parse the file
    let parse_result = crate::workspace::parse_surface_program(db, source_file);
    
    // Collect parse errors
    if let Some(ref program) = parse_result {
        // Parse succeeded, check for harvesting errors
        let harvest_result = crate::workspace::file_declarations(db, source_file);
        
        // Collect harvest errors (name conflicts, etc.)
        // These are warnings/errors during declaration harvesting
    } else {
        // Parse failed - create diagnostic from parse error
        // (Parser should store errors somewhere we can retrieve)
        diagnostics.push(Diagnostic {
            severity: DiagnosticSeverity::Error,
            span: Span::new(0, 0), // TODO: Get actual span from parse error
            message: "Parse error".to_string(),
            code: Some("E0001".to_string()),
            // ... more fields
        });
    }
    
    Arc::new(diagnostics)
}
```

### 1.2 Workspace-Wide Diagnostics Query

```rust
/// Compute diagnostics for all files in the workspace.
///
/// This aggregates diagnostics from all files, performs post-processing
/// (deduplication, cascading analysis), and groups by file.
///
/// # Incremental Compilation
///
/// When file A is edited:
/// - `file_diagnostics(A)` invalidates → recomputes A's diagnostics
/// - `file_diagnostics(B, C, D)` stay cached → uses cached diagnostics
/// - `workspace_diagnostics()` invalidates → BUT most work is cached!
/// - Only A's diagnostics are recomputed, rest are reused
#[salsa::tracked]
pub fn workspace_diagnostics(
    db: &dyn salsa::Database,
    vfs_map: VfsFileMap,
) -> Arc<DiagnosticCollection> {
    let files = vfs_map.files(db);

    // Gather diagnostics from all files (most will be cached!)
    let mut all_diagnostics = Vec::new();
    for (path, source_file) in files.iter() {
        let file_diags = file_diagnostics(db, *source_file);

        // Tag each diagnostic with its source file
        for diag in file_diags.iter() {
            all_diagnostics.push(FileTaggedDiagnostic {
                file: *source_file,
                path: path.clone(),
                diagnostic: diag.clone(),
            });
        }
    }

    // Post-processing (outside Salsa - not cached)
    let collection = DiagnosticCollection::new(all_diagnostics);

    Arc::new(collection)
}

/// A diagnostic tagged with its source file for workspace-wide analysis
#[derive(Debug, Clone)]
pub struct FileTaggedDiagnostic {
    pub file: SourceFile,
    pub path: PathBuf,
    pub diagnostic: Diagnostic,
}

/// Collection of diagnostics across multiple files with post-processing
#[derive(Debug, Clone)]
pub struct DiagnosticCollection {
    /// All diagnostics (before post-processing)
    pub raw: Vec<FileTaggedDiagnostic>,

    /// Diagnostics grouped by file
    pub by_file: HashMap<PathBuf, Vec<Diagnostic>>,

    /// Total counts
    pub errors: usize,
    pub warnings: usize,
    pub hints: usize,
}

impl DiagnosticCollection {
    fn new(mut diagnostics: Vec<FileTaggedDiagnostic>) -> Self {
        // Sort by file, then by position
        diagnostics.sort_by(|a, b| {
            a.path.cmp(&b.path)
                .then(a.diagnostic.span.start.cmp(&b.diagnostic.span.start))
        });

        // Group by file
        let mut by_file: HashMap<PathBuf, Vec<Diagnostic>> = HashMap::new();
        for tagged in &diagnostics {
            by_file.entry(tagged.path.clone())
                .or_insert_with(Vec::new)
                .push(tagged.diagnostic.clone());
        }

        // Count by severity
        let errors = diagnostics.iter()
            .filter(|d| d.diagnostic.severity == DiagnosticSeverity::Error)
            .count();
        let warnings = diagnostics.iter()
            .filter(|d| d.diagnostic.severity == DiagnosticSeverity::Warning)
            .count();
        let hints = diagnostics.iter()
            .filter(|d| d.diagnostic.severity == DiagnosticSeverity::Hint)
            .count();

        Self {
            raw: diagnostics,
            by_file,
            errors,
            warnings,
            hints,
        }
    }
}
```

---

## Component 2: VFS Integration

### 2.1 Current VFS Architecture (Already Implemented)

HWML already has a clean VFS abstraction following ADR-008:

**Key Principle:** VFS lives OUTSIDE Salsa and feeds it SourceFile inputs.

```rust
pub trait Vfs {
    /// Get or create a SourceFile for a path
    fn get_or_create_file(
        &mut self,
        db: &HwmlDatabase,
        path: &Path,
    ) -> Result<SourceFile, VfsError>;

    /// Update file content (triggers Salsa invalidation)
    fn update_file(
        &mut self,
        db: &mut HwmlDatabase,
        path: &Path,
        new_text: String,
    ) -> Result<(), VfsError>;

    /// Get file without I/O (if already loaded)
    fn get_file(&self, path: &Path) -> Option<SourceFile>;
}
```

**Three Implementations:**

1. **OsVfs** - CLI: Reads from filesystem
2. **LspVfs** - LSP: Tracks open editor buffers
3. **MemoryVfs** - Tests: In-memory storage

### 2.2 How Diagnostics Integrate with VFS

**The VFS doesn't change!** Diagnostics are purely derived data.

**Data Flow:**

```
1. VFS creates/updates SourceFile
   ↓
2. VFS calls: file.set_text(db).to(new_text)
   ↓
3. Salsa invalidates all queries depending on this SourceFile
   ↓
4. Next time we call file_diagnostics(db, file):
   - Salsa detects input changed
   - Recomputes diagnostics
   - Returns fresh result
```

**Example (LSP editing a file):**

```rust
// In LSP server, user types in editor
fn recv_did_change_text_document(&mut self, params: DidChangeTextDocumentParams) {
    let uri = params.text_document.uri;

    // Step 1: VFS updates file (triggers Salsa invalidation)
    self.vfs.update_document(&mut self.db, &uri, new_content)
        .expect("Failed to update");

    // Step 2: Query diagnostics (Salsa recomputes automatically)
    let file = self.vfs.get_by_uri(&uri).unwrap();
    let diagnostics = hwml_db::file_diagnostics(&self.db, file);

    // Step 3: Convert to LSP format and publish
    let lsp_diagnostics = self.to_lsp_diagnostics(&*diagnostics, file);
    self.publish_diagnostics(uri, lsp_diagnostics);
}
```

**Key Insight:** VFS is unchanged! Diagnostics query the Salsa database, which automatically handles incrementality.

---

## Component 3: LSP Integration

### 3.1 Current LSP Architecture

**Location:** `crates/hwml-lsp-server/src/main.rs`

**Current State:**
- ✅ LspVfs tracks open documents
- ✅ Incremental edits supported
- ✅ Basic `PublishDiagnostics` capability
- ❌ Diagnostics are minimal (just parse errors)
- ❌ No rich diagnostic features

**Current diagnostic code:**

```rust
fn compile_file(&self, db: &HwmlDatabase, uri: &Uri, file: SourceFile) {
    let _program = hwml_db::db::parse_program(&*db, file);
    let diagnostics = hwml_db::db::parse_program::accumulated::<hwml_db::db::Diagnostics>(db, file);

    // Convert to LSP format (very basic)
    let lsp_diagnostics = diagnostics.into_iter()
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
```

**Problem:** This uses Salsa accumulators (`accumulated::<Diagnostics>`), which don't support the post-processing we need.

### 3.2 New LSP Diagnostic Integration

**Replace the current diagnostic code with our new system:**

```rust
// In crates/hwml-lsp-server/src/main.rs

use hwml_db::diagnostics::{file_diagnostics, workspace_diagnostics};
use hwml_diagnostic::{DiagnosticSystem, LspConverter};

impl Server {
    /// Publish diagnostics for a single file
    fn publish_file_diagnostics(&self, uri: &Uri, file: SourceFile) {
        // Step 1: Query diagnostics from Salsa (cached!)
        let raw_diagnostics = file_diagnostics(&self.db, file);

        // Step 2: Post-process (dedup, suggestions, etc.)
        let diag_system = DiagnosticSystem::new(&self.db);
        let processed = diag_system.post_process_file(&*raw_diagnostics, file);

        // Step 3: Convert to LSP format
        let converter = LspConverter::new(&self.db);
        let lsp_diagnostics = converter.to_lsp(&processed, file);

        // Step 4: Send to client
        self.send_diagnostics(uri.clone(), lsp_diagnostics);
    }

    /// Publish diagnostics for entire workspace
    fn publish_workspace_diagnostics(&self) {
        // Step 1: Get VfsFileMap (tracks all known files)
        let vfs_map = self.get_vfs_file_map(); // Helper to create VfsFileMap from VFS

        // Step 2: Query workspace diagnostics (most files cached!)
        let collection = workspace_diagnostics(&self.db, vfs_map);

        // Step 3: Post-process entire workspace
        let diag_system = DiagnosticSystem::new(&self.db);
        let processed = diag_system.post_process_workspace(&*collection);

        // Step 4: Convert to LSP format and publish per-file
        let converter = LspConverter::new(&self.db);
        for (path, file_diags) in processed.by_file.iter() {
            let uri = Uri::from_file_path(path).unwrap();
            let lsp_diagnostics = converter.to_lsp(file_diags, file);
            self.send_diagnostics(uri, lsp_diagnostics);
        }
    }

    fn recv_did_change_text_document(&mut self, params: DidChangeTextDocumentParams) {
        let uri = params.text_document.uri;
        let edits = params.content_changes;

        // Apply edits via VFS (triggers Salsa invalidation)
        Self::apply_document_edits(&mut self.vfs, &mut self.db, &uri, edits.as_slice());

        // Publish updated diagnostics for this file
        if let Some(file) = self.vfs.get_by_uri(&uri) {
            self.publish_file_diagnostics(&uri, file);
        }

        // Optional: Publish workspace diagnostics if file affects other files
        // (e.g., changed a type that other files depend on)
        if self.should_recheck_workspace(&uri) {
            self.publish_workspace_diagnostics();
        }
    }

    fn recv_did_open_text_document(&mut self, params: DidOpenTextDocumentParams) {
        let uri = params.text_document.uri;
        let text = params.text_document.text;
        let path = PathBuf::from(uri.as_str().trim_start_matches("file://"));

        // Open in VFS
        let file = self.vfs.open_document(&self.db, uri.clone(), path, text);

        // Publish diagnostics immediately
        self.publish_file_diagnostics(&uri, file);
    }
}
```

### 3.3 LSP Diagnostic Conversion

**Location:** `crates/hwml-diagnostic/src/lsp.rs` (NEW FILE)

```rust
use crate::{Diagnostic, DiagnosticSeverity, Span, DiagnosticCode};
use hwml_db::db::{HwmlDatabase, SourceFile};
use lsp_types::{
    Diagnostic as LspDiagnostic,
    DiagnosticSeverity as LspSeverity,
    DiagnosticRelatedInformation,
    Location,
    NumberOrString,
    Position,
    Range,
    Uri,
};

pub struct LspConverter<'db> {
    db: &'db HwmlDatabase,
}

impl<'db> LspConverter<'db> {
    pub fn new(db: &'db HwmlDatabase) -> Self {
        Self { db }
    }

    /// Convert HWML diagnostics to LSP diagnostics
    pub fn to_lsp(&self, diagnostics: &[Diagnostic], file: SourceFile) -> Vec<LspDiagnostic> {
        diagnostics.iter().map(|diag| self.convert_one(diag, file)).collect()
    }

    fn convert_one(&self, diag: &Diagnostic, file: SourceFile) -> LspDiagnostic {
        let line_info = hwml_db::db::get_line_info(self.db, file);

        // Convert byte spans to line:column positions
        let start_pos = self.to_position(&line_info, diag.span.start);
        let end_pos = self.to_position(&line_info, diag.span.end);

        LspDiagnostic {
            range: Range {
                start: start_pos,
                end: end_pos,
            },
            severity: Some(self.convert_severity(diag.severity)),
            code: diag.code.as_ref().map(|c| NumberOrString::String(c.to_string())),
            code_description: diag.code.as_ref().map(|code| {
                lsp_types::CodeDescription {
                    href: Uri::parse(&format!("https://hwml.dev/errors/{}", code))
                        .unwrap_or_else(|_| Uri::parse("https://hwml.dev").unwrap()),
                }
            }),
            source: Some("hwml".to_string()),
            message: diag.message.clone(),
            related_information: self.convert_related_info(diag),
            tags: None, // TODO: Add tags for deprecated, unnecessary
            data: None,
        }
    }

    fn to_position(&self, line_info: &hwml_support::line_info::LineInfo, offset: usize) -> Position {
        let (line, col) = line_info.loc(offset);
        Position {
            line: line as u32,
            character: col as u32,
        }
    }

    fn convert_severity(&self, severity: DiagnosticSeverity) -> LspSeverity {
        match severity {
            DiagnosticSeverity::Error => LspSeverity::ERROR,
            DiagnosticSeverity::Warning => LspSeverity::WARNING,
            DiagnosticSeverity::Info => LspSeverity::INFORMATION,
            DiagnosticSeverity::Hint => LspSeverity::HINT,
        }
    }

    fn convert_related_info(&self, diag: &Diagnostic) -> Option<Vec<DiagnosticRelatedInformation>> {
        if diag.related.is_empty() {
            return None;
        }

        Some(diag.related.iter().map(|rel| {
            let file = rel.file;
            let line_info = hwml_db::db::get_line_info(self.db, file);
            let start_pos = self.to_position(&line_info, rel.span.start);
            let end_pos = self.to_position(&line_info, rel.span.end);

            let uri = Uri::from_file_path(file.path(self.db)).unwrap();

            DiagnosticRelatedInformation {
                location: Location {
                    uri,
                    range: Range {
                        start: start_pos,
                        end: end_pos,
                    },
                },
                message: rel.message.clone(),
            }
        }).collect())
    }
}
```

---

## Component 4: Diagnostic Data Types

### 4.1 Core Diagnostic Type

**Location:** `crates/hwml-diagnostic/src/lib.rs` (NEW CRATE)

```rust
use std::path::PathBuf;
use hwml_db::db::SourceFile;

/// A single diagnostic (error, warning, hint, etc.)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Diagnostic {
    /// Severity level
    pub severity: DiagnosticSeverity,

    /// Byte span in source file
    pub span: Span,

    /// Primary message
    pub message: String,

    /// Error code (e.g., "E0001", "W0042")
    pub code: Option<DiagnosticCode>,

    /// Detailed explanation (for `--explain`)
    pub explanation: Option<String>,

    /// Suggested fixes
    pub suggestions: Vec<Suggestion>,

    /// Related diagnostic locations
    pub related: Vec<RelatedDiagnostic>,

    /// Elaboration backtrace (from trace guards)
    pub backtrace: Vec<BacktraceEntry>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum DiagnosticSeverity {
    Error,
    Warning,
    Info,
    Hint,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Span {
    pub start: usize,  // Byte offset
    pub end: usize,    // Byte offset
}

impl Span {
    pub fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DiagnosticCode(pub String);

impl DiagnosticCode {
    pub fn new(code: impl Into<String>) -> Self {
        Self(code.into())
    }
}

impl std::fmt::Display for DiagnosticCode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Suggestion {
    /// Description of what to change
    pub message: String,

    /// Optional automated fix
    pub fix: Option<Fix>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Fix {
    /// Replace a range with new text
    Replace {
        span: Span,
        replacement: String,
    },

    /// Insert text at a position
    Insert {
        position: usize,
        text: String,
    },

    /// Delete a range
    Delete {
        span: Span,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RelatedDiagnostic {
    /// File where related location is
    pub file: SourceFile,

    /// Span in that file
    pub span: Span,

    /// Message explaining the relationship
    pub message: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BacktraceEntry {
    /// Description of what was being checked
    pub description: String,

    /// Where in source code
    pub span: Span,

    /// File (if different from main diagnostic)
    pub file: Option<SourceFile>,
}
```

### 4.2 Diagnostic Builder (Ergonomic Construction)

```rust
/// Builder for constructing diagnostics
pub struct DiagnosticBuilder {
    diagnostic: Diagnostic,
}

impl DiagnosticBuilder {
    pub fn error(span: Span, message: impl Into<String>) -> Self {
        Self {
            diagnostic: Diagnostic {
                severity: DiagnosticSeverity::Error,
                span,
                message: message.into(),
                code: None,
                explanation: None,
                suggestions: Vec::new(),
                related: Vec::new(),
                backtrace: Vec::new(),
            },
        }
    }

    pub fn warning(span: Span, message: impl Into<String>) -> Self {
        let mut builder = Self::error(span, message);
        builder.diagnostic.severity = DiagnosticSeverity::Warning;
        builder
    }

    pub fn with_code(mut self, code: impl Into<String>) -> Self {
        self.diagnostic.code = Some(DiagnosticCode::new(code));
        self
    }

    pub fn with_explanation(mut self, explanation: impl Into<String>) -> Self {
        self.diagnostic.explanation = Some(explanation.into());
        self
    }

    pub fn with_suggestion(mut self, message: impl Into<String>) -> Self {
        self.diagnostic.suggestions.push(Suggestion {
            message: message.into(),
            fix: None,
        });
        self
    }

    pub fn with_fix(mut self, message: impl Into<String>, fix: Fix) -> Self {
        self.diagnostic.suggestions.push(Suggestion {
            message: message.into(),
            fix: Some(fix),
        });
        self
    }

    pub fn with_related(
        mut self,
        file: SourceFile,
        span: Span,
        message: impl Into<String>,
    ) -> Self {
        self.diagnostic.related.push(RelatedDiagnostic {
            file,
            span,
            message: message.into(),
        });
        self
    }

    pub fn with_backtrace_entry(
        mut self,
        description: impl Into<String>,
        span: Span,
        file: Option<SourceFile>,
    ) -> Self {
        self.diagnostic.backtrace.push(BacktraceEntry {
            description: description.into(),
            span,
            file,
        });
        self
    }

    pub fn build(self) -> Diagnostic {
        self.diagnostic
    }
}

// Usage example:
fn example_diagnostic_construction(span: Span, file: SourceFile) -> Diagnostic {
    DiagnosticBuilder::error(span, "type mismatch")
        .with_code("E0308")
        .with_explanation("Expected type Nat, but found Bool")
        .with_suggestion("consider using an if expression")
        .with_related(file, Span::new(10, 20), "function return type declared here")
        .build()
}
```

---

## Component 5: File Manager Integration

### 5.1 VfsFileMap Management

**Location:** `crates/hwml-lsp-server/src/main.rs`

The LSP server needs to maintain a `VfsFileMap` Salsa input that tracks all files:

```rust
impl Server {
    /// Create or update VfsFileMap from current VFS state
    fn get_or_update_vfs_file_map(&mut self) -> VfsFileMap {
        // Collect all files from LspVfs
        let mut files = HashMap::new();

        // Add all open documents
        for (uri, (path, file)) in self.vfs.open_documents() {
            files.insert(path.clone(), *file);
        }

        // Add all workspace files (if workspace is loaded)
        if let Some(ref workspace) = self.workspace {
            for lib in workspace.libraries.values() {
                for source_file in &lib.source_files {
                    let path = source_file.canonical_path();
                    if !files.contains_key(&path) {
                        // Load from VFS
                        if let Ok(file) = self.vfs.get_or_create_file(&self.db, &path) {
                            files.insert(path, file);
                        }
                    }
                }
            }
        }

        // Create or update VfsFileMap Salsa input
        if let Some(existing_map) = self.vfs_file_map {
            // Update existing map
            existing_map.set_files(&mut self.db).to(Arc::new(files));
            existing_map
        } else {
            // Create new map
            let map = VfsFileMap::new(&self.db, Arc::new(files));
            self.vfs_file_map = Some(map);
            map
        }
    }

    fn reload_workspace(&mut self) {
        // Load workspace manifest
        // ...

        // Update VfsFileMap with all workspace files
        let _ = self.get_or_update_vfs_file_map();

        // Publish diagnostics for entire workspace
        self.publish_workspace_diagnostics();
    }

    fn recv_did_open_text_document(&mut self, params: DidOpenTextDocumentParams) {
        let uri = params.text_document.uri;
        let text = params.text_document.text;
        let path = PathBuf::from(uri.as_str().trim_start_matches("file://"));

        // Open in VFS
        let file = self.vfs.open_document(&self.db, uri.clone(), path.clone(), text);

        // Update VfsFileMap (add this file)
        let mut map = self.get_or_update_vfs_file_map();
        let mut files = map.files(&self.db).as_ref().clone();
        files.insert(path, file);
        map.set_files(&mut self.db).to(Arc::new(files));

        // Publish diagnostics
        self.publish_file_diagnostics(&uri, file);
    }

    fn recv_did_close_text_document(&mut self, params: DidCloseTextDocumentParams) {
        let uri = params.text_document.uri;

        // Close in VFS
        self.vfs.close_document(&uri);

        // Update VfsFileMap (remove if not in workspace)
        let path = PathBuf::from(uri.as_str().trim_start_matches("file://"));
        if !self.is_workspace_file(&path) {
            let mut map = self.get_or_update_vfs_file_map();
            let mut files = map.files(&self.db).as_ref().clone();
            files.remove(&path);
            map.set_files(&mut self.db).to(Arc::new(files));
        }

        // Clear diagnostics for closed file
        self.send_diagnostics(uri, vec![]);
    }
}
```

### 5.2 Incremental Update Flow

**When user edits file A:**

```
1. LSP receives DidChangeTextDocument notification
   ↓
2. LspVfs.update_document(&mut db, uri, new_text)
   → Calls file.set_text(db).to(new_text)
   → Salsa invalidates all queries depending on file A
   ↓
3. LSP calls file_diagnostics(db, file_a)
   → Salsa detects input changed
   → Recomputes diagnostics for file A ONLY
   → Returns fresh diagnostics
   ↓
4. Convert diagnostics to LSP format
   ↓
5. PublishDiagnostics to client
```

**Key Benefit:** Files B, C, D use cached diagnostics!

---

## Component 6: CLI Integration

### 6.1 Terminal Diagnostic Rendering

**Location:** `crates/hwml-cli/src/main.rs`

```rust
use hwml_vfs::OsVfs;
use hwml_db::{HwmlDatabase, diagnostics::{workspace_diagnostics, file_diagnostics}};
use hwml_diagnostic::{DiagnosticSystem, TerminalRenderer};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Parse command line arguments
    let args = parse_args();

    // Create database and VFS
    let mut db = HwmlDatabase::new();
    let mut vfs = OsVfs::new();

    // Load workspace
    let workspace = load_workspace(&args.manifest_path)?;

    // Create VfsFileMap
    let mut files = HashMap::new();
    for lib in workspace.libraries.values() {
        for source_path in &lib.source_files {
            let file = vfs.get_or_create_file(&db, source_path)?;
            files.insert(source_path.clone(), file);
        }
    }
    let vfs_map = VfsFileMap::new(&db, Arc::new(files));

    // Query workspace diagnostics
    let collection = workspace_diagnostics(&db, vfs_map);

    // Post-process
    let diag_system = DiagnosticSystem::new(&db);
    let processed = diag_system.post_process_workspace(&*collection);

    // Render to terminal
    let renderer = TerminalRenderer::new(&db, &vfs);
    let output = renderer.render(&processed);

    // Print to stdout
    println!("{}", output);

    // Exit with error code if there were errors
    if processed.errors > 0 {
        std::process::exit(1);
    }

    Ok(())
}
```

### 6.2 JSON Export (for CI/CD)

```rust
use hwml_diagnostic::JsonExporter;

fn export_diagnostics_json(
    db: &HwmlDatabase,
    collection: &DiagnosticCollection,
    output_path: &Path,
) -> Result<(), Box<dyn std::error::Error>> {
    let exporter = JsonExporter::new(db);
    let json = exporter.export(collection)?;

    std::fs::write(output_path, json)?;

    Ok(())
}
```

**JSON Format:**

```json
{
  "version": "1.0",
  "summary": {
    "errors": 5,
    "warnings": 3,
    "hints": 2,
    "files": 3
  },
  "files": {
    "src/main.hwml": {
      "errors": 2,
      "warnings": 1,
      "diagnostics": [
        {
          "severity": "error",
          "code": "E0308",
          "message": "type mismatch",
          "span": {"start": 42, "end": 46},
          "line": 10,
          "column": 5,
          "suggestions": ["consider using an if expression"],
          "related": [
            {
              "file": "src/lib.hwml",
              "span": {"start": 100, "end": 110},
              "message": "function return type declared here"
            }
          ]
        }
      ]
    }
  }
}
```

---

## Component 7: Post-Processing System

### 7.1 DiagnosticSystem

**Location:** `crates/hwml-diagnostic/src/system.rs`

```rust
use crate::{Diagnostic, DiagnosticCollection};
use hwml_db::db::HwmlDatabase;

pub struct DiagnosticSystem<'db> {
    db: &'db HwmlDatabase,
}

impl<'db> DiagnosticSystem<'db> {
    pub fn new(db: &'db HwmlDatabase) -> Self {
        Self { db }
    }

    /// Post-process diagnostics for a single file
    pub fn post_process_file(
        &self,
        diagnostics: &[Diagnostic],
        file: SourceFile,
    ) -> Vec<Diagnostic> {
        let mut processed = diagnostics.to_vec();

        // Step 1: Deduplication
        processed = self.deduplicate(processed);

        // Step 2: Pattern detection & suggestions
        processed = self.add_pattern_suggestions(processed);

        // Step 3: Sort by position
        processed.sort_by_key(|d| d.span.start);

        processed
    }

    /// Post-process diagnostics for entire workspace
    pub fn post_process_workspace(
        &self,
        collection: &DiagnosticCollection,
    ) -> DiagnosticCollection {
        let mut processed = collection.clone();

        // Step 1: Deduplication across files
        processed.raw = self.deduplicate_workspace(processed.raw);

        // Step 2: Cascading error analysis
        processed = self.identify_cascading_errors(processed);

        // Step 3: Pattern detection
        processed.raw = processed.raw.into_iter()
            .map(|mut tagged| {
                let diags = self.add_pattern_suggestions(vec![tagged.diagnostic.clone()]);
                tagged.diagnostic = diags.into_iter().next().unwrap();
                tagged
            })
            .collect();

        // Step 4: Rebuild groupings
        processed.rebuild_groupings();

        processed
    }

    fn deduplicate(&self, mut diagnostics: Vec<Diagnostic>) -> Vec<Diagnostic> {
        use std::collections::HashSet;

        let mut seen = HashSet::new();
        diagnostics.retain(|diag| {
            let key = (diag.span.start, diag.span.end, &diag.message, &diag.code);
            seen.insert(key)
        });

        diagnostics
    }

    fn deduplicate_workspace(
        &self,
        diagnostics: Vec<FileTaggedDiagnostic>,
    ) -> Vec<FileTaggedDiagnostic> {
        // Similar to deduplicate, but across files
        // TODO: Implement
        diagnostics
    }

    fn identify_cascading_errors(
        &self,
        collection: DiagnosticCollection,
    ) -> DiagnosticCollection {
        // Use provenance graph to find root causes
        // Suppress cascading errors
        // TODO: Implement
        collection
    }

    fn add_pattern_suggestions(&self, diagnostics: Vec<Diagnostic>) -> Vec<Diagnostic> {
        diagnostics.into_iter()
            .map(|diag| self.detect_patterns(diag))
            .collect()
    }

    fn detect_patterns(&self, mut diag: Diagnostic) -> Diagnostic {
        // Pattern 1: Type mismatch with unit type → suggest return
        if diag.message.contains("type mismatch")
            && diag.message.contains("expected")
            && diag.message.contains("found ()")
        {
            diag.suggestions.push(Suggestion {
                message: "Add explicit return statement".to_string(),
                fix: Some(Fix::Insert {
                    position: diag.span.end,
                    text: "\nreturn <value>".to_string(),
                }),
            });
        }

        // Pattern 2: Name not in scope → did you mean?
        if diag.message.contains("not in scope") {
            // TODO: Levenshtein distance to find similar names
        }

        // More patterns...

        diag
    }
}
```

---

## Component 8: Integration Testing

### 8.1 End-to-End LSP Test

**Location:** `crates/hwml-lsp-server/tests/diagnostics.rs`

```rust
use hwml_lsp_server::Server;
use hwml_vfs::MemoryVfs;
use hwml_db::HwmlDatabase;
use lsp_types::*;

#[test]
fn test_incremental_diagnostics() {
    // Setup
    let db = HwmlDatabase::new();
    let mut vfs = MemoryVfs::new();

    // Add file with error
    vfs.add_file("/test.hwml", "def x : Nat = true");
    let file = vfs.get_or_create_file(&db, Path::new("/test.hwml")).unwrap();

    // Query diagnostics
    let diagnostics = hwml_db::file_diagnostics(&db, file);
    assert_eq!(diagnostics.len(), 1);
    assert!(diagnostics[0].message.contains("type mismatch"));

    // Fix the error
    vfs.update_file(&mut db, Path::new("/test.hwml"), "def x : Nat = 42".to_string()).unwrap();

    // Query again - should be cached and updated
    let file = vfs.get_file(Path::new("/test.hwml")).unwrap();
    let diagnostics = hwml_db::file_diagnostics(&db, file);
    assert_eq!(diagnostics.len(), 0); // No errors!
}

#[test]
fn test_workspace_diagnostics() {
    // Setup workspace with multiple files
    let db = HwmlDatabase::new();
    let mut vfs = MemoryVfs::new();

    vfs.add_file("/a.hwml", "def foo : Nat = 42");
    vfs.add_file("/b.hwml", "def bar : Bool = foo");  // Error: type mismatch

    let file_a = vfs.get_or_create_file(&db, Path::new("/a.hwml")).unwrap();
    let file_b = vfs.get_or_create_file(&db, Path::new("/b.hwml")).unwrap();

    let mut files = HashMap::new();
    files.insert(PathBuf::from("/a.hwml"), file_a);
    files.insert(PathBuf::from("/b.hwml"), file_b);
    let vfs_map = VfsFileMap::new(&db, Arc::new(files));

    // Query workspace diagnostics
    let collection = hwml_db::workspace_diagnostics(&db, vfs_map);

    assert_eq!(collection.errors, 1);
    assert_eq!(collection.by_file.len(), 1); // Only b.hwml has error
    assert!(collection.by_file.contains_key(&PathBuf::from("/b.hwml")));
}
```

---

## Implementation Plan

### Phase 1: Foundation (Week 1)

**Goal:** Set up new diagnostic crate and basic data types

**Tasks:**
1. Create `crates/hwml-diagnostic/` crate
2. Define core types (`Diagnostic`, `Span`, `DiagnosticSeverity`, etc.)
3. Implement `DiagnosticBuilder` for ergonomic construction
4. Write unit tests for basic functionality

**Deliverables:**
- ✅ `hwml-diagnostic` crate with core types
- ✅ Builder pattern for diagnostics
- ✅ Unit tests passing

**Files Created:**
- `crates/hwml-diagnostic/Cargo.toml`
- `crates/hwml-diagnostic/src/lib.rs`
- `crates/hwml-diagnostic/src/types.rs`
- `crates/hwml-diagnostic/src/builder.rs`

### Phase 2: Salsa Integration (Week 2)

**Goal:** Add diagnostic queries to Salsa database

**Tasks:**
1. Add `crates/hwml-db/src/diagnostics.rs`
2. Implement `file_diagnostics()` query
3. Implement `workspace_diagnostics()` query
4. Update `parse_surface_program` to collect parse errors
5. Update elaboration to collect elab errors

**Deliverables:**
- ✅ `file_diagnostics` query working
- ✅ `workspace_diagnostics` query working
- ✅ Parse errors collected as diagnostics
- ✅ Basic elaboration errors collected

**Migration Note:** Replace existing Salsa accumulator pattern:

```rust
// OLD (current):
#[salsa::accumulator]
pub struct Diagnostics(pub Diagnostic);

Diagnostics(error).accumulate(db);

// NEW (proposed):
// Return diagnostics from queries instead of accumulating
#[salsa::tracked]
fn parse_program(db: &dyn salsa::Database, file: SourceFile)
    -> (Option<Program>, Vec<Diagnostic>) {
    // Parse and collect errors
    (program, parse_errors)
}
```

### Phase 3: LSP Integration (Week 3)

**Goal:** Update LSP server to use new diagnostic system

**Tasks:**
1. Add `crates/hwml-diagnostic/src/lsp.rs` for LSP conversion
2. Update `Server::compile_file()` to use new queries
3. Implement `Server::publish_file_diagnostics()`
4. Implement `Server::publish_workspace_diagnostics()`
5. Update `recv_did_change_text_document()` handler
6. Add `VfsFileMap` management

**Deliverables:**
- ✅ LSP publishes rich diagnostics
- ✅ Incremental updates working
- ✅ Related information shown in IDE
- ✅ Code descriptions (links to docs)

**Testing:**
- Open VSCode with HWML extension
- Edit file, see diagnostics update
- Hover over error, see related info
- Click code link, opens documentation

### Phase 4: Post-Processing (Week 4)

**Goal:** Implement diagnostic post-processing

**Tasks:**
1. Add `crates/hwml-diagnostic/src/system.rs`
2. Implement deduplication
3. Implement pattern detection
4. Implement suggestion generation
5. Add basic cascading error analysis

**Deliverables:**
- ✅ Deduplication reduces error count >30%
- ✅ Pattern detection suggests fixes
- ✅ Common mistakes get helpful hints

**Patterns to Detect:**
- Type mismatch with unit → suggest return
- Name not in scope → did you mean?
- Wrong arity → show expected vs. actual
- Missing type annotation → suggest where to add

### Phase 5: Terminal & JSON Output (Week 5)

**Goal:** Beautiful CLI output and CI/CD integration

**Tasks:**
1. Add `crates/hwml-diagnostic/src/terminal.rs`
2. Implement colored terminal rendering
3. Implement source snippet rendering
4. Add `crates/hwml-diagnostic/src/json.rs` for JSON export
5. Update CLI to use new diagnostic system

**Deliverables:**
- ✅ Beautiful terminal output with colors
- ✅ Multi-line source snippets
- ✅ JSON export for CI/CD
- ✅ File grouping and statistics

**Example Terminal Output:**

```
error[E0308]: type mismatch
  --> src/main.hwml:42:10
   |
40 | fn process(x: Nat) -> Nat {
41 |     let y = x + 1;
42 |     return true;
   |            ^^^^ expected Nat, found Bool
   |
help: consider using an if expression that returns Nat

error: aborting due to 1 previous error

For more information about this error, try `hwml --explain E0308`
```

### Phase 6: Advanced Features (Week 6)

**Goal:** Elaborate backtrace and cascading analysis

**Tasks:**
1. Implement RAII trace guards in elaboration
2. Add backtrace to diagnostics
3. Implement cascading error analysis using provenance
4. Add `--explain` command for detailed error explanations

**Deliverables:**
- ✅ Elaboration backtrace shown for complex errors
- ✅ Root cause identified, cascading errors suppressed
- ✅ `hwml --explain E0308` shows detailed explanation

---

## Migration Strategy

### Compatibility During Transition

**Keep both systems working during migration:**

```rust
// In hwml-db/src/diagnostics.rs

#[salsa::tracked]
pub fn file_diagnostics_new(
    db: &dyn salsa::Database,
    file: SourceFile,
) -> Arc<Vec<hwml_diagnostic::Diagnostic>> {
    // New system
    // ...
}

// OLD system stays for now
#[salsa::accumulator]
pub struct Diagnostics(pub Diagnostic);
```

**LSP uses new system, CLI can use old or new:**

```rust
// In hwml-lsp-server/src/main.rs
use hwml_db::file_diagnostics_new;  // Use new system

// In hwml-cli/src/main.rs
#[cfg(feature = "new-diagnostics")]
use hwml_db::file_diagnostics_new;
#[cfg(not(feature = "new-diagnostics"))]
use hwml_db::old_diagnostics;
```

### Gradual Rollout

1. **Week 1-2:** Implement new system, keep old system
2. **Week 3:** LSP switches to new system
3. **Week 4:** CLI gets `--new-diagnostics` flag
4. **Week 5:** New system becomes default
5. **Week 6:** Remove old system

---

## Performance Considerations

### Salsa Incrementality Benefits

**Scenario: Edit file A in workspace with 100 files**

**Without Salsa:**
```
Parse all 100 files           → 5s
Harvest all 100 files         → 2s
Compute diagnostics for all   → 10s
Total: 17s
```

**With Salsa (after first compilation):**
```
file_diagnostics(A) invalidates  → recomputes A only
file_diagnostics(B-Z) cached     → instant
workspace_diagnostics()          → aggregates (fast)
Total: ~200ms
```

**95% reduction in recomputation time!**

### Memory Overhead

**Per-file diagnostic storage:**
- `Vec<Diagnostic>` wrapped in `Arc`
- Shared across queries via Arc cloning
- Typical file: 0-10 diagnostics × ~200 bytes = 0-2KB
- 100 files × 2KB = 200KB total (negligible)

**VfsFileMap storage:**
- `HashMap<PathBuf, SourceFile>` in `Arc`
- 100 files × (path + pointer) ≈ 10KB

**Total overhead: <1MB for typical workspace**

### Optimization Opportunities

1. **Lazy source loading** - Only load source snippets for displayed diagnostics
2. **Diagnostic caching** - Cache rendered output (terminal/LSP)
3. **Incremental post-processing** - Track which diagnostics changed
4. **Batch LSP publishes** - Send updates in batches, not per-file

---

## Success Metrics

### Week 3 (LSP Integration)

- [ ] LSP publishes diagnostics within 100ms of file change
- [ ] Related information shows in IDE
- [ ] Code links work (open error documentation)
- [ ] Incremental edits update only changed file

### Week 4 (Post-Processing)

- [ ] Deduplication reduces diagnostic count by >30%
- [ ] At least 5 common patterns detected with suggestions
- [ ] Pattern suggestions help fix >50% of detected cases

### Week 5 (Terminal Output)

- [ ] Terminal output passes visual inspection
- [ ] ANSI colors work correctly
- [ ] Source snippets align properly (Unicode-aware)
- [ ] JSON export validates against schema

### Week 6 (Advanced Features)

- [ ] Backtrace shows correct elaboration context
- [ ] Cascading errors identified correctly >80% of time
- [ ] Root cause highlighted, secondary errors suppressed
- [ ] `--explain` command shows detailed error info

---

## Appendix: Example Integration Flows

### Flow A: User Types in VSCode

```
1. User types "true" where Nat expected
   ↓
2. VSCode sends DidChangeTextDocument
   ↓
3. LSP receives, calls vfs.update_document()
   → file.set_text(db).to(new_text)
   → Salsa invalidates parse_surface_program(file)
   → Salsa invalidates file_diagnostics(file)
   ↓
4. LSP queries file_diagnostics(db, file)
   → Salsa detects invalidation
   → Calls parse_surface_program (recomputes)
   → Calls elaborate (recomputes)
   → Returns diagnostics with type error
   ↓
5. LSP post-processes diagnostics
   → Deduplication (none needed)
   → Pattern detection (suggests fix)
   ↓
6. LSP converts to LSP format
   → Creates Diagnostic with Range
   → Adds relatedInformation
   → Adds codeDescription link
   ↓
7. LSP sends PublishDiagnostics
   ↓
8. VSCode shows red squiggle
   ↓
9. User hovers, sees:
   "type mismatch: expected Nat, found Bool

   help: consider using an if expression that returns Nat

   Related: function return type declared at line 40

   Code: E0308 (click for details)"
```

### Flow B: User Runs `hwml build`

```
1. User runs `hwml build`
   ↓
2. CLI loads workspace manifest
   ↓
3. CLI creates VfsFileMap with all source files
   ↓
4. CLI queries workspace_diagnostics(db, vfs_map)
   → Salsa calls file_diagnostics(file) for each file
   → Most files cached from previous builds!
   → Returns DiagnosticCollection
   ↓
5. CLI post-processes
   → Deduplication
   → Cascading analysis
   → Pattern detection
   ↓
6. CLI renders to terminal
   → Color terminal output
   → Source snippets
   → File grouping
   → Summary statistics
   ↓
7. Terminal shows:

   error[E0308]: type mismatch
     --> src/main.hwml:42:10
      |
   42 |     return true;
      |            ^^^^ expected Nat, found Bool

   error[E0404]: not in scope
     --> src/lib.hwml:10:5
      |
   10 |     proces(x)
      |     ^^^^^^ did you mean 'process'?

   error: aborting due to 2 errors

   Found 2 error(s) across 2 file(s)

8. Exit code 1 (failure for CI/CD)
```

---

## Conclusion

This design integrates the diagnostic framework seamlessly with HWML's existing infrastructure:

✅ **Salsa integration** - Automatic incrementality, minimal recomputation
✅ **VFS independence** - Works with OsVfs, LspVfs, MemoryVfs
✅ **LSP rich features** - Related info, code links, suggestions
✅ **Multiple outputs** - Terminal, LSP, JSON, HTML
✅ **Post-processing** - Dedup, cascading, patterns, fixes
✅ **Backward compatible** - Gradual migration from old system

**Implementation:** 6 weeks, well-defined phases, measurable success metrics.

**Next Steps:** Create ADR-016 for diagnostic framework, start Phase 1 implementation.

