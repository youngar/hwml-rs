# Diagnostic Post-Processing & Rendering

**Date:** 2026-05-08  
**Status:** Design Specification  
**Context:** Holistic error analysis for HWML diagnostics  
**See Also:** `diagnostic-framework-design.md`

---

## Overview

This document specifies the **post-processing pipeline** for HWML diagnostics, transforming raw elaboration errors into optimized, user-friendly diagnostics with source code rendering, intelligent sorting, and multiple output formats.

**Key Insight:** Elaboration produces errors, but a separate post-processing phase enables holistic analysis, deduplication, root cause detection, and optimal presentation.

---

## Current State vs. Target

### Current State ✅ (Already Implemented)

```rust
// Lenient error collection (continues on errors)
pub struct ElabProgramResult<'db> {
    pub decls: Vec<ElaboratedDecl<'db>>,
    pub errors: Vec<ElabError<'db>>,  // Multiple errors collected
}

// In elab_library_with_sccs:
for scc in sccs {
    if let Err(e) = elaborate_headers(...) {
        errors.push(e);
        continue;  // Keep going!
    }
}
```

**Status:** ✅ Elaborator collects errors without fail-fast

### Target State 🎯 (To Be Implemented)

```rust
// Post-processing pipeline
let result = elab_library_with_sccs(...);

let diag_system = DiagnosticSystem::new(db);
let diagnostics = diag_system.process_errors(result.errors);
let rendered = diag_system.render_terminal(&diagnostics);

println!("{}", rendered);
```

**Status:** 🔄 Need post-processing and rendering

---

## Post-Processing Pipeline

### Architecture

```
Vec<ElabError<'db>>
      │
      ├─→ Convert to Diagnostic objects
      ├─→ Deduplicate similar errors  
      ├─→ Group related errors (cascading analysis)
      ├─→ Sort by severity/file/line
      ├─→ Add suggestions and fix-its
      ├─→ Gather source files
      │
      ▼
DiagnosticSet<'db>
```

### Phase 1: Deduplication

**Problem:** Same error reported multiple times.

**Example:**
```rust
// Type error at line 42 triggers:
// - Error from check()
// - Error from constraint solver
// - Error from zonking

// Without dedup: 3 identical errors
// With dedup: 1 error
```

**Algorithm:**
```rust
fn deduplicate(diagnostics: Vec<Diagnostic>) -> Vec<Diagnostic> {
    let mut seen = HashSet::new();
    diagnostics.into_iter()
        .filter(|d| {
            let key = (d.code, d.location.clone(), d.message.clone());
            seen.insert(key)
        })
        .collect()
}
```

### Phase 2: Cascading Analysis

**Problem:** One root error causes many cascading errors.

**Example:**
```rust
// Missing type annotation causes:
// - UnsolvedMeta ?0
// - TypeMismatch in function body
// - UnificationFailure in constraint solver
// - 5 more cascading errors

// Want to show: "Missing type annotation" (root cause)
// Suppress: 7 cascading errors
```

**Algorithm:**
```rust
fn find_root_causes(errors: &[ElabError]) -> Vec<ErrorCascade> {
    // 1. Build constraint dependency graph
    let graph = build_constraint_graph(errors);
    
    // 2. Find connected components
    let components = graph.connected_components();
    
    // 3. Identify root vs. cascading
    components.into_iter()
        .map(|component| {
            let root = find_root_in_component(&component);
            let cascaded = component.into_iter()
                .filter(|e| e != root)
                .collect();
            ErrorCascade { root, cascaded }
        })
        .collect()
}
```

### Phase 3: Intelligent Sorting

**Goal:** Present errors in optimal order for user comprehension.

**Sort Priority:**
1. **Severity:** Bug > Error > Warning > Info > Hint
2. **File:** Alphabetical by path
3. **Line:** Earlier first
4. **Column:** Left-to-right

```rust
diagnostics.sort_by(|a, b| {
    a.severity.order().cmp(&b.severity.order())
        .then(a.file_path().cmp(&b.file_path()))
        .then(a.line().cmp(&b.line()))
        .then(a.column().cmp(&b.column()))
});
```

### Phase 4: Pattern Detection & Suggestions

**Goal:** Recognize common mistakes and suggest fixes.

**Patterns Detected:**

| Pattern | Error | Suggestion |
|---------|-------|------------|
| **Forgot return** | Type mismatch (expected T, got ()) | Add explicit return |
| **Typo** | Not in scope "proces" | Did you mean "process"? |
| **Missing annotation** | Unsolved meta | Add type annotation |
| **Wrong arity** | Expected 2 args, got 3 | Check function signature |
| **Bool vs Nat** | Type mismatch | Check conditional logic |

**Implementation:**
```rust
fn detect_patterns(error: &ElabError) -> Vec<Suggestion> {
    match error {
        ElabError::TypeMismatch { expected, actual, span } => {
            if is_unit(actual) && !is_unit(expected) {
                vec![Suggestion {
                    message: "Add explicit return statement".into(),
                    fix: Some(Fix::InsertText {
                        location: span.end(),
                        text: format!("return <value>"),
                    }),
                }]
            } else {
                vec![]
            }
        }
        ElabError::NotInScope { name, .. } => {
            find_similar_names(name).map(|similar| {
                Suggestion {
                    message: format!("Did you mean '{}'?", similar),
                    fix: Some(Fix::ReplaceText {
                        range: span.clone(),
                        text: similar,
                    }),
                }
            }).collect()
        }
        _ => vec![],
    }
}
```

### Phase 5: Source File Gathering

**Goal:** Pre-load source files for rendering.

```rust
fn gather_sources(diagnostics: &[Diagnostic]) -> HashMap<PathBuf, String> {
    let mut sources = HashMap::new();
    
    for diagnostic in diagnostics {
        if let Some(path) = diagnostic.file_path() {
            sources.entry(path.clone())
                .or_insert_with(|| {
                    std::fs::read_to_string(path).unwrap_or_default()
                });
        }
    }
    
    sources
}
```

---

## Source Code Rendering

### Terminal Renderer

**Goal:** Beautiful, readable source snippets with colors.

**Features:**
- Line number gutter
- Context lines (2 before/after error)
- Caret underlines (`^^^`)
- ANSI color highlighting
- Multi-line error spans

**Example Output:**
```
error[E001]: type mismatch
  --> src/main.hwml:42:10

   38 |
   39 | fn process(x: Nat) -> Nat {
   40 |     let y = x + 1;
   41 |     let z = y * 2;
   42 |     return true;
      |            ^^^^ expected Nat, found Bool
   43 | }
   44 |
```

**Implementation:**
```rust
pub struct SourceRenderer<'db> {
    db: &'db dyn salsa::Database,
    style: RenderStyle,
    sources: HashMap<PathBuf, String>,
}

impl<'db> SourceRenderer<'db> {
    pub fn render(&self, diagnostic: &Diagnostic<'db>) -> String {
        let mut output = String::new();

        // 1. Header: error[E001]: message
        output.push_str(&self.render_header(diagnostic));

        // 2. Location: --> file:line:column
        output.push_str(&self.render_location(diagnostic));

        // 3. Source snippet with highlighting
        if let Some(snippet) = self.render_snippet(diagnostic) {
            output.push_str(&snippet);
        }

        // 4. Backtrace
        if !diagnostic.backtrace.is_empty() {
            output.push_str(&self.render_backtrace(diagnostic));
        }

        // 5. Help/suggestions
        if !diagnostic.suggestions.is_empty() {
            output.push_str(&self.render_suggestions(diagnostic));
        }

        output
    }

    fn render_snippet(&self, diagnostic: &Diagnostic<'db>) -> Option<String> {
        let location = diagnostic.location.as_ref()?;
        let source_text = self.get_source(location.source)?;

        let start_line = location.range.start.line.saturating_sub(2);
        let end_line = location.range.end.line + 2;
        let error_start = location.range.start.line;
        let error_end = location.range.end.line;

        let mut output = String::new();
        output.push('\n');

        let gutter_width = format!("{}", end_line).len();

        for line_num in start_line..=end_line {
            let line_text = self.get_line(&source_text, line_num)?;

            if line_num >= error_start && line_num <= error_end {
                // Error line - highlighted
                output.push_str(&format!(
                    "{:>width$} | {}\n",
                    self.color(line_num, Color::Blue),
                    line_text,
                    width = gutter_width
                ));

                // Add underline
                if line_num == error_start {
                    output.push_str(&self.render_underline(
                        location,
                        line_num,
                        gutter_width,
                        diagnostic.message.clone(),
                    ));
                }
            } else {
                // Context line - dimmed
                output.push_str(&format!(
                    "{:>width$} | {}\n",
                    self.color(line_num, Color::Gray),
                    self.dim(&line_text),
                    width = gutter_width
                ));
            }
        }

        Some(output)
    }

    fn render_underline(
        &self,
        location: &SourceRange,
        line_num: usize,
        gutter_width: usize,
        message: String,
    ) -> String {
        let line_text = self.get_line_at(location.source, line_num);
        let line_start_byte = self.line_start_byte(location.source, line_num);

        // Calculate visual columns (handle tabs, Unicode)
        let start_col = self.byte_to_visual_column(&line_text,
            location.range.start.offset - line_start_byte);
        let end_col = if location.range.end.line == line_num {
            self.byte_to_visual_column(&line_text,
                location.range.end.offset - line_start_byte)
        } else {
            self.visual_line_length(&line_text)
        };

        let padding = " ".repeat(gutter_width + 3 + start_col);
        let carets = "^".repeat((end_col - start_col).max(1));

        format!(
            "{}{} {}\n",
            padding,
            self.color(&carets, Color::Red),
            self.color(&message, Color::Red)
        )
    }

    fn byte_to_visual_column(&self, line: &str, byte_offset: usize) -> usize {
        // Handle tabs (expand to 4 spaces) and Unicode width
        let substr = &line[..byte_offset.min(line.len())];
        substr.chars()
            .map(|c| match c {
                '\t' => 4,
                _ => unicode_width::UnicodeWidthChar::width(c).unwrap_or(1),
            })
            .sum()
    }
}
```

### Color Schemes

```rust
pub enum RenderStyle {
    Plain,     // No colors
    Ansi,      // ANSI escape codes
    Html,      // HTML with CSS
}

pub enum Color {
    Red,       // Errors, underlines
    Yellow,    // Warnings
    Blue,      // Line numbers
    Gray,      // Context lines
    Green,     // Suggestions
    White,     // Normal text
}

impl SourceRenderer<'_> {
    fn color<T: Display>(&self, text: T, color: Color) -> String {
        match self.style {
            RenderStyle::Plain => text.to_string(),
            RenderStyle::Ansi => {
                let code = match color {
                    Color::Red => "\x1b[31m",
                    Color::Yellow => "\x1b[33m",
                    Color::Blue => "\x1b[34m",
                    Color::Gray => "\x1b[90m",
                    Color::Green => "\x1b[32m",
                    Color::White => "\x1b[37m",
                };
                format!("{}{}\x1b[0m", code, text)
            }
            RenderStyle::Html => {
                let class = format!("{:?}", color).to_lowercase();
                format!("<span class=\"{}\">{}</span>", class, text)
            }
        }
    }
}
```

---

## Output Formats

### 1. Terminal (Human-Readable)

```rust
pub fn render_terminal(diagnostics: &DiagnosticSet) -> String {
    let mut output = String::new();

    // Summary
    output.push_str(&DiagnosticStats::from(diagnostics).render());
    output.push_str("\n\n");

    // File summary
    output.push_str(&DiagnosticsByFile::from(diagnostics).render_summary());
    output.push_str("\n\n");

    // Detailed errors
    for diagnostic in &diagnostics.diagnostics {
        output.push_str(&SourceRenderer::new().render(diagnostic));
        output.push_str("\n");
    }

    output
}
```

### 2. LSP (IDE Integration)

```rust
pub fn to_lsp(diagnostics: &DiagnosticSet)
    -> HashMap<Url, Vec<lsp_types::Diagnostic>>
{
    let mut by_uri = HashMap::new();

    for diagnostic in &diagnostics.diagnostics {
        let uri = diagnostic.location.source.to_lsp_uri()?;
        let lsp_diag = lsp_types::Diagnostic {
            range: diagnostic.location.to_lsp_range(),
            severity: Some(diagnostic.severity.to_lsp()),
            code: Some(NumberOrString::String(diagnostic.code.to_string())),
            code_description: Some(CodeDescription {
                href: Url::parse(&format!(
                    "https://hwml-lang.org/errors/{}",
                    diagnostic.code
                )).unwrap(),
            }),
            source: Some("hwml".to_string()),
            message: diagnostic.message.clone(),
            related_information: Some(
                diagnostic.backtrace_to_related_info()
            ),
            tags: None,
            data: None,
        };

        by_uri.entry(uri).or_insert_with(Vec::new).push(lsp_diag);
    }

    by_uri
}
```

### 3. JSON (Machine-Readable)

```rust
#[derive(Serialize)]
pub struct DiagnosticJson {
    pub severity: String,
    pub code: String,
    pub message: String,
    pub file: Option<String>,
    pub line: Option<usize>,
    pub column: Option<usize>,
    pub backtrace: Vec<FrameJson>,
    pub suggestions: Vec<String>,
}

pub fn to_json(diagnostics: &DiagnosticSet) -> String {
    let json_diags: Vec<_> = diagnostics.diagnostics.iter()
        .map(|d| d.to_json())
        .collect();
    serde_json::to_string_pretty(&json_diags).unwrap()
}
```

**Example:**
```json
[
  {
    "severity": "Error",
    "code": "E001",
    "message": "type mismatch",
    "file": "src/main.hwml",
    "line": 42,
    "column": 10,
    "backtrace": [...],
    "suggestions": ["consider using an if expression"]
  }
]
```

### 4. HTML (Web Reports)

```rust
pub fn to_html(diagnostics: &DiagnosticSet) -> String {
    let mut html = String::from(r#"
<!DOCTYPE html>
<html>
<head>
    <title>HWML Diagnostic Report</title>
    <style>
        .error { color: #e74c3c; }
        .warning { color: #f39c12; }
        .line-number { color: #3498db; }
        .context { color: #95a5a6; }
        pre { background: #2c3e50; color: #ecf0f1; padding: 1em; }
    </style>
</head>
<body>
"#);

    let renderer = SourceRenderer::new(RenderStyle::Html);
    for diagnostic in &diagnostics.diagnostics {
        html.push_str(&renderer.render(diagnostic));
    }

    html.push_str("</body></html>");
    html
}
```

---

## Implementation Checklist

### Phase 1: Post-Processing (Week 1)
- [ ] `DiagnosticPostProcessor` struct
- [ ] Deduplication algorithm
- [ ] Cascading error analysis
- [ ] Intelligent sorting
- [ ] Pattern detection
- [ ] Suggestion generation

### Phase 2: Rendering (Week 2)
- [ ] `SourceRenderer` struct
- [ ] Multi-line snippet rendering
- [ ] Caret underline generation
- [ ] ANSI color support
- [ ] Unicode width handling
- [ ] Tab expansion

### Phase 3: Output Formats (Week 2)
- [ ] Terminal format
- [ ] LSP conversion
- [ ] JSON export
- [ ] HTML reports
- [ ] Statistics summary
- [ ] File grouping

### Phase 4: Integration (Week 3)
- [ ] Wire into `elab_library_with_sccs`
- [ ] CLI flags (`--format=`)
- [ ] LSP integration
- [ ] Tests for all formats
- [ ] Performance benchmarks

---

## References

- **Main design:** `diagnostic-framework-design.md`
- **Summary:** `DIAGNOSTIC-SYSTEM-SUMMARY.md`
- **Asai review:** `asai-detailed-review.md`
- **Current code:** `crates/hwml-elab/src/error.rs`

