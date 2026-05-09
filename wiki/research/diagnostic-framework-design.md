# Diagnostic Framework Design (Inspired by Asai)

**Date:** 2026-05-08  
**Status:** Design Research - Ready for ADR  
**Context:** Designing HWML's production-quality diagnostic system  
**Source:** `external/asai/` - RedPRL diagnostic library

---

## Overview

This document presents a design for HWML's diagnostic framework, inspired by the **Asai (浅い "shallow")** library from the RedPRL team. Asai provides a comprehensive approach to compiler diagnostics with five independent parameters and strong support for Unicode rendering.

**Key Insight:** Diagnostics should be composable, structured, and provide multiple independent dimensions of information (severity, location, backtrace, error codes, extra remarks) that can be specified independently.

---

## Core Design Principles (from Asai)

### 1. Five Independent Parameters

Every diagnostic should allow independent specification of:

1. **Fatality** - Whether the program terminates after emission (`emit` vs `fatal`)
2. **Error Code** - Short, Google-able code (e.g., `E001` not "type-checking error")
3. **Severity** - How serious: `Error`, `Warning`, `Info`, `Hint`, or `Bug`
4. **Backtrace** - Stack of elaboration/compilation operations
5. **Extra Remarks** - Additional notes with location information

**Design Philosophy:** Each parameter should be orthogonal and specifiable independently.

### 2. Free-Form vs Structured Reporting

**Two modes supported:**

- **Free-form:** Direct text explanations, messages as loose categorization
- **Structured:** Messages are fully typed (variant types), explanation determined by message

**HWML Application:** Use structured reporting with typed error variants (`ElabError`, `ParseError`, etc.)

### 3. Location Inheritance

**Problem:** Manually threading location through every function is verbose and error-prone.

**Asai's Solution:** 
- Remember locations from backtrace frames (`trace ~loc`)
- Use innermost location as default for `emit`/`fatal`
- Inner backtrace frames don't inherit location (avoid duplication)

```ocaml
Reporter.trace ~loc "outer trace" @@ fun () ->
  Reporter.trace "inner trace" @@ fun () ->  (* no duplicate loc *)
    Reporter.emit Error "message"  (* inherits outer loc *)
```

### 4. Unicode Display Stability (Level 2)

**Asai's Choice:** No column numbers, only byte offsets

**Rationale:**
- Visual width of Unicode characters is unpredictable
- Emoji sequences vary by platform (🏴‍☠️ may show as 🏴☠️)
- East Asian "Ambiguous" width characters
- Column-based highlighting breaks with non-ASCII

**Display Stability Level 2:** Assumptions allowed:
- Halfwidth/Narrow characters have same width
- Fullwidth/Wide characters have same width  
- Box-drawing "Ambiguous" characters have same width
- Equivalent grapheme clusters have same width

**Result:** Beautiful Unicode art that works reliably across platforms.

---

## Asai Architecture

### Core Types

```ocaml
(* Severity levels *)
type severity = Hint | Info | Warning | Error | Bug

(* Range: byte-oriented positions *)
type position = {
  source : source;         (* File or String *)
  offset : int;            (* 0-indexed byte offset *)
  start_of_line : int;     (* Byte offset to line start *)
  line_num : int;          (* 1-indexed line number *)
}
type range = position * position

(* Located text with optional range *)
type loctext = { loc : range option; value : text }

(* Backtrace as backward list of loctext *)
type backtrace = loctext bwd

(* Diagnostic structure *)
type 'message diagnostic = {
  severity : severity;
  message : 'message;          (* Structured message type *)
  explanation : loctext;        (* Free-form explanation *)
  backtrace : backtrace;        (* Call stack *)
  extra_remarks : loctext bwd;  (* Additional notes *)
}
```

### Message Interface

```ocaml
module type Message = sig
  type t  (* User-defined message enum *)
  
  val default_severity : t -> severity
  val short_code : t -> string  (* "E001" not "type-checking error" *)
end
```

**HWML Equivalent:**
```rust
pub enum ElabMessage {
    TypeMismatch,    // E001
    NotInScope,      // E002
    UnsolvedMeta,    // E003
    // ...
}

impl ElabMessage {
    fn severity(&self) -> Severity { /* ... */ }
    fn code(&self) -> &'static str { /* ... */ }
}
```

---

## Effect-Based Dynamic Scoping

**Asai's Approach (OCaml):**

Uses algebraic effects (`Algaeff.Reader`) for automatic context threading:

```ocaml
module Traces = Algaeff.Reader.Make(
  struct type t = range option * backtrace end
)

let trace_text ?loc text f =
  Traces.scope @@ fun (l, bt) ->
    let new_loc = match loc with None -> l | Some _ -> loc in
    let new_bt = bt <: {loc; value = text} in
    f ()
```

**Benefits:**
- No manual passing of context
- Automatic stack management
- Location inheritance "for free"

**HWML Adaptation (Rust):**

Use RAII pattern with explicit context:

```rust
pub struct ElabContext<'db> {
    trace_stack: Vec<ElabFrame<'db>>,
    current_location: Option<SourceRange<'db>>,
}

impl<'db> ElabContext<'db> {
    pub fn trace<'a>(&'a mut self, desc: String, loc: SourceRange<'db>) 
        -> TraceGuard<'a, 'db> 
    {
        self.current_location = Some(loc.clone());
        self.trace_stack.push(ElabFrame { desc, loc });
        TraceGuard { context: self }
    }
}

pub struct TraceGuard<'a, 'db> {
    context: &'a mut ElabContext<'db>,
}

impl<'a, 'db> Drop for TraceGuard<'a, 'db> {
    fn drop(&mut self) {
        self.context.trace_stack.pop();
    }
}
```

**Usage:**
```rust
pub fn check(...) -> Result<...> {
    let _guard = elab.context.trace(
        format!("checking against {}", ty),
        location,
    );
    // _guard automatically pops on return/error
}
```

---

## Byte-Level Location Tracking

**Asai's Position:** All positions should be **byte-oriented** (not characters, not code units, not grapheme clusters).

**Alternatives Rejected:**

| Unit | Problem |
|------|---------|
| **Unicode characters** (scalar values) | Linear time to count from bytes; doesn't match visual perception |
| **UTF-16 code units** | LSP default; worse than Unicode chars; surrogate pairs complicate |
| **Grapheme clusters** | Complex, locale-dependent, linear time; unreliable for positions |
| **Visual columns** | Ill-defined; unpredictable Unicode widths; heuristics fail on emoji |

**Why Bytes Win:**
- ✅ Well-defined, unambiguous
- ✅ Constant-time access from file/string
- ✅ Matches how parsers (like `ocamllex`) work
- ✅ No locale or platform dependencies
- ✅ Works with any encoding if specified

**HWML Status:** ✅ Already byte-based (see `ADR-014-byte-level-location-tracking`)

---

## Compositionality: Adopting Library Diagnostics

**Problem:** How to integrate diagnostics from libraries that also use `asai`?

**Asai's Solution:**

```ocaml
(* Library has its own message type *)
module CoolLib = struct
  type message = LibError | LibWarning
  module Reporter = Asai.Reporter.Make(struct ... end)
end

(* Application adopts library diagnostics *)
Reporter.adopt
  (Diagnostic.map message_mapper)  (* Transform lib messages *)
  CoolLib.Reporter.run             (* Library's runner *)
  @@ fun () -> CoolLib.do_something ()
```

**Key Features:**
- Backtrace from library includes application's outer backtrace
- Location inheritance carries over
- Libraries and applications can use different message types

**HWML Application:**
- Less relevant (no effect system)
- But: Consider when integrating external parsers/tools
- Message mapping still useful for categorization

---

## Reporter API Pattern

### Emitting Diagnostics

```ocaml
(* Non-fatal emission *)
val emit : ?severity:severity -> ?loc:range -> ?backtrace:backtrace
        -> ?extra_remarks:loctext list
        -> message -> string -> unit

val emitf : ... -> message -> ('a, formatter, unit, unit) format4 -> 'a

(* Fatal emission - aborts computation *)
val fatal : ?severity:severity -> ?loc:range -> ?backtrace:backtrace
         -> ?extra_remarks:loctext list
         -> message -> string -> 'a

val fatalf : ... -> message -> ('a, formatter, unit, 'b) format4 -> 'a
```

### Backtrace Management

```ocaml
(* Add trace frame *)
val trace : ?loc:range -> string -> (unit -> 'a) -> 'a
val tracef : ?loc:range -> ('a, formatter, unit, (unit -> 'b) -> 'b) format4 -> 'a

(* Query backtrace *)
val get_backtrace : unit -> backtrace
val with_backtrace : backtrace -> (unit -> 'a) -> 'a
```

### Location Management

```ocaml
(* Get current default location *)
val get_loc : unit -> range option

(* Set default location *)
val with_loc : range option -> (unit -> 'a) -> 'a

(* Merge with current location (None keeps current) *)
val merge_loc : range option -> (unit -> 'a) -> 'a
```

---

## HWML Application Strategy

### Phase 1: Core Infrastructure (1-2 days)

**Goal:** Establish diagnostic types and basic machinery

```rust
// Severity levels
pub enum Severity {
    Hint,
    Info,
    Warning,
    Error,
    Bug,  // Internal compiler bug
}

// Backtrace frame
pub struct DiagnosticFrame<'db> {
    description: String,
    location: Option<SourceRange<'db>>,
}

// Diagnostic context (in Elaborator)
pub struct DiagnosticContext<'db> {
    trace_stack: Vec<DiagnosticFrame<'db>>,
    current_location: Option<SourceRange<'db>>,
}

// Unified diagnostic type
pub struct Diagnostic<'db> {
    severity: Severity,
    code: &'static str,
    message: String,
    location: Option<SourceRange<'db>>,
    backtrace: Vec<DiagnosticFrame<'db>>,
    extra_remarks: Vec<(String, Option<SourceRange<'db>>)>,
}
```

### Phase 2: Error Code System (1 day)

**Goal:** Add Google-able error codes to all error types

```rust
impl<'db> ElabError<'db> {
    pub fn code(&self) -> &'static str {
        match self {
            ElabError::TypeMismatch { .. } => "E001",
            ElabError::NotInScope { .. } => "E002",
            ElabError::CannotInfer { .. } => "E003",
            ElabError::UnificationFailure { .. } => "E004",
            ElabError::OccursCheck { .. } => "E005",
            ElabError::UnsolvedMeta { .. } => "E006",
            // ... etc
        }
    }

    pub fn severity(&self) -> Severity {
        match self {
            ElabError::NotImplemented { .. } => Severity::Warning,
            _ => Severity::Error,
        }
    }

    pub fn to_diagnostic(&self, context: &DiagnosticContext<'db>) -> Diagnostic<'db> {
        Diagnostic {
            severity: self.severity(),
            code: self.code(),
            message: self.primary_message(),
            location: self.location().or_else(|| context.current_location.clone()),
            backtrace: context.trace_stack.clone(),
            extra_remarks: self.extra_remarks(),
        }
    }
}
```

### Phase 3: RAII Trace Guards (2-3 days)

**Goal:** Ergonomic backtrace instrumentation

```rust
impl<'db> DiagnosticContext<'db> {
    pub fn trace<'a>(
        &'a mut self,
        description: impl Into<String>,
        location: Option<SourceRange<'db>>,
    ) -> TraceGuard<'a, 'db> {
        if let Some(loc) = location.clone() {
            self.current_location = Some(loc.clone());
        }
        self.trace_stack.push(DiagnosticFrame {
            description: description.into(),
            location,
        });
        TraceGuard { context: self }
    }
}

// Usage in elaboration
pub fn check<'db>(
    db: &'db Db,
    elab: &mut Elaborator<'_, 'db>,
    expr: &Expression,
    expected: RcTy<'db>,
) -> Result<RcSyntax<'db>, ElabError<'db>> {
    let loc = expr_location(db, expr);
    let _guard = elab.diagnostics.trace(
        format!("checking expression against {}", display_ty(&expected)),
        Some(loc),
    );

    // ... elaboration logic
    // _guard automatically pops on return or error
}
```

### Phase 4: Enhanced Display (1-2 days)

**Goal:** Beautiful, informative error output

```rust
impl<'db> Display for Diagnostic<'db> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        // Error code and severity
        write!(f, "{}[{}]: ",
            match self.severity {
                Severity::Error => "error",
                Severity::Warning => "warning",
                Severity::Info => "info",
                Severity::Hint => "hint",
                Severity::Bug => "internal compiler bug",
            },
            self.code
        )?;

        // Primary message with location
        writeln!(f, "{}", self.message)?;
        if let Some(loc) = &self.location {
            writeln!(f, "  --> {}:{}:{}",
                loc.source.path(),
                loc.range.start.line,
                loc.range.start.column
            )?;
        }

        // Backtrace
        if !self.backtrace.is_empty() {
            writeln!(f, "\nelaboration backtrace:")?;
            for (i, frame) in self.backtrace.iter().rev().enumerate() {
                write!(f, "  {}: {}", i, frame.description)?;
                if let Some(loc) = &frame.location {
                    write!(f, " at {}:{}:{}",
                        loc.source.path(),
                        loc.range.start.line,
                        loc.range.start.column
                    )?;
                }
                writeln!(f)?;
            }
        }

        // Extra remarks
        if !self.extra_remarks.is_empty() {
            writeln!(f, "\nnotes:")?;
            for (remark, loc) in &self.extra_remarks {
                write!(f, "  = note: {}", remark)?;
                if let Some(loc) = loc {
                    write!(f, " at {}:{}:{}",
                        loc.source.path(),
                        loc.range.start.line,
                        loc.range.start.column
                    )?;
                }
                writeln!(f)?;
            }
        }

        Ok(())
    }
}
```

**Example output:**
```
error[E001]: type mismatch at src/main.hwml:42:10
  expected: Nat
  got:      Bool

elaboration backtrace:
  0: checking expression against Nat at src/main.hwml:42:10
  1: checking function return type at src/main.hwml:40:5
  2: checking definition 'process' at src/main.hwml:38:1
  3: elaborating module '/main' at src/main.hwml:1:1

notes:
  = note: Nat is defined at src/prelude.hwml:10:1
  = note: consider using `if` expression to return Nat
```

---

## Integration with Existing HWML Systems

### Constraint Provenance (Already Exists)

HWML's unique strength: `ConstraintOrigin` and `MetaProvenance` side-tables.

**Keep and enhance:**
```rust
pub struct Diagnostic<'db> {
    // ... standard fields ...

    // HWML-specific: constraint context
    constraint_origin: Option<ConstraintOrigin<'db>>,
    blocking_constraints: Vec<ConstraintId>,
    meta_provenance: Option<MetaProvenance<'db>>,
}
```

**Combined output:**
```
error[E006]: unsolved metavariable ?42

elaboration backtrace:
  0: checking return type at src/main.hwml:100:10
  1: checking function 'compute' at src/main.hwml:95:1

constraint context:
  origin: underscore placeholder at src/main.hwml:100:10
  created by: C10 (type annotation)
  blocking: C10, C15, C20

provenance chain:
  ?42 <- created from underscore at src/main.hwml:100:10
  ?40 <- parameter type inference at src/main.hwml:95:15
```

### LSP Integration

**Diagnostic → LSP Diagnostic:**
```rust
impl<'db> Diagnostic<'db> {
    pub fn to_lsp_diagnostic(&self) -> lsp_types::Diagnostic {
        lsp_types::Diagnostic {
            range: self.location.map(|loc| loc.to_lsp_range())
                       .unwrap_or_default(),
            severity: Some(match self.severity {
                Severity::Error => lsp_types::DiagnosticSeverity::ERROR,
                Severity::Warning => lsp_types::DiagnosticSeverity::WARNING,
                Severity::Info => lsp_types::DiagnosticSeverity::INFORMATION,
                Severity::Hint => lsp_types::DiagnosticSeverity::HINT,
                Severity::Bug => lsp_types::DiagnosticSeverity::ERROR,
            }),
            code: Some(lsp_types::NumberOrString::String(self.code.to_string())),
            message: self.message.clone(),
            related_information: self.backtrace_to_related_info(),
            // ...
        }
    }
}
```

---

## Comparison: Asai vs HWML

| Feature | Asai (OCaml) | HWML (Proposed) |
|---------|--------------|-----------------|
| **Effect Handlers** | ✅ Algebraic effects | ❌ RAII guards instead |
| **Elaboration Backtrace** | ✅ Built-in | ✅ Adopting pattern |
| **Constraint Provenance** | ❌ Not present | ✅ **Unique to HWML** |
| **Meta Provenance** | ❌ Not present | ✅ **Unique to HWML** |
| **Error Codes** | ✅ Built-in | ✅ Adopting pattern |
| **Location Inheritance** | ✅ Automatic (effects) | ✅ Via context |
| **Byte-Based Positions** | ✅ Core design | ✅ Already implemented |
| **Unicode Stability** | ✅ Level 2 | 🔄 To be enhanced |
| **Compositionality** | ✅ Library adoption | ⚠️ Less relevant (no effects) |

**Result:** HWML will have **best-in-class diagnostics** combining:
- Asai's elaboration backtrace
- HWML's constraint/meta provenance
- Rust's RAII safety guarantees

---

## References

- **Asai source:** `external/asai/`
- **Asai documentation:** https://redprl.org/asai/asai/
- **Design principles:** `external/asai/docs/design.mld`
- **STLC example:** `external/asai/examples/stlc/`
- **Related ADRs:** ADR-014 (byte-level tracking), ADR-015 (provenance architecture)
- **Related research:** `asai-detailed-review.md`, `asai-vs-hwml-comparison.md`

---

## Next Steps

1. **Create ADR:** Propose diagnostic framework as formal architecture decision
2. **Document error codes:** Create `docs/error-codes.md` with catalog
3. **Implementation phases:** Follow 4-phase plan (3-4 weeks total)
4. **Testing strategy:** Integration tests for complex error scenarios
5. **LSP integration:** Ensure diagnostics work beautifully in editors
6. **Documentation:** User-facing guide on understanding HWML errors

**Estimated Total Effort:** 3-4 weeks for production-ready diagnostic system

**Expected Outcome:** HWML error messages on par with or exceeding Rust, GHC, and Lean 4.

---

## Holistic Error Analysis & Post-Processing

### Current State (Already Implemented)

✅ **Lenient Error Collection:** HWML already collects errors instead of fail-fast:
```rust
pub struct ElabProgramResult<'db> {
    pub decls: Vec<ElaboratedDecl<'db>>,
    pub errors: Vec<ElabError<'db>>,  // Multiple errors collected
}

// In elab_library_with_sccs:
for (scc_idx, scc) in sccs.iter().enumerate() {
    // Catch errors, push to Vec, continue
    if let Err(e) = elaborate_headers(...) {
        errors.push(e);
        continue;  // Keep going!
    }
}
```

### Required Enhancements

#### 1. Error Post-Processing Pipeline

**Goal:** Transform raw elaboration errors into optimized diagnostics for users.

```rust
/// Post-processor for holistic error analysis
pub struct DiagnosticPostProcessor<'db> {
    db: &'db dyn salsa::Database,
}

impl<'db> DiagnosticPostProcessor<'db> {
    /// Process raw errors into final diagnostics
    pub fn process(&self, errors: Vec<ElabError<'db>>) -> DiagnosticSet<'db> {
        let mut diagnostics = Vec::new();

        // 1. Convert to diagnostic objects
        for error in errors {
            diagnostics.push(self.to_diagnostic(error));
        }

        // 2. Deduplicate similar errors
        diagnostics = self.deduplicate(diagnostics);

        // 3. Group related errors
        let groups = self.group_related(diagnostics);

        // 4. Prioritize / rank errors
        let prioritized = self.prioritize(groups);

        // 5. Add suggestions and fix-its
        let enhanced = self.add_suggestions(prioritized);

        DiagnosticSet {
            diagnostics: enhanced,
            source_files: self.gather_sources(&enhanced),
        }
    }

    /// Deduplicate errors (e.g., same type mismatch reported multiple times)
    fn deduplicate(&self, mut diagnostics: Vec<Diagnostic<'db>>)
        -> Vec<Diagnostic<'db>>
    {
        use std::collections::HashSet;
        let mut seen = HashSet::new();
        diagnostics.retain(|d| {
            let key = (d.code, d.location.clone(), d.message.clone());
            seen.insert(key)
        });
        diagnostics
    }

    /// Group related errors (e.g., cascading type errors from one root cause)
    fn group_related(&self, diagnostics: Vec<Diagnostic<'db>>)
        -> Vec<DiagnosticGroup<'db>>
    {
        // Analyze constraint graph to find root causes
        // Group cascading errors under primary error
        // Use meta provenance to link related issues
        todo!()
    }

    /// Prioritize errors (show most important first)
    fn prioritize(&self, groups: Vec<DiagnosticGroup<'db>>)
        -> Vec<DiagnosticGroup<'db>>
    {
        // Sort by:
        // 1. Root causes before cascading errors
        // 2. Errors before warnings
        // 3. Earlier in source before later
        // 4. User code before generated code
        todo!()
    }

    /// Add suggestions and automated fixes
    fn add_suggestions(&self, groups: Vec<DiagnosticGroup<'db>>)
        -> Vec<DiagnosticGroup<'db>>
    {
        // Pattern matching on error types:
        // - Type mismatch -> suggest coercion or fix
        // - Not in scope -> suggest similar names (typo detection)
        // - Unsolved meta -> suggest adding annotation
        todo!()
    }
}
```

#### 2. Source Code Rendering

**Goal:** Show source snippets with diagnostics (like Rust/GHC).

```rust
/// Renders source code with diagnostic annotations
pub struct SourceRenderer<'db> {
    db: &'db dyn salsa::Database,
    style: RenderStyle,
}

#[derive(Clone, Copy)]
pub enum RenderStyle {
    /// Plain text (for CLI)
    Plain,
    /// ANSI colors (for terminal)
    Ansi,
    /// Rich HTML (for IDE/web)
    Html,
}

impl<'db> SourceRenderer<'db> {
    /// Render diagnostic with source context
    pub fn render(&self, diagnostic: &Diagnostic<'db>) -> RenderedDiagnostic {
        let mut output = String::new();

        // 1. Header line with code and location
        output.push_str(&self.render_header(diagnostic));

        // 2. Source snippet with highlighting
        if let Some(snippet) = self.render_source_snippet(diagnostic) {
            output.push_str(&snippet);
        }

        // 3. Additional notes and suggestions
        output.push_str(&self.render_notes(diagnostic));

        RenderedDiagnostic { text: output }
    }

    /// Render source snippet with multi-line highlighting
    fn render_source_snippet(&self, diagnostic: &Diagnostic<'db>)
        -> Option<String>
    {
        let location = diagnostic.location.as_ref()?;
        let source = self.get_source_text(location.source)?;

        // Calculate line range (show 2 lines before/after)
        let start_line = location.range.start.line.saturating_sub(2);
        let end_line = location.range.end.line + 2;

        let mut output = String::new();

        // Line number gutter width
        let gutter_width = format!("{}", end_line).len();

        for line_num in start_line..=end_line {
            let line_text = self.get_line(&source, line_num)?;

            // Line number gutter
            if line_num >= location.range.start.line
                && line_num <= location.range.end.line
            {
                // Highlight line with diagnostic
                output.push_str(&format!(
                    "{:>width$} | {}\n",
                    line_num,
                    self.colorize(&line_text, Color::White),
                    width = gutter_width
                ));

                // Add caret underline
                output.push_str(&self.render_underline(
                    location,
                    line_num,
                    gutter_width
                ));
            } else {
                // Context line (dimmed)
                output.push_str(&format!(
                    "{:>width$} | {}\n",
                    line_num,
                    self.colorize(&line_text, Color::Gray),
                    width = gutter_width
                ));
            }
        }

        Some(output)
    }

    /// Render underline with carets (^^^) and message
    fn render_underline(
        &self,
        location: &SourceRange<'db>,
        line_num: usize,
        gutter_width: usize,
    ) -> String {
        // Calculate column positions (byte->column conversion)
        let line_start_byte = self.get_line_start_byte(location.source, line_num);
        let start_col = location.range.start.offset - line_start_byte;
        let end_col = if location.range.end.line == line_num {
            location.range.end.offset - line_start_byte
        } else {
            self.get_line_length(location.source, line_num)
        };

        let padding = " ".repeat(gutter_width + 3 + start_col);
        let carets = "^".repeat(end_col - start_col);

        format!("{}{}\n", padding, self.colorize(&carets, Color::Red))
    }

    /// Get source text for a file
    fn get_source_text(&self, source: Source<'db>) -> Option<String> {
        match source.info(self.db) {
            SourceInfo::File(path) => {
                std::fs::read_to_string(path).ok()
            }
            SourceInfo::Synthetic(_) => None,
        }
    }
}
```

**Example Output:**
```
error[E001]: type mismatch
  --> src/main.hwml:42:10

   40 | fn process(x: Nat) -> Nat {
   41 |     let y = x + 1;
   42 |     return true;
      |            ^^^^ expected Nat, found Bool
   43 | }

elaboration backtrace:
  0: checking expression against Nat at src/main.hwml:42:10
  1: checking function return type at src/main.hwml:40:23

help: consider using an `if` expression
   42 |     return if condition { 0 } else { 1 };
```

#### 3. Diagnostic Sorting & Grouping

**Goal:** Present errors in optimal order for user comprehension.

```rust
/// Sort diagnostics by multiple criteria
pub fn sort_diagnostics(diagnostics: &mut Vec<Diagnostic>) {
    diagnostics.sort_by(|a, b| {
        // 1. Primary: Severity (Error > Warning > Info > Hint)
        let severity_order = a.severity.order().cmp(&b.severity.order());
        if severity_order != std::cmp::Ordering::Equal {
            return severity_order;
        }

        // 2. Secondary: File path (alphabetical)
        let file_a = a.location.as_ref().map(|l| l.source.path());
        let file_b = b.location.as_ref().map(|l| l.source.path());
        let file_order = file_a.cmp(&file_b);
        if file_order != std::cmp::Ordering::Equal {
            return file_order;
        }

        // 3. Tertiary: Line number (earlier first)
        let line_a = a.location.as_ref().map(|l| l.range.start.line);
        let line_b = b.location.as_ref().map(|l| l.range.start.line);
        let line_order = line_a.cmp(&line_b);
        if line_order != std::cmp::Ordering::Equal {
            return line_order;
        }

        // 4. Quaternary: Column number (left-to-right)
        let col_a = a.location.as_ref().map(|l| l.range.start.column);
        let col_b = b.location.as_ref().map(|l| l.range.start.column);
        col_a.cmp(&col_b)
    });
}

impl Severity {
    fn order(&self) -> u8 {
        match self {
            Severity::Bug => 0,      // Internal bugs first
            Severity::Error => 1,    // Then errors
            Severity::Warning => 2,  // Then warnings
            Severity::Info => 3,     // Then info
            Severity::Hint => 4,     // Hints last
        }
    }
}
```

#### 4. Error Grouping by File

**Goal:** Group errors by file for better navigation.

```rust
/// Group diagnostics by source file
pub struct DiagnosticsByFile<'db> {
    pub files: BTreeMap<PathBuf, Vec<Diagnostic<'db>>>,
}

impl<'db> DiagnosticsByFile<'db> {
    pub fn new(diagnostics: Vec<Diagnostic<'db>>) -> Self {
        let mut files = BTreeMap::new();

        for diagnostic in diagnostics {
            if let Some(location) = &diagnostic.location {
                if let SourceInfo::File(path) = location.source.info() {
                    files.entry(path.clone())
                        .or_insert_with(Vec::new)
                        .push(diagnostic);
                }
            }
        }

        // Sort within each file
        for diagnostics in files.values_mut() {
            diagnostics.sort_by_key(|d| {
                d.location.as_ref().map(|l| (l.range.start.line, l.range.start.column))
            });
        }

        DiagnosticsByFile { files }
    }

    /// Render summary showing errors per file
    pub fn render_summary(&self) -> String {
        let mut output = String::new();

        let total_errors = self.count_by_severity(Severity::Error);
        let total_warnings = self.count_by_severity(Severity::Warning);

        output.push_str(&format!(
            "Found {} error(s) and {} warning(s) across {} file(s)\n\n",
            total_errors,
            total_warnings,
            self.files.len()
        ));

        for (path, diagnostics) in &self.files {
            let errors = diagnostics.iter()
                .filter(|d| d.severity == Severity::Error)
                .count();
            let warnings = diagnostics.iter()
                .filter(|d| d.severity == Severity::Warning)
                .count();

            output.push_str(&format!(
                "  {} - {} error(s), {} warning(s)\n",
                path.display(),
                errors,
                warnings
            ));
        }

        output
    }
}
```

**Example Summary:**
```
Found 5 error(s) and 3 warning(s) across 3 file(s)

  src/main.hwml - 2 error(s), 1 warning(s)
  src/lib.hwml - 2 error(s), 2 warning(s)
  src/utils.hwml - 1 error(s), 0 warning(s)
```

#### 5. Advanced Error Analysis

**Goal:** Detect cascading errors, root causes, and provide intelligent suggestions.

```rust
/// Analyzes error patterns for better diagnostics
pub struct ErrorAnalyzer<'db> {
    db: &'db dyn salsa::Database,
}

impl<'db> ErrorAnalyzer<'db> {
    /// Detect cascading errors from a single root cause
    pub fn find_root_causes(&self, errors: &[ElabError<'db>])
        -> Vec<ErrorCascade<'db>>
    {
        // Build dependency graph from constraint provenance
        let mut graph = ErrorDependencyGraph::new();

        for (idx, error) in errors.iter().enumerate() {
            // Extract constraint origins
            if let Some(origins) = self.get_constraint_origins(error) {
                for origin in origins {
                    // Link errors through shared metavariables
                    graph.add_edge(origin.meta_id, idx);
                }
            }
        }

        // Find connected components (error cascades)
        graph.find_cascades()
    }

    /// Detect common error patterns
    pub fn detect_patterns(&self, error: &ElabError<'db>)
        -> Vec<ErrorPattern>
    {
        let mut patterns = Vec::new();

        match error {
            ElabError::TypeMismatch { expected, actual, .. } => {
                // Check for common mismatches
                if self.is_unit_vs_value(expected, actual) {
                    patterns.push(ErrorPattern::ForgotReturn);
                }
                if self.is_bool_vs_nat(expected, actual) {
                    patterns.push(ErrorPattern::ConditionNotBool);
                }
            }
            ElabError::NotInScope { name, .. } => {
                // Find similar names (typo detection)
                if let Some(suggestions) = self.find_similar_names(name) {
                    patterns.push(ErrorPattern::PossibleTypo(suggestions));
                }
            }
            ElabError::UnsolvedMeta { .. } => {
                // Suggest adding type annotation
                patterns.push(ErrorPattern::NeedsAnnotation);
            }
            _ => {}
        }

        patterns
    }

    /// Find similar names for typo detection (Levenshtein distance)
    fn find_similar_names(&self, name: &str) -> Option<Vec<String>> {
        // Get all names in scope
        let in_scope = self.get_names_in_scope();

        // Calculate edit distance
        let mut candidates: Vec<_> = in_scope
            .into_iter()
            .map(|n| (n.clone(), levenshtein_distance(name, &n)))
            .filter(|(_, dist)| *dist <= 3)  // Max 3 edits
            .collect();

        candidates.sort_by_key(|(_, dist)| *dist);

        if candidates.is_empty() {
            None
        } else {
            Some(candidates.into_iter().map(|(n, _)| n).take(3).collect())
        }
    }
}

/// Represents a cascade of related errors
pub struct ErrorCascade<'db> {
    pub root: ElabError<'db>,       // The primary error
    pub cascaded: Vec<ElabError<'db>>,  // Errors caused by root
}

/// Common error patterns detected
pub enum ErrorPattern {
    ForgotReturn,
    ConditionNotBool,
    PossibleTypo(Vec<String>),
    NeedsAnnotation,
    MissingImport,
    WrongArity { expected: usize, got: usize },
}
```

#### 6. LSP Integration: Diagnostics as Structured Data

**Goal:** Provide rich diagnostics to LSP for IDE integration.

```rust
/// Convert to LSP diagnostic format
impl<'db> Diagnostic<'db> {
    pub fn to_lsp(&self) -> lsp_types::Diagnostic {
        use lsp_types::*;

        let range = self.location
            .as_ref()
            .map(|loc| loc.to_lsp_range())
            .unwrap_or_default();

        lsp_types::Diagnostic {
            range,
            severity: Some(match self.severity {
                Severity::Error => DiagnosticSeverity::ERROR,
                Severity::Warning => DiagnosticSeverity::WARNING,
                Severity::Info => DiagnosticSeverity::INFORMATION,
                Severity::Hint => DiagnosticSeverity::HINT,
                Severity::Bug => DiagnosticSeverity::ERROR,
            }),
            code: Some(NumberOrString::String(self.code.to_string())),
            code_description: Some(CodeDescription {
                href: Url::parse(&format!(
                    "https://hwml-lang.org/errors/{}",
                    self.code
                )).unwrap(),
            }),
            source: Some("hwml".to_string()),
            message: self.message.clone(),
            related_information: Some(self.backtrace_to_related_info()),
            tags: self.get_tags(),
            data: None,
        }
    }

    /// Convert backtrace to LSP related information
    fn backtrace_to_related_info(&self) -> Vec<lsp_types::DiagnosticRelatedInformation> {
        use lsp_types::*;

        self.backtrace
            .iter()
            .filter_map(|frame| {
                let location = frame.location.as_ref()?;
                Some(DiagnosticRelatedInformation {
                    location: Location {
                        uri: location.source.to_lsp_uri()?,
                        range: location.to_lsp_range(),
                    },
                    message: frame.description.clone(),
                })
            })
            .collect()
    }

    /// Get diagnostic tags (deprecated, unnecessary, etc.)
    fn get_tags(&self) -> Option<Vec<lsp_types::DiagnosticTag>> {
        // Could mark certain patterns as deprecated or unnecessary
        None
    }
}
```

#### 7. JSON Export for Tooling

**Goal:** Export diagnostics as JSON for external tools (CI/CD, build systems).

```rust
use serde::{Serialize, Deserialize};

/// JSON-serializable diagnostic
#[derive(Serialize, Deserialize)]
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

#[derive(Serialize, Deserialize)]
pub struct FrameJson {
    pub description: String,
    pub file: Option<String>,
    pub line: Option<usize>,
    pub column: Option<usize>,
}

impl<'db> Diagnostic<'db> {
    pub fn to_json(&self) -> DiagnosticJson {
        DiagnosticJson {
            severity: format!("{:?}", self.severity),
            code: self.code.to_string(),
            message: self.message.clone(),
            file: self.location.as_ref()
                .and_then(|l| l.source.path().to_str())
                .map(|s| s.to_string()),
            line: self.location.as_ref()
                .map(|l| l.range.start.line),
            column: self.location.as_ref()
                .map(|l| l.range.start.column),
            backtrace: self.backtrace.iter()
                .map(|f| f.to_json())
                .collect(),
            suggestions: self.extra_remarks.iter()
                .map(|(msg, _)| msg.clone())
                .collect(),
        }
    }
}

/// Export all diagnostics as JSON array
pub fn export_json(diagnostics: &[Diagnostic]) -> String {
    let json_diags: Vec<_> = diagnostics.iter()
        .map(|d| d.to_json())
        .collect();
    serde_json::to_string_pretty(&json_diags).unwrap()
}
```

**Example JSON Output:**
```json
[
  {
    "severity": "Error",
    "code": "E001",
    "message": "type mismatch",
    "file": "src/main.hwml",
    "line": 42,
    "column": 10,
    "backtrace": [
      {
        "description": "checking expression against Nat",
        "file": "src/main.hwml",
        "line": 42,
        "column": 10
      },
      {
        "description": "checking function return type",
        "file": "src/main.hwml",
        "line": 40,
        "column": 23
      }
    ],
    "suggestions": [
      "consider using an if expression"
    ]
  }
]
```

#### 8. Summary Statistics

**Goal:** Provide high-level summary for large codebases.

```rust
/// Diagnostic statistics
#[derive(Debug, Default)]
pub struct DiagnosticStats {
    pub total: usize,
    pub errors: usize,
    pub warnings: usize,
    pub hints: usize,
    pub info: usize,
    pub bugs: usize,
    pub files_with_errors: HashSet<PathBuf>,
    pub by_code: HashMap<&'static str, usize>,
}

impl DiagnosticStats {
    pub fn from_diagnostics(diagnostics: &[Diagnostic]) -> Self {
        let mut stats = DiagnosticStats::default();
        stats.total = diagnostics.len();

        for diag in diagnostics {
            match diag.severity {
                Severity::Error => stats.errors += 1,
                Severity::Warning => stats.warnings += 1,
                Severity::Hint => stats.hints += 1,
                Severity::Info => stats.info += 1,
                Severity::Bug => stats.bugs += 1,
            }

            *stats.by_code.entry(diag.code).or_insert(0) += 1;

            if let Some(loc) = &diag.location {
                if let SourceInfo::File(path) = loc.source.info() {
                    stats.files_with_errors.insert(path.clone());
                }
            }
        }

        stats
    }

    pub fn render(&self) -> String {
        let mut output = String::new();

        output.push_str(&format!("Total diagnostics: {}\n", self.total));
        output.push_str(&format!("  Errors: {}\n", self.errors));
        output.push_str(&format!("  Warnings: {}\n", self.warnings));
        output.push_str(&format!("  Info: {}\n", self.info));
        output.push_str(&format!("  Hints: {}\n", self.hints));
        if self.bugs > 0 {
            output.push_str(&format!("  ⚠️  Internal bugs: {}\n", self.bugs));
        }
        output.push_str(&format!("\nFiles affected: {}\n",
            self.files_with_errors.len()));

        output.push_str("\nError breakdown by code:\n");
        let mut codes: Vec<_> = self.by_code.iter().collect();
        codes.sort_by_key(|(_, count)| std::cmp::Reverse(**count));
        for (code, count) in codes.iter().take(5) {
            output.push_str(&format!("  {}: {}\n", code, count));
        }

        output
    }
}
```

**Example Stats Output:**
```
Total diagnostics: 23
  Errors: 15
  Warnings: 7
  Info: 1
  Hints: 0

Files affected: 8

Error breakdown by code:
  E001: 8
  E002: 4
  E006: 2
  E003: 1
```

---

## Complete Diagnostic Pipeline Architecture

### Overview

```
┌─────────────────────────────────────────────────────────────────┐
│                    Elaboration Phase                             │
│  (Already Implemented: Lenient error collection)                │
└──────────────────────┬──────────────────────────────────────────┘
                       │
                       ▼
              Vec<ElabError<'db>>
                       │
                       ▼
┌─────────────────────────────────────────────────────────────────┐
│              Post-Processing Phase (NEW)                         │
├─────────────────────────────────────────────────────────────────┤
│  1. Convert to Diagnostic objects                               │
│  2. Deduplicate similar errors                                  │
│  3. Group related errors (cascading analysis)                   │
│  4. Sort by severity, file, line                                │
│  5. Add suggestions and fix-its                                 │
│  6. Gather source files                                         │
└──────────────────────┬──────────────────────────────────────────┘
                       │
                       ▼
                DiagnosticSet<'db>
                       │
                       ├──────────────┬────────────────┬──────────┐
                       ▼              ▼                ▼          ▼
              ┌─────────────┐  ┌──────────┐  ┌──────────┐  ┌──────────┐
              │   Terminal  │  │   LSP    │  │   JSON   │  │  HTML    │
              │   Renderer  │  │ Protocol │  │  Export  │  │  Report  │
              └─────────────┘  └──────────┘  └──────────┘  └──────────┘
```

### Complete API

```rust
/// Main diagnostic system entry point
pub struct DiagnosticSystem<'db> {
    db: &'db dyn salsa::Database,
    processor: DiagnosticPostProcessor<'db>,
    renderer: SourceRenderer<'db>,
    analyzer: ErrorAnalyzer<'db>,
}

impl<'db> DiagnosticSystem<'db> {
    pub fn new(db: &'db dyn salsa::Database) -> Self {
        DiagnosticSystem {
            db,
            processor: DiagnosticPostProcessor::new(db),
            renderer: SourceRenderer::new(db, RenderStyle::Ansi),
            analyzer: ErrorAnalyzer::new(db),
        }
    }

    /// Process errors from elaboration
    pub fn process_errors(
        &self,
        errors: Vec<ElabError<'db>>
    ) -> DiagnosticSet<'db> {
        self.processor.process(errors)
    }

    /// Render diagnostics for terminal
    pub fn render_terminal(&self, diagnostics: &DiagnosticSet<'db>) -> String {
        let mut output = String::new();

        // 1. Summary statistics
        let stats = DiagnosticStats::from_diagnostics(&diagnostics.diagnostics);
        output.push_str(&stats.render());
        output.push_str("\n\n");

        // 2. Grouped by file
        let by_file = DiagnosticsByFile::new(diagnostics.diagnostics.clone());
        output.push_str(&by_file.render_summary());
        output.push_str("\n\n");

        // 3. Detailed diagnostics
        for diagnostic in &diagnostics.diagnostics {
            output.push_str(&self.renderer.render(diagnostic).text);
            output.push_str("\n\n");
        }

        output
    }

    /// Export diagnostics for LSP
    pub fn to_lsp(&self, diagnostics: &DiagnosticSet<'db>)
        -> HashMap<Url, Vec<lsp_types::Diagnostic>>
    {
        let mut by_uri = HashMap::new();

        for diagnostic in &diagnostics.diagnostics {
            if let Some(uri) = diagnostic.location.as_ref()
                .and_then(|l| l.source.to_lsp_uri())
            {
                by_uri.entry(uri)
                    .or_insert_with(Vec::new)
                    .push(diagnostic.to_lsp());
            }
        }

        by_uri
    }

    /// Export diagnostics as JSON
    pub fn to_json(&self, diagnostics: &DiagnosticSet<'db>) -> String {
        export_json(&diagnostics.diagnostics)
    }
}

/// Container for processed diagnostics
pub struct DiagnosticSet<'db> {
    pub diagnostics: Vec<Diagnostic<'db>>,
    pub source_files: HashMap<PathBuf, String>,
}
```

### Revised Implementation Roadmap

#### Phase 1: Core Infrastructure (2-3 days)

**Goal:** Basic diagnostic types and error code system

- [ ] Create `Diagnostic<'db>` type with all fields
- [ ] Add `code()` method to all `ElabError` variants
- [ ] Add `severity()` method to all `ElabError` variants
- [ ] Create `DiagnosticContext` with trace stack (already done)
- [ ] Create `to_diagnostic()` conversion

#### Phase 2: Post-Processing (3-4 days)

**Goal:** Error analysis and optimization

- [ ] Implement `DiagnosticPostProcessor`
- [ ] Deduplication logic
- [ ] Error grouping (cascading analysis)
- [ ] Sorting by severity/file/line
- [ ] Pattern detection (`ErrorAnalyzer`)
- [ ] Suggestion generation

#### Phase 3: Source Rendering (2-3 days)

**Goal:** Beautiful source code display

- [ ] Implement `SourceRenderer`
- [ ] Multi-line highlighting
- [ ] Caret underlines (`^^^`)
- [ ] Context lines (2 before/after)
- [ ] ANSI color support
- [ ] Plain text fallback

#### Phase 4: Output Formats (2 days)

**Goal:** Support all output targets

- [ ] LSP conversion (`to_lsp()`)
- [ ] JSON export (`to_json()`)
- [ ] HTML report generation (bonus)
- [ ] Summary statistics (`DiagnosticStats`)
- [ ] File grouping (`DiagnosticsByFile`)

#### Phase 5: Integration & Testing (2-3 days)

**Goal:** Wire into compiler pipeline

- [ ] Update `elab_library_with_sccs` to use `DiagnosticSystem`
- [ ] CLI flag for output format (`--format=terminal|json|lsp`)
- [ ] Integration tests with multi-file errors
- [ ] LSP integration tests
- [ ] Performance benchmarking

**Total Effort:** 3-4 weeks for complete system

---

## Usage Examples

### Example 1: Terminal Output

```rust
// In CLI driver
let result = elab_library_with_sccs(db, &mut global, &programs, &stub_table);

if !result.errors.is_empty() {
    let diag_system = DiagnosticSystem::new(db);
    let diagnostics = diag_system.process_errors(result.errors);
    let rendered = diag_system.render_terminal(&diagnostics);

    eprintln!("{}", rendered);
    std::process::exit(1);
}
```

**Output:**
```
Total diagnostics: 5
  Errors: 3
  Warnings: 2

Files affected: 2

Error breakdown by code:
  E001: 2
  E002: 1

  src/main.hwml - 2 error(s), 1 warning(s)
  src/lib.hwml - 1 error(s), 1 warning(s)


error[E001]: type mismatch
  --> src/main.hwml:42:10

   40 | fn process(x: Nat) -> Nat {
   41 |     let y = x + 1;
   42 |     return true;
      |            ^^^^ expected Nat, found Bool
   43 | }

elaboration backtrace:
  0: checking expression against Nat at src/main.hwml:42:10
  1: checking function return type at src/main.hwml:40:23

help: consider using an if expression that returns Nat
```

### Example 2: LSP Integration

```rust
// In LSP server
fn publish_diagnostics(&mut self, uri: Url, version: Option<i32>) {
    let result = elab_library_with_sccs(
        &self.db,
        &mut self.global,
        &programs,
        &stub_table
    );

    let diag_system = DiagnosticSystem::new(&self.db);
    let diagnostics = diag_system.process_errors(result.errors);
    let by_uri = diag_system.to_lsp(&diagnostics);

    for (uri, lsp_diags) in by_uri {
        self.client.publish_diagnostics(uri, lsp_diags, version);
    }
}
```

### Example 3: JSON Export for CI

```rust
// In build system integration
let result = elab_library_with_sccs(db, &mut global, &programs, &stub_table);

let diag_system = DiagnosticSystem::new(db);
let diagnostics = diag_system.process_errors(result.errors);

// Write to file for CI tool consumption
let json = diag_system.to_json(&diagnostics);
std::fs::write("diagnostics.json", json)?;

// Exit with error code if any errors present
if diagnostics.diagnostics.iter().any(|d| d.severity == Severity::Error) {
    std::process::exit(1);
}
```

### Example 4: HTML Report

```rust
// For web-based error viewer
let html_renderer = SourceRenderer::new(db, RenderStyle::Html);
let mut html = String::from("<html><body>");

for diagnostic in &diagnostics.diagnostics {
    html.push_str(&html_renderer.render(diagnostic).text);
}

html.push_str("</body></html>");
std::fs::write("error-report.html", html)?;
```

---

## Testing Strategy

### Unit Tests

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_deduplication() {
        // Create duplicate errors
        let errors = vec![
            ElabError::TypeMismatch { /* same location */ },
            ElabError::TypeMismatch { /* same location */ },
        ];

        let processor = DiagnosticPostProcessor::new(db);
        let diagnostics = processor.process(errors);

        // Should deduplicate to 1
        assert_eq!(diagnostics.diagnostics.len(), 1);
    }

    #[test]
    fn test_sorting() {
        // Create errors in random order
        let errors = vec![
            error_at_line(42),
            error_at_line(10),
            error_at_line(25),
        ];

        let processor = DiagnosticPostProcessor::new(db);
        let mut diagnostics = processor.process(errors);

        sort_diagnostics(&mut diagnostics.diagnostics);

        // Should be sorted by line
        assert_eq!(diagnostics.diagnostics[0].location.line, 10);
        assert_eq!(diagnostics.diagnostics[1].location.line, 25);
        assert_eq!(diagnostics.diagnostics[2].location.line, 42);
    }

    #[test]
    fn test_typo_detection() {
        let analyzer = ErrorAnalyzer::new(db);
        let suggestions = analyzer.find_similar_names("proces");

        // Should suggest "process"
        assert!(suggestions.unwrap().contains(&"process".to_string()));
    }
}
```

### Integration Tests

```rust
#[test]
fn test_multi_file_error_grouping() {
    // Create programs with errors across files
    let program1 = parse("src/main.hwml", "...bad code...");
    let program2 = parse("src/lib.hwml", "...more bad code...");

    let result = elab_library_with_sccs(
        db,
        &mut global,
        &[(path1, &program1), (path2, &program2)],
        &stub_table
    );

    let diag_system = DiagnosticSystem::new(db);
    let diagnostics = diag_system.process_errors(result.errors);

    let by_file = DiagnosticsByFile::new(diagnostics.diagnostics);

    assert_eq!(by_file.files.len(), 2);
    assert!(by_file.files.contains_key(&PathBuf::from("src/main.hwml")));
    assert!(by_file.files.contains_key(&PathBuf::from("src/lib.hwml")));
}
```

