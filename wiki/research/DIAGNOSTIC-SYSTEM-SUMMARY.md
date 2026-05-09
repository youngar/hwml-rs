# Diagnostic System Research Summary

**Date:** 2026-05-08  
**Status:** Design Complete - Ready for Implementation  
**Context:** Comprehensive diagnostic framework for HWML compiler

---

## Executive Summary

This document summarizes the research on diagnostic systems for HWML, centered around the **Asai (浅い)** library from RedPRL. The research identifies concrete improvements HWML can adopt while leveraging our unique constraint/meta provenance system.

---

## Research Documents

### 1. Diagnostic Framework Design
**File:** `diagnostic-framework-design.md`  
**Focus:** Asai-inspired design for HWML

**Key Topics:**
- Five independent diagnostic parameters
- Effect-based (OCaml) vs RAII-based (Rust) context management
- Byte-level location tracking rationale
- Unicode display stability (Level 2)
- Error code system design
- Integration with HWML's constraint provenance

**Main Contribution:** Complete 4-phase implementation plan with code examples

### 2. Asai Detailed Review
**File:** `asai-detailed-review.md`  
**Focus:** Deep dive into Asai codebase

**Key Topics:**
- Effect-based dynamic scoping with `Algaeff.Reader`
- Message type system with short codes
- Backtrace representation (backward list of loctexts)
- STLC example usage patterns
- RAII adaptation strategy for Rust
- Performance considerations

**Main Contribution:** Concrete Rust equivalents for OCaml patterns

### 3. Asai vs HWML Comparison
**File:** `asai-vs-hwml-comparison.md`  
**Focus:** Gap analysis and recommendations

**Key Topics:**
- Side-by-side feature comparison
- Critical gaps (elaboration backtrace, location threading)
- Minor gaps (error codes, unified display)
- Detailed implementation for each priority
- Migration strategy (3 weeks)

**Main Contribution:** Actionable roadmap with effort estimates

---

## Critical Findings

### What Asai Has (and HWML Needs)

1. **Elaboration Backtrace** ⭐⭐⭐⭐⭐
   - Call stack of elaboration operations
   - Shows "how we got here" in complex errors
   - **Effort:** 5-7 days
   - **Impact:** Critical for UX

2. **Location Inheritance** ⭐⭐⭐
   - Automatic context threading
   - Reduces boilerplate
   - **Effort:** 1-2 days
   - **Impact:** Developer ergonomics

3. **Error Codes** ⭐⭐
   - Short, Google-able codes (`E001`)
   - Better documentation
   - **Effort:** 1 day
   - **Impact:** User support

4. **Unicode Display Stability** ⭐⭐⭐⭐
   - Level 2: Works across platforms
   - No column numbers (byte-based only)
   - **Effort:** 2-3 days
   - **Impact:** International users

### What HWML Has (and Asai Lacks)

1. **Constraint Provenance** ⭐⭐⭐⭐⭐
   - `ConstraintOrigin` side-table
   - Tracks why constraints were created
   - **Status:** ✅ Already implemented
   - **Unique to HWML**

2. **Meta Provenance** ⭐⭐⭐⭐⭐
   - `MetaProvenance` side-table
   - Tracks metavariable creation
   - **Status:** ✅ Already implemented
   - **Unique to HWML**

3. **Byte-Level Location Tracking** ⭐⭐⭐⭐
   - Unambiguous positions
   - Fast, platform-independent
   - **Status:** ✅ Already implemented (ADR-014)

---

## Proposed Architecture

### Unified Diagnostic Type

```rust
pub struct Diagnostic<'db> {
    // From Asai
    severity: Severity,           // Error, Warning, Info, Hint, Bug
    code: &'static str,           // "E001"
    message: String,              // Primary message
    location: Option<SourceRange<'db>>,
    backtrace: Vec<DiagnosticFrame<'db>>,  // Elaboration stack
    extra_remarks: Vec<(String, Option<SourceRange<'db>>)>,
    
    // HWML-specific
    constraint_origin: Option<ConstraintOrigin<'db>>,
    blocking_constraints: Vec<ConstraintId>,
    meta_provenance: Option<MetaProvenance<'db>>,
}
```

### Example Output

```
error[E001]: type mismatch at src/main.hwml:42:10
  expected: Nat
  got:      Bool

elaboration backtrace:
  0: checking expression against Nat at src/main.hwml:42:10
  1: checking function return type at src/main.hwml:40:5
  2: checking definition 'process' at src/main.hwml:38:1
  3: elaborating module '/main' at src/main.hwml:1:1

constraint context:
  origin: type annotation at src/main.hwml:42:10
  created by: C10
  blocking: C10, C15, C20

notes:
  = note: Nat is defined at src/prelude.hwml:10:1
  = note: consider using `if` expression to return Nat
```

---

## Implementation Roadmap

### Week 1: Infrastructure
- Create `DiagnosticContext` with trace stack
- Implement `TraceGuard` RAII pattern
- Add `elab_backtrace` to all error variants
- Add error code methods

### Week 2: Instrumentation
- Wrap `check()`, `synth()` with traces
- Add error helper methods to `Elaborator`
- Update all error construction sites
- Test backtrace capture

### Week 3: Polish & Integration
- Enhanced `Display` implementation
- LSP diagnostic conversion
- Integration tests
- Error code documentation

**Total Effort:** 2-3 weeks

---

## Next Actions

1. ✅ Research complete
2. 🔄 Create ADR for diagnostic framework
3. ⏳ Implement Phase 1 (infrastructure)
4. ⏳ Create `docs/error-codes.md`
5. ⏳ LSP integration tests

---

---

## Advanced Features (Added 2026-05-08)

### Holistic Error Analysis

✅ **Already Implemented:** Lenient error collection (continues on errors)
✅ **New:** Post-processing pipeline for error optimization

**Features:**
1. **Deduplication** - Remove duplicate errors
2. **Cascading Analysis** - Find root causes vs. cascading errors
3. **Error Grouping** - Group related errors from constraint graph
4. **Intelligent Sorting** - By severity, file, line, column
5. **Pattern Detection** - Recognize common mistakes (typos, missing returns, etc.)
6. **Suggestion Generation** - Automated fix suggestions

### Source Code Rendering

**Terminal Output:**
```
error[E001]: type mismatch
  --> src/main.hwml:42:10

   40 | fn process(x: Nat) -> Nat {
   41 |     let y = x + 1;
   42 |     return true;
      |            ^^^^ expected Nat, found Bool
   43 | }

elaboration backtrace:
  0: checking expression against Nat
  1: checking function return type

help: consider using an if expression
```

**Features:**
- Multi-line source snippets
- Context lines (2 before/after)
- Caret underlines (`^^^`)
- ANSI colors for terminal
- Plain text fallback
- HTML output for reports

### Multiple Output Formats

1. **Terminal** - Human-readable with colors
2. **LSP** - Rich IDE integration with related information
3. **JSON** - Machine-readable for CI/CD tools
4. **HTML** - Web-based error reports

### Diagnostic Statistics

```
Total diagnostics: 23
  Errors: 15
  Warnings: 7
  Info: 1

Files affected: 8

Error breakdown by code:
  E001: 8
  E002: 4
  E006: 2
```

### File Grouping

```
Found 5 error(s) and 3 warning(s) across 3 file(s)

  src/main.hwml - 2 error(s), 1 warning(s)
  src/lib.hwml - 2 error(s), 2 warning(s)
  src/utils.hwml - 1 error(s), 0 warning(s)
```

---

## Complete Pipeline Architecture

```
Elaboration → Vec<ElabError> → Post-Processing → DiagnosticSet
                                                       │
                    ┌──────────────┬──────────────────┼──────────────┐
                    ▼              ▼                  ▼              ▼
               Terminal          LSP              JSON            HTML
```

**Post-Processing Steps:**
1. Convert to Diagnostic objects
2. Deduplicate similar errors
3. Group related errors (cascading)
4. Sort by severity/file/line
5. Add suggestions and fix-its
6. Gather source files

---

## Revised Implementation Roadmap

### Week 1: Core + Post-Processing (5-7 days)
- Create `Diagnostic<'db>` type
- Add error codes to `ElabError`
- Implement `DiagnosticPostProcessor`
- Deduplication and sorting
- Pattern detection

### Week 2: Rendering + Formats (4-5 days)
- Implement `SourceRenderer`
- Multi-line highlighting
- ANSI colors
- LSP conversion
- JSON export

### Week 3: Integration + Testing (3-4 days)
- Wire into compiler pipeline
- CLI output formatting
- LSP integration
- Statistics and grouping
- Comprehensive tests

**Total Effort:** 3-4 weeks

---

## References

- **Asai library:** `external/asai/`
- **Asai docs:** https://redprl.org/asai/asai/
- **Research files:**
  - `diagnostic-framework-design.md` - Complete design with post-processing
  - `asai-detailed-review.md` - Asai codebase analysis
  - `asai-vs-hwml-comparison.md` - Gap analysis
- **Related ADRs:** ADR-014, ADR-015
- **Current code:** `crates/hwml-elab/src/error.rs`, `crates/hwml-elab/src/program.rs`

