# Diagnostic Framework Implementation Plan (Revised from Asai)

**Date:** 2026-05-08
**Status:** ✅ **ACTIVE** - Primary implementation plan
**Revision:** v2 (revised after studying Asai source code `external/asai/`)
**Supersedes:** `DIAGNOSTIC-VFS-LSP-INTEGRATION.md` (original 6-week plan)
**See Also:**
- `UNICODE-RENDERING-ASAI-APPROACH.md` - Unicode rendering principles
- `BIG-PICTURE-PIPELINE.md` - Overall architecture
- `research/diagnostic-framework-design.md` - Theoretical foundation
- `ADR-014-byte-level-location-tracking.md` - Why byte offsets

**Implementation Status:**
- Week 1: ✅ Foundation (basic types complete, needs revision)
- Week 2-6: 📋 Planned

---

## Executive Summary

This plan revises our diagnostic framework implementation after studying the **actual Asai source code** in `external/asai/`.

**Critical Discovery:** The Asai documentation describes principles, but the SOURCE CODE reveals crucial implementation details:
- Terminal rendering uses **ANSI underline escapes**, not column alignment
- Positions cache **line information** to avoid recomputation
- **5 severity levels** (including `Bug` for internal errors)
- Backtrace and extra remarks are **separated**
- LSP implementation is **deliberately simple** (UTF-8 only)

**Key Change:** We were planning to use `unicode-width` for caret alignment - this is **fundamentally wrong**. Asai never calculates visual width. Instead, it uses ANSI underline (`\x1b[4m`) to highlight ranges directly in the source text.

---

## Key Insights from Asai Source Code

### Architecture Insights

**1. Severity Levels (5, not 4!)**
- `Hint` - Code smell, not rendered as squiggles in LSP
- `Info` - Informational
- `Warning` - Suspicious but non-fatal
- `Error` - User error
- `Bug` - Internal compiler bug (important for users to report!)

**2. Text vs Loctext**
- `Text.t = Format.formatter -> unit` - Pretty-printable text (NO raw strings!)
- `Loctext.t = Text.t Range.located` - Text + optional source range
- This preserves formatting structure for layout engines

**3. Range with Position Information**
```ocaml
type position = {
  source : source;        (* File or string *)
  offset : int;           (* Byte offset *)
  start_of_line : int;    (* Byte offset of line start *)
  line_num : int;         (* 1-indexed line number *)
}

type t (* range *) = position * position
```

**Key difference:** Asai stores BOTH byte offsets AND line numbers in positions!
- Our current `Span` only has byte offsets
- We need to cache line:column info to avoid recomputation

**4. Diagnostic Structure**
```ocaml
type 'message t = {
  severity : severity;
  message : 'message;       (* Structured message type *)
  explanation : Loctext.t;  (* Free-form text with ranges *)
  backtrace : Loctext.t bwd;        (* Backward list *)
  extra_remarks : Loctext.t bwd;    (* Additional notes *)
}
```

**Key insights:**
- Uses **backward lists** (snoc lists) for efficient appending
- Separates **backtrace** (execution context) from **extra_remarks** (related notes)
- Both structured messages AND free-form text

**5. Terminal Rendering Features**
- ANSI underline (`[4m`) for highlighting ranges in source
- Box-drawing characters (`╭` `┆` `╯`) for structure
- `^` marker at FIXED left margin (never aligned!)
- Custom marker functions for different visualization styles
- Block splitting threshold (avoid showing too many non-highlighted lines)
- Tab expansion (always to fixed width, default 8 spaces)

**6. LSP Integration**
- Separate package `asai-lsp`
- Simple server implementation with callbacks
- Note in docs: "does not handle positionEncoding" (they always use UTF-8 byte offsets!)

---

## What We Got Wrong

### ❌ **Our Current Issues**

1. **Missing severity level:** We don't have `Bug` severity
2. **Too simple span:** We only store byte offsets, not line info
3. **No structured text:** We use plain strings, not formatter-friendly text
4. **No backtrace separation:** We mix backtrace and related diagnostics
5. **Wrong rendering plan:** We were going to use `unicode-width` and column alignment
6. **Missing features:**
   - Extra remarks (notes beyond backtrace)
   - Block splitting (avoid showing huge files)
   - Custom markers
   - Tab expansion strategy

---

## ✅ **Revised Type Design**

### Core Types (Rust equivalent of Asai)

```rust
// Severity with Bug level
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum DiagnosticSeverity {
    Bug,      // Compiler bug - highest priority!
    Error,    // User error
    Warning,  // Suspicious
    Info,     // Informational
    Hint,     // Code smell
}

// Position with cached line info (like Asai)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Position {
    pub offset: usize,           // Byte offset
    pub start_of_line: usize,    // Byte offset of line start
    pub line_num: usize,          // 1-indexed line number
}

// Span is now two positions (not just offsets!)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    pub start: Position,
    pub end: Position,
}

// Text with formatting (simplified - Rust doesn't have Format.formatter)
// We use a trait object or enum for now
pub enum Text {
    Plain(String),
    Formatted(Box<dyn Fn(&mut String)>),  // Or use a simpler approach
}

// Located text (like Asai's Loctext)
#[derive(Debug, Clone)]
pub struct Loctext {
    pub loc: Option<Span>,
    pub text: String,  // Simplified from Text for now
}

// Diagnostic structure
#[derive(Debug, Clone)]
pub struct Diagnostic {
    pub severity: DiagnosticSeverity,
    pub message: DiagnosticCode,  // Structured message
    pub explanation: Loctext,      // Main explanation
    pub backtrace: Vec<Loctext>,   // Execution context
    pub extra_remarks: Vec<Loctext>,  // Related notes
}
```

---

## 📝 **Updated Implementation Plan**

### Week 1: Foundation (REVISED)

**Current Status:** ✅ Partially complete - need to revise types

**Tasks:**
1. ✅ Create `hwml-diagnostic` crate structure
2. 🔄 Revise core types based on Asai:
   - Add `Bug` severity level
   - Change `Span` to store `Position` with line info
   - Add `Loctext` type for located text
   - Separate `backtrace` from `extra_remarks`
3. 🔄 Update builder API for new structure
4. ✅ Write unit tests

**Key changes from current implementation:**
- `Span::new(start, end)` → `Span { start: Position, end: Position }`
- Add `Position::from_byte_offset(source, offset)` helper
- Add `DiagnosticSeverity::Bug`
- Split suggestions into backtrace vs. remarks

---

### Week 2: Salsa Integration (NO CHANGES)

**Goal:** Integrate diagnostics with Salsa database

**Tasks remain the same:**
1. Create `hwml-db/src/diagnostics.rs`
2. Implement `file_diagnostics` query
3. Implement `workspace_diagnostics` query
4. Update parsing to return diagnostics
5. Update elaboration to collect diagnostics
6. Test incrementality

---

### Week 3: LSP Integration (REVISED)

**Key insight from Asai:** They use a **callback-based LSP server** with simple interface!

```rust
// Asai's approach (simplified):
pub fn start_lsp_server<M: Message>(
    init: impl FnOnce(Option<&Path>),         // Workspace init
    load_file: impl Fn(&Path, &dyn DisplayDiag<M>),  // Load & emit
) {
    // Simple LSP server loop
}
```

**Our approach:**
1. Keep existing LSP infrastructure (we have more features than Asai)
2. Add simple diagnostic conversion: `Diagnostic → lsp_types::Diagnostic`
3. Use ANSI underline technique from Asai for ranges
4. **NO positionEncoding handling** (Asai doesn't either - they always use UTF-8 bytes!)

**Updated tasks:**
1. Create `hwml-diagnostic/src/lsp.rs`
2. Implement conversion WITHOUT handling positionEncoding (it's a mess)
3. Convert byte offsets to line:column using cached `Position` data
4. Publish diagnostics with range highlights
5. Test with VSCode (our primary target)

---

### Week 4: Post-Processing (REVISED with Asai insights)

**New insights:**
- Asai doesn't do pattern detection or auto-fixes in the library
- That's application-specific!
- Focus on **deduplication** and **block splitting**

**Revised tasks:**
1. Implement deduplication (same as before)
2. **NEW:** Implement block splitting threshold
   - Don't show huge files with one error
   - Show only ±N lines around highlighted regions
   - Asai uses default threshold of 5 non-highlighted lines
3. Remove pattern detection (move to Week 6 as application-level feature)
4. Test effectiveness

---

### Week 5: Terminal Rendering (MAJOR REVISION)

**Goal:** Implement Asai-style terminal output with ANSI underlines

**✅ FOUNDATION INTEGRATED (2026-05-08):**
- `ansi.rs` module with ANSI codes, colors, symbols, box-drawing
- `marked_source.rs` types for structured rendering
- `AnsiMode` with auto-detection (TTY, TERM, NO_COLOR)
- All constants from Asai analysis

**Key techniques from Asai test output:**

```
 ￫ error[E0308]
 ￭ /path/to/file.cool
 1 | aaaaaaaaaa
 2 | bbbbbbbbbb
 3 | cccccccccc
   ^ this is an error
```

**With ANSI escape codes:**
```
 1 | aaa[4maaaaaaa[m        ← [4m = underline start, [m = reset
 2 | [4mbbbbbbbbbb[m
 3 | [4mcccc[mcccccc
   ^                     ← Fixed position, never aligned!
```

**Implementation tasks:**
1. Box-drawing characters (`￫` `￭` `╭` `┆` `╯`)
2. ANSI underline (`\x1b[4m`) for highlighted ranges
3. ANSI colors for severity (red=error, yellow=warning, etc.)
4. `^` marker at FIXED left margin
5. Tab expansion (8 spaces default, configurable)
6. Block splitting (show only relevant lines)
7. Test with emoji, CJK, combining characters

**NO column alignment, NO `unicode-width`, NO `wcwidth`!**

---

### Week 6: Advanced Features (REVISED)

**Based on Asai, focus on:**

1. **Backtrace rendering** (Asai style with `╭` `╯` frames)
2. **Extra remarks** (separate from backtrace)
3. **Custom markers** (for different visualization styles)
4. **GitHub Actions integration** (Asai has this!)
5. Application-level pattern detection (not library-level)
6. `--explain` command for error codes

**GitHub Actions Workflow Commands:**
Asai supports this format:
```
::warning file=main.hwml,line=42::type mismatch
```

We should too!

---

## Summary of Major Changes

| Aspect | Original Plan | Revised (from Asai) |
|--------|---------------|---------------------|
| Severity levels | 4 (Error/Warning/Info/Hint) | 5 (add Bug) |
| Span | Byte offsets only | Position with line cache |
| Diagnostic parts | One big message | Explanation + backtrace + remarks |
| Terminal rendering | Column alignment | ANSI underline + fixed margin |
| Unicode handling | `unicode-width` crate | NO width calculation |
| LSP | Complex encoding | Simple, UTF-8 only |
| Pattern detection | Week 4 | Week 6 (application-level) |
| Block splitting | Not planned | Week 4 (from Asai) |
| GitHub Actions | Not planned | Week 6 (from Asai) |

---

## Next Steps

1. ✅ Study Asai source code (DONE)
2. 🔄 Revise Week 1 types to match Asai architecture
3. 🔄 Update DIAGNOSTIC-VFS-LSP-INTEGRATION.md with findings
4. ▶️ Continue implementation with correct approach
