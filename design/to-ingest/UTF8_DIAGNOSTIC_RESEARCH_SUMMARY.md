# UTF-8 Character Handling and Diagnostics Research - Executive Summary

**Date:** 2026-05-06  
**Research Duration:** Deep dive completed  
**Status:** Ready for implementation planning

---

## What Was Researched

I've completed a comprehensive deep-dive research project on **UTF-8 character representation in compiler internals and diagnostic rendering**, focusing on the challenges you outlined:

1. ✅ **Byte-level lexing** - Safe handling of arbitrary UTF-8, invalid sequences
2. ✅ **Grapheme vs terminal width** - The emoji alignment problem
3. ✅ **LSP UTF-16 trap** - Position encoding negotiation and conversion
4. ✅ **`asai`-style diagnostics** - Structured generation vs presentation
5. ✅ **InfoTree architecture** - Interactive elaboration state for LSP

---

## Key Deliverable

**Main Document:** `wiki/research/utf8-diagnostics-rendering.md` (1,709 lines)

This is a comprehensive research report covering:
- The complete UTF-8 spectrum (bytes → code points → graphemes → terminal cells)
- Byte-level lexing strategies with the `bstr` crate
- Three position systems and conversion between them
- Diagnostic rendering for CLI (miette), LSP (structured ranges), and terminals
- LSP InfoTree architecture (from Lean 4) for dependent type interactivity
- Production implementations (rust-analyzer, GHC, Lean 4)
- Complete implementation roadmap (5 phases, 6 weeks)
- Current HWML status assessment and gaps

---

## Critical Findings

### 1. The Three Position Systems

**You must maintain three distinct representations:**

| System | Use | Example | Notes |
|--------|-----|---------|-------|
| **Byte offsets** | Internal (source of truth) | `offset: 45` | Fast, deterministic |
| **LSP positions** | Editor communication | `{line: 3, character: 12}` | UTF-16 or UTF-8 |
| **Grapheme columns** | Terminal display | Column 8 on screen | Best-effort, fragile |

**Current HWML status:**
- ✅ Already uses byte offsets internally (correct!)
- ❌ No UTF-16 conversion for LSP (will break with emoji)
- ❌ No grapheme handling for terminal rendering

### 2. The LSP UTF-16 Trap

**The Problem:**
```
Text:        "Hello 👩🏽‍💻 World"
Byte offset: 6     17
UTF-16 units: 6     11  ← Different!
```

If your server sends byte offset 17, but VS Code expects UTF-16 offset 11, diagnostics misalign.

**The Solution:**
1. Negotiate UTF-8 encoding in LSP initialization (LSP 3.17+)
2. Fallback: Maintain UTF-16 conversion (see rust-analyzer's `LineIndex`)

### 3. Terminal Rendering is Fundamentally Fragile

**Key insight:** Emoji width calculation is **not standardized**. Different terminals report different widths.

```rust
let emoji = "👩🏽‍💻";
// iTerm2: 2 cells
// Alacritty: 1 cell  
// tmux: depends on $TERM
```

**Recommendation:** Accept best-effort alignment with `miette`, focus on LSP correctness.

### 4. LSP Sidesteps the Problem

**Beautiful insight:** LSP doesn't send ASCII-art! It sends **structured ranges**.

```rust
// Server sends:
Diagnostic {
    range: Range {
        start: Position { line: 3, character: 10 },
        end: Position { line: 3, character: 15 },
    },
    message: "type mismatch",
    // ...
}

// Editor draws squiggly lines with its own layout engine
// ✅ Perfect alignment guaranteed!
```

### 5. Structured Diagnostics (asai Philosophy)

**Separate generation from presentation:**

```rust
// Generate once (byte-based, format-agnostic)
let diag = Diagnostic {
    labels: vec![
        Label { range: ByteRange::new(45, 50), ... }
    ],
    // ...
};

// Render many ways
CliRenderer::render(&diag);   // miette with colors
LspRenderer::render(&diag);   // LSP ranges
JsonRenderer::render(&diag);  // For CI/tooling
```

---

## Current HWML Status

### What You Have ✅

From analyzing `crates/hwml-surface/src/lex.rs`:

- ✅ **Byte-level lexing** - `#[logos(source = [u8])]` (perfect!)
- ✅ **Unicode line breaks** - Handles LF, CR, CRLF, NEL, LS, PS
- ✅ **Lossless grammar** - All bytes tokenized (enables streaming positions)
- ✅ **Byte-based tracking** - Columns use `slice.len()`

### What You're Missing ❌

**Position Encoding:**
- ❌ No UTF-16 conversion (LSP will break with non-ASCII)
- ❌ No position encoding negotiation in LSP
- ❌ No grapheme cluster support (CLI alignment issues)

**Diagnostics:**
- ❌ No structured diagnostic types
- ❌ No multi-span support
- ❌ No `miette` integration (CLI errors are plain text)
- ❌ Lexer panics on errors instead of returning error tokens

**LSP Advanced:**
- ❌ No InfoTree for elaboration state queries
- ❌ No custom RPC endpoints (`$/hwml/metavarInfo`, `$/hwml/goalState`)

---

## Implementation Roadmap

I've provided a detailed 5-phase, 6-week roadmap in the research document.

### Phase 1: Foundation (Week 1) - **START HERE**

**Goal:** Fix lexer safety and add UTF-8 validation

**Tasks:**
```rust
// 1. Fix panic on lexical error
// Current (UNSAFE):
Err(_err) => panic!("Lexical error at {}:{}", self.line, self.column);

// Recommended:
Err(err) => return Some((span.start, Token::Error, span.end));

// 2. Add UTF-8 validation helper
pub fn validate_identifier(bytes: &[u8]) -> Result<&str, InvalidUtf8Error> {
    std::str::from_utf8(bytes).map_err(|e| InvalidUtf8Error {
        bytes: bytes.to_vec(),
        error: e,
    })
}

// 3. Add comprehensive Unicode tests
#[test]
fn test_emoji_identifier() {
    let source = "def 🚀_speed = 299792";
    // ... assert byte offsets are correct
}
```

**Deliverables:**
- Lexer handles invalid UTF-8 gracefully
- Test suite covers emoji, combining characters, RTL text
- All positions remain byte-based

### Phase 2: Position Encoding (Week 2)

**Goal:** Build LSP conversion infrastructure

**Create `LineIndex` struct:**
```rust
pub struct LineIndex {
    line_starts: Vec<usize>,  // Byte offsets
    utf16_cache: RefCell<HashMap<usize, Utf16Data>>,  // Lazy
}

impl LineIndex {
    pub fn byte_to_position_utf8(&self, offset: usize) -> Position;
    pub fn byte_to_position_utf16(&self, offset: usize) -> Position;
}
```

**Add LSP negotiation:**
```rust
fn initialize(&self, params: InitializeParams) -> InitializeResult {
    InitializeResult {
        capabilities: ServerCapabilities {
            position_encoding: Some(PositionEncodingKind::UTF8),
            // ...
        },
    }
}
```

### Phase 3: Structured Diagnostics (Week 3)

**Goal:** Decouple generation from presentation

```rust
// Define format-agnostic diagnostics
pub struct Diagnostic {
    pub severity: Severity,
    pub labels: Vec<Label>,  // Byte ranges!
    pub notes: Vec<String>,
    pub help: Option<String>,
}

// Implement renderers
let cli_output = CliRenderer::new().render(&diag);  // Uses miette
let lsp_diag = LspRenderer::new(encoding).render(&diag, &line_index);
```

**Add to Cargo.toml:**
```toml
[dependencies]
miette = { version = "7.2", features = ["fancy"] }
bstr = "1.9"
unicode-segmentation = "1.11"
```

### Phase 4-5: InfoTree & Advanced Features (Weeks 4-6)

See full roadmap in `wiki/research/utf8-diagnostics-rendering.md` section 8.

---

## Recommended Next Steps

### Immediate (Today)

1. **Read the full research:** `wiki/research/utf8-diagnostics-rendering.md`
2. **Review current lexer:** `crates/hwml-surface/src/lex.rs` (you already have a great foundation!)
3. **Decide on priorities:** Do you need LSP support now? CLI improvements? Both?

### This Week

1. **Fix lexer error handling** - Stop panicking, return error tokens
2. **Add Unicode test suite** - Emoji, combining chars, RTL text
3. **Plan diagnostics architecture** - Structured types, renderers

### Next 2 Weeks

1. **Implement `LineIndex`** - UTF-16 conversion for LSP
2. **Integrate `miette`** - Beautiful CLI diagnostics
3. **Update elaborator** - Generate structured diagnostics

---

## Key Resources

### In This Repository

**Main Research:**
- `wiki/research/utf8-diagnostics-rendering.md` (1,709 lines) - **START HERE**
- `wiki/research/elaboration-error-messages.md` - Error reporting philosophy (complements this)
- `wiki/research/provenance-deep-dive.md` - Metavariable origin tracking

**Current Code:**
- `crates/hwml-surface/src/lex.rs` - Your lexer (already well-designed!)
- `crates/hwml-support/src/line_info.rs` - Line break tracking
- `crates/hwml-vfs/src/lsp.rs` - LSP VFS

### External Examples

**rust-analyzer:**
- `crates/ide-db/src/line_index.rs` - UTF-16 conversion reference implementation
- Source: https://github.com/rust-lang/rust-analyzer

**Lean 4:**
- `src/Lean/Data/Lsp/Utf16.lean` - Position encoding
- `src/Lean/Elab/InfoTree/` - InfoTree architecture
- Source: https://github.com/leanprover/lean4

### Crates to Use

```toml
# Essential
bstr = "1.9"              # Byte string utilities
miette = "7.2"            # Diagnostic rendering
lsp-types = "0.95"        # LSP types

# For grapheme support (optional)
unicode-segmentation = "1.11"
unicode-width = "0.1"

# Already using
logos = "0.13"            # Your lexer
```

---

## Questions Answered

✅ **"How do I safely lex UTF-8 with emojis?"**
→ Use `&[u8]` lexing (you already do!), validate selectively with `std::str::from_utf8()`

✅ **"How do I align diagnostics in terminals with emoji?"**
→ Best-effort with `miette`, but accept it's fragile. Focus on LSP correctness.

✅ **"What's the LSP UTF-16 trap?"**
→ LSP (pre-3.17) uses UTF-16 code units, not bytes. Negotiate UTF-8 or convert.

✅ **"How do I separate diagnostic generation from presentation?"**
→ Internal diagnostics use byte ranges. Renderers convert to target format (CLI, LSP, JSON).

✅ **"How do I support interactive elaboration queries (like Lean)?"**
→ Build InfoTree during elaboration, expose via custom RPC (`$/hwml/metavarInfo`)

---

## Success Criteria

**For CLI:**
- ✅ Beautiful multi-span error messages with colors
- ✅ Correct alignment for ASCII and most Unicode
- ⚠️ Acceptable misalignment for complex emoji (±1-2 columns)

**For LSP:**
- ✅ Zero alignment issues (editor handles rendering)
- ✅ Support both UTF-8 and UTF-16 encoding
- ✅ Fast position conversions (<10ms)

**For Compiler:**
- ✅ No panics on invalid UTF-8
- ✅ Deterministic byte-based positions
- ✅ Comprehensive Unicode test coverage

---

## Final Thoughts

**You have a strong foundation!** Your lexer already uses byte-level processing (`&[u8]`), which is exactly right. The main gaps are:

1. **LSP position encoding** - Add UTF-16 conversion (needed for non-ASCII correctness)
2. **Structured diagnostics** - Separate generation from rendering
3. **Error handling** - Stop panicking on invalid UTF-8

The research document provides detailed implementations, examples from production systems, and a concrete roadmap.

**Start with Phase 1** (fix lexer safety), then tackle UTF-16 conversion for LSP. The `miette` integration for CLI can come in parallel.

Good luck! The research is thorough and ready to guide implementation. 🚀

