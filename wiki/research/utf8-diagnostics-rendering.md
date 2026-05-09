# UTF-8 Character Handling and Diagnostic Rendering in Compiler Internals

**Date:** 2026-05-06  
**Type:** Research  
**Status:** Deep Dive  
**Confidence:** 0.9

---

## Executive Summary

This research explores the complete spectrum of challenges in handling UTF-8 text, including complex grapheme clusters and emojis, in a compiler's lexer, internal representation, and diagnostic output. The goal is to design a robust architecture that handles arbitrary UTF-8 safely while producing correctly-aligned diagnostics across terminals, LSP clients, and text editors.

### Key Findings

1. **Byte-level lexing with validation** - Use `&[u8]` + selective UTF-8 validation (via `bstr`)
2. **Grapheme clusters ≠ chars ≠ terminal cells** - Three distinct concepts requiring different crates
3. **LSP's UTF-16 trap** - Must negotiate UTF-8 encoding or maintain translation maps
4. **Terminal rendering is fragile** - Emoji width calculation is fundamentally unreliable
5. **Escape hatch: LSP sidesteps rendering** - Editors handle visualization, server sends ranges
6. **`asai`-style structured diagnostics** - Separate generation from presentation

### The Three-Layer Strategy

1. **Internal (lexer/parser):** Byte offsets + validated UTF-8 slices
2. **Diagnostic generation:** Structured errors with byte ranges + origin tracking
3. **Presentation layer:** Format-specific rendering (CLI with `miette`, LSP with ranges)

---

## 1. The UTF-8 Spectrum: What We're Dealing With

### 1.1 Characters Are Not What You Think

**The hierarchy:**

```
Byte sequence:       F0 9F 91 A9 F0 9F 8F BD E2 80 8D F0 9F 92 BB
UTF-8 decoding:      4 code points (U+1F469, U+1F3FD, U+200D, U+1F4BB)
Rust chars:          Not representable (Rust char = single code point)
Grapheme cluster:    1 visible "character" 👩🏽‍💻 (woman technologist with skin tone)
Terminal cells:      1 or 2 cells (depends on terminal emulator!)
```

**The problem:** A single visual "character" may span:
- 1-14 bytes (for complex emoji sequences)
- 1-7 UTF-8 code points
- Multiple Rust `char` values
- 1-2 terminal columns (inconsistent!)

### 1.2 Why This Matters for Compilers

**Identifiers:**
```hwml
def café = 42           // é is 1 grapheme, 2 bytes (0xC3 0xA9)
def 你好 = "hello"      // Each character is 3 bytes
def 🚀_speed = 299792   // Emoji identifier (4 bytes + underscore)
```

**Diagnostic alignment:**
```
error: type mismatch
  --> example.hwml:3:10
   |
3  | let 🚀 = "hello"
   |     ^^ expected Nat, got String
```

If the diagnostic engine counts bytes but the terminal counts columns, the `^^` underline will misalign.

---

## 2. Byte-Level Lexing: The Foundation

### 2.1 Why `&[u8]` Instead of `&str`

**Rust's guarantee:** `&str` is always valid UTF-8. If the lexer encounters invalid UTF-8, it will panic.

**The problem:** User might save a file with:
- Invalid UTF-8 from copy-paste
- Mixed encodings (Latin-1 + UTF-8)
- Binary data in string literals

**The solution:** Lex on `&[u8]`, validate selectively.

### 2.2 The `bstr` Crate

**Purpose:** String-like operations on byte slices without UTF-8 enforcement.

```rust
use bstr::ByteSlice;

fn lex_identifier(input: &[u8]) -> Result<&str, LexError> {
    // Find identifier bytes (using byte patterns)
    let slice = input[start..end];
    
    // Only validate when we know it should be an identifier
    match std::str::from_utf8(slice) {
        Ok(valid) => Ok(valid),
        Err(e) => Err(LexError::InvalidUtf8 {
            bytes: slice.to_vec(),
            error: e,
            location: ByteOffset(start),
        }),
    }
}
```

**Benefits:**
- ✅ No panic on invalid UTF-8
- ✅ Can emit structured error with raw bytes
- ✅ Parser can continue past errors
- ✅ Error message shows problematic bytes: `[0xFF, 0xFE]`

### 2.3 Current HWML Lexer Analysis

**From `crates/hwml-surface/src/lex.rs`:**

```rust
#[derive(Logos, Copy, Clone, Debug)]
#[logos(source = [u8], error = LexicalError)]  // ✅ Already using &[u8]!
```

**Good:**
- ✅ Uses byte-level lexing
- ✅ Handles Unicode line breaks correctly
- ✅ Regex for identifiers: `r"[^\p{gc=Separator}\p{gc=Control}{}()\[\];,]+"`

**Potential issues:**
- ⚠️ Column tracking uses `slice.len()` (byte count, not grapheme count)
- ⚠️ Comments: "Using byte count (not char count) - fine for MLIR FileLineColLoc"
- ⚠️ No explicit invalid UTF-8 handling

**Recommendation:** This is actually CORRECT for internal representation (byte offsets), but needs care when rendering diagnostics.

---

## 3. The Three Position Systems

### 3.1 Internal: Byte Offsets (The Source of Truth)

**What HWML uses:**

```rust
pub struct Lexer<'input> {
    inner: logos::Lexer<'input, Token>,
    line: usize,   // Current line (1-based)
    column: usize, // Current column (BYTE OFFSET, not graphemes!)
}
```

**Why this is correct:**
- ✅ **Deterministic:** Same file = same offsets
- ✅ **Fast:** No Unicode decoding needed
- ✅ **LSP-compatible:** Can convert to UTF-8 positions
- ✅ **MLIR-compatible:** `FileLineColLoc` accepts byte-based columns

**Trade-off:** Must convert to graphemes/columns for human-facing output.

### 3.2 LSP: UTF-16 Code Units (The Trap)

**The LSP specification (pre-3.17):**

```typescript
interface Position {
  line: number;       // 0-based
  character: number;  // UTF-16 code units (not bytes, not code points!)
}
```

**Why UTF-16?** Because LSP was designed by Microsoft for VS Code, which uses JavaScript strings (UTF-16 internally).

**The problem:**

```
Text:        "Hello 👩🏽‍💻 World"
Bytes:       [H][e][l][l][o][ ][👩🏽‍💻][ ][W][o][r][l][d]
UTF-8:       0  1  2  3  4  5  6          17 18 19 20 21 22
UTF-16:      0  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15
Graphemes:   0  1  2  3  4  5  6          7  8  9 10 11 12
```

The emoji `👩🏽‍💻` is:
- 11 bytes in UTF-8
- 5 UTF-16 code units (2 + 1 + 1 + 2)
- 1 grapheme cluster

**If your server sends byte offset 17, but the client expects UTF-16 offset 10, diagnostics will be misaligned!**

### 3.3 LSP 3.17+: Position Encoding Negotiation

**The fix:**

```rust
// During LSP initialization handshake
fn initialize(&self, params: InitializeParams) -> InitializeResult {
    InitializeResult {
        capabilities: ServerCapabilities {
            position_encoding: Some(PositionEncodingKind::UTF8),  // Request UTF-8!
            // ... other capabilities
        },
        // ...
    }
}
```

**Fallback strategy (if client doesn't support UTF-8):**

```rust
pub struct LineIndex {
    /// Byte offset of each line start
    line_starts: Vec<usize>,

    /// UTF-16 code unit offsets (lazy computed per line)
    utf16_offsets: HashMap<usize, Vec<usize>>,
}

impl LineIndex {
    /// Convert byte offset to LSP Position (UTF-16)
    pub fn byte_to_lsp_position(&self, byte_offset: usize) -> Position {
        let line = self.line_for_byte(byte_offset);
        let line_start = self.line_starts[line];
        let byte_col = byte_offset - line_start;

        // Convert byte column to UTF-16 column
        let utf16_col = self.byte_to_utf16_col(line, byte_col);

        Position { line, character: utf16_col }
    }

    fn byte_to_utf16_col(&self, line: usize, byte_col: usize) -> usize {
        // Walk the line counting UTF-16 code units
        let line_text = self.line_text(line);
        line_text[..byte_col].encode_utf16().count()
    }
}
```

**Reference:** `rust-analyzer`'s `line_index` crate does exactly this.

### 3.4 Terminal: Grapheme Clusters + Display Width

**What humans perceive:**

```rust
use unicode_segmentation::UnicodeSegmentation;

let text = "Hello 👩🏽‍💻 World";
let graphemes: Vec<&str> = text.graphemes(true).collect();
// ["H", "e", "l", "l", "o", " ", "👩🏽‍💻", " ", "W", "o", "r", "l", "d"]
```

**What terminals display:**

```rust
use unicode_width::UnicodeWidthStr;

let text = "👩🏽‍💻";
let width = text.width();  // Usually 2, but can be 1 or 3 depending on terminal!
```

**The fundamental problem:** There is NO universal standard for emoji width. Different terminals report different values.

| Terminal | `👩🏽‍💻` Width | Notes |
|----------|-------------|-------|
| iTerm2 | 2 cells | Most common |
| tmux | 2 cells | Depends on `$TERM` |
| Alacritty | 1 cell | Modern Unicode-aware |
| Windows Terminal | 2 cells | Varies by font |
| VS Code terminal | 2 cells | Electron-based |

**Implication:** ASCII-art diagnostic underlining (`^^^`) will ALWAYS be fragile with emojis.

---

## 4. Diagnostic Rendering Strategies

### 4.1 CLI: The `miette` / `ariadne` Approach

**Strategy:** Best-effort terminal rendering with grapheme awareness.

**Using `miette`:**

```rust
use miette::{Diagnostic, SourceSpan};

#[derive(Debug, Diagnostic)]
#[diagnostic(code(hwml::type_error))]
struct TypeMismatch {
    #[source_code]
    src: String,

    #[label("expected {expected}")]
    actual_span: SourceSpan,

    #[label("declared here")]
    declaration_span: SourceSpan,

    expected: String,
    actual: String,
}
```

**What `miette` does:**
1. Takes byte-based `SourceSpan` (offset, length)
2. Converts to line:column using byte offsets
3. Renders with `unicode-width` for display
4. Best-effort alignment (accepts it may be wrong with complex emojis)

**Example output:**

```
error: type mismatch
  ┌─ example.hwml:3:10
  │
3 │ def 🚀_speed : Nat = "hello"
  │     ────────         ^^^^^^^ expected Nat, got String
  │     │
  │     declared here
```

**Benefits:**
- ✅ Handles most cases well
- ✅ Clean, modern error output
- ✅ Multi-span support
- ⚠️ May misalign with complex emoji (acceptable trade-off)

### 4.2 LSP: The Escape Hatch

**Key insight:** LSP doesn't send formatted text. It sends structured data.

**LSP Diagnostic structure:**

```rust
pub struct Diagnostic {
    pub range: Range,           // Start/end positions (not formatted strings!)
    pub severity: DiagnosticSeverity,
    pub code: Option<String>,
    pub message: String,
    pub related_information: Option<Vec<DiagnosticRelatedInformation>>,
}

pub struct Range {
    pub start: Position,  // { line: u32, character: u32 }
    pub end: Position,
}
```

**The client (editor) handles rendering:**
- VS Code: Draws red squiggly underlines using its own layout engine
- Neovim: Uses virtual text and highlights
- Emacs: Uses overlays

**No ASCII-art needed!** The editor knows how to align underlines because it controls the display.

**Implementation:**

```rust
// HWML's internal representation
struct InternalDiagnostic {
    file_id: FileId,
    byte_range: ByteRange,  // (start: usize, end: usize)
    message: String,
    severity: Severity,
    related: Vec<(ByteRange, String)>,
}

// Convert to LSP
fn to_lsp_diagnostic(
    &self,
    line_index: &LineIndex,
    encoding: PositionEncoding,
) -> lsp_types::Diagnostic {
    let range = match encoding {
        PositionEncoding::Utf8 => {
            // Direct conversion (fast path)
            Range {
                start: line_index.byte_to_position_utf8(self.byte_range.start),
                end: line_index.byte_to_position_utf8(self.byte_range.end),
            }
        }
        PositionEncoding::Utf16 => {
            // Conversion with UTF-16 mapping (slower)
            Range {
                start: line_index.byte_to_position_utf16(self.byte_range.start),
                end: line_index.byte_to_position_utf16(self.byte_range.end),
            }
        }
    };

    lsp_types::Diagnostic {
        range,
        severity: Some(self.severity.to_lsp()),
        code: None,
        message: self.message.clone(),
        related_information: self.related.iter().map(|(r, m)| {
            DiagnosticRelatedInformation {
                location: Location {
                    uri: self.file_id.to_uri(),
                    range: byte_range_to_lsp(*r, line_index, encoding),
                },
                message: m.clone(),
            }
        }).collect(),
        ..Default::default()
    }
}
```

**Benefits:**
- ✅ **Zero alignment issues** - Editor handles display
- ✅ **Works with all character sets** - No grapheme counting needed
- ✅ **Faster** - No terminal width calculations
- ✅ **Richer UX** - Editors can show colors, tooltips, inline hints

### 4.3 Structured Diagnostics: The `asai` Philosophy

**Core principle:** Separate diagnostic **generation** from **presentation**.

**Internal representation:**

```rust
pub struct Diagnostic {
    pub severity: Severity,
    pub code: DiagnosticCode,
    pub message: String,
    pub labels: Vec<Label>,         // Primary highlights
    pub notes: Vec<String>,         // Additional context
    pub help: Option<String>,       // Suggested fix
    pub related: Vec<Diagnostic>,   // Nested/contextual diagnostics
}

pub struct Label {
    pub file_id: FileId,
    pub range: ByteRange,    // ALWAYS byte offsets internally
    pub message: String,
    pub style: LabelStyle,   // Primary, Secondary, Note
}
```

**Multiple renderers:**

```rust
trait DiagnosticRenderer {
    fn render(&self, diag: &Diagnostic) -> String;
}

struct CliRenderer {
    use_color: bool,
    grapheme_aware: bool,
}

struct LspRenderer {
    position_encoding: PositionEncoding,
}

struct JsonRenderer;  // For tools/CI
```

**Usage:**

```rust
// Generate diagnostic (format-agnostic)
let diag = Diagnostic {
    severity: Severity::Error,
    code: DiagnosticCode::TypeMismatch,
    message: "type mismatch".to_string(),
    labels: vec![
        Label {
            file_id: file_id,
            range: ByteRange::new(45, 50),  // Byte offsets!
            message: "expected Nat".to_string(),
            style: LabelStyle::Primary,
        },
    ],
    // ...
};

// Render for CLI
let cli_output = CliRenderer::new().render(&diag);
eprintln!("{}", cli_output);

// Render for LSP
let lsp_diag = LspRenderer::new(encoding).render(&diag);
client.publish_diagnostics(lsp_diag);
```

**Benefits:**
- ✅ **Single source of truth** - One diagnostic, multiple presentations
- ✅ **Testable** - Test diagnostic logic without rendering
- ✅ **Future-proof** - Add new renderers (HTML, IDE plugins) without changing core
- ✅ **Consistent** - Same errors everywhere

---

## 5. Bridging `asai` to LSP

### 5.1 The InfoTree Architecture (Lean 4)

**Problem:** Standard LSP is insufficient for dependent types.

**Standard LSP capabilities:**
- `textDocument/hover` - Show type at cursor (stateless)
- `textDocument/signatureHelp` - Show function signatures (stateless)
- `textDocument/publishDiagnostics` - Show errors (one-way)

**What dependent types need:**
- Interactive goal state (current proof obligations)
- Metavariable context (what's unsolved, why)
- Constraint graph (what equations exist)
- Elaboration trace (how did we get here)

**Lean 4's solution: Custom RPC endpoints + InfoTree**

```rust
// InfoTree: Spatial mapping from source positions to elaboration state
enum InfoTree<'db> {
    Context {
        context: PartialContextInfo<'db>,
        children: Vec<InfoTree<'db>>,
    },
    Node {
        info: Info<'db>,
        children: Vec<InfoTree<'db>>,
    },
    Hole(MetaVarId),  // Unsolved metavariable
}

struct Info<'db> {
    syntax: SourceRange,
    expr: Option<Expr<'db>>,
    expected_type: Option<Type<'db>>,
    implicit_args: Vec<(String, Type<'db>)>,
}
```

**Custom LSP endpoints:**

```typescript
// Request goal state at cursor
interface GoalStateRequest {
    textDocument: TextDocumentIdentifier;
    position: Position;
}

interface GoalStateResponse {
    hypotheses: Array<{ name: string; type: string }>;
    goal: string;
    metavariables: Array<{
        id: string;
        type: string;
        created_at: Location;
    }>;
}

// Server implements: $/lean/goalState
client.request('$/lean/goalState', params);
```

**How it works:**

1. **During elaboration**, build InfoTree alongside type checking
2. **On LSP query**, search InfoTree for node containing cursor position
3. **Return structured JSON** (not formatted text) to client
4. **Client renders** in editor-specific way (VS Code panel, Neovim split, Emacs buffer)

**Benefits:**
- ✅ **Works in terminals** - Neovim `lean.nvim` uses same RPC, renders in split pane
- ✅ **Rich interactivity** - Click on metavariable to see constraints
- ✅ **Editor-agnostic** - Same server, different UIs
- ✅ **No formatting issues** - Client handles all rendering

### 5.2 HWML Adaptation

**Recommendation:**

```rust
// Build InfoTree during elaboration
pub struct InfoTreeState<'db> {
    enabled: bool,  // Disable for batch compilation
    trees: Vec<InfoTree<'db>>,
}

impl<'db> Elaborator<'db> {
    fn elaborate_application(
        &mut self,
        func: &SurfaceExpr,
        arg: &SurfaceExpr,
    ) -> Result<CoreExpr<'db>, ElabError> {
        // Capture elaboration state if InfoTree enabled
        let ctx = if self.info_tree.enabled {
            Some(self.capture_context())
        } else {
            None
        };

        // Perform elaboration
        let result = self.elaborate_app_inner(func, arg)?;

        // Record in InfoTree
        if let Some(ctx) = ctx {
            self.info_tree.add_node(InfoTree::Application {
                range: func.span().merge(arg.span()),
                func_type: self.infer_type(func)?,
                arg_type: self.infer_type(arg)?,
                result_type: self.infer_type(&result)?,
            });
        }

        Ok(result)
    }
}

// Custom LSP endpoint
async fn hwml_metavar_info(
    &self,
    params: MetavarInfoParams,
) -> Result<MetavarInfoResponse> {
    let file = self.get_file(params.uri)?;
    let byte_offset = self.position_to_byte(params.position, file)?;

    // Query InfoTree at position
    let info = file.info_tree.query(byte_offset)?;

    // Return structured data
    Ok(MetavarInfoResponse {
        metavariables: info.metavars.iter().map(|m| {
            MetavarInfo {
                id: format!("?{}", m.id.0),
                type_: self.pretty_print_type(m.ty),
                created_at: self.byte_to_lsp_location(m.created_at),
                created_by: format!("{:?}", m.origin),  // Could be richer
                constraints: m.constraints.iter().map(|c| {
                    format!("{:?}", c)  // Could be structured
                }).collect(),
            }
        }).collect(),
    })
}
```

---

## 6. Production Implementation Examples

### 6.1 rust-analyzer's `LineIndex`

**Source:** `rust-analyzer/crates/ide-db/src/line_index.rs`

```rust
pub struct LineIndex {
    /// Byte offset of each line start
    newlines: Vec<TextSize>,

    /// UTF-16 code unit offsets for lines containing non-ASCII
    /// Only computed lazily when needed for LSP
    utf16_lines: HashMap<u32, Utf16LineData>,
}

impl LineIndex {
    /// Convert byte offset to LSP position
    pub fn line_col(&self, offset: TextSize) -> LineCol {
        let line = self.newlines.partition_point(|&it| it <= offset) - 1;
        let line_start = self.newlines[line];
        let col = offset - line_start;

        LineCol { line: line as u32, col: col.into() }
    }

    /// Convert to UTF-16 for LSP (only if client doesn't support UTF-8)
    pub fn to_utf16(&self, line_col: LineCol) -> Utf16LineCol {
        let utf16_data = self.utf16_lines.get(&line_col.line);
        match utf16_data {
            None => {
                // Line is ASCII-only, byte offset = UTF-16 offset
                Utf16LineCol {
                    line: line_col.line,
                    col: line_col.col,
                }
            }
            Some(data) => {
                // Convert using precomputed mapping
                let utf16_col = data.to_utf16_col(line_col.col);
                Utf16LineCol {
                    line: line_col.line,
                    col: utf16_col,
                }
            }
        }
    }
}
```

**Key optimizations:**
- ✅ UTF-16 conversion is **lazy** (only computed when needed)
- ✅ **Per-line caching** (most lines are ASCII, no conversion needed)
- ✅ **Binary search** for line lookup (O(log N))

### 6.2 GHC's Source Locations

**GHC tracks locations at multiple granularities:**

```haskell
-- Exact source location (byte-based)
data RealSrcLoc = SrcLoc {
    srcLocFile :: FastString,
    srcLocLine :: {-# UNPACK #-} !Int,
    srcLocCol  :: {-# UNPACK #-} !Int  -- Character column (not byte!)
}

-- GHC counts columns in CHARACTERS (code points), not bytes
-- This is a deliberate choice for Haskell's Unicode support
```

**Conversion strategy:**

```haskell
-- GHC's lexer tracks character positions
alexGetByte :: AlexInput -> Maybe (Char, AlexInput)
alexGetByte input =
    case utf8DecodeChar (input_bytes input) of
        (c, len) -> Just (c, advance_input input len)

advance_input :: AlexInput -> Int -> AlexInput
advance_input input len = input {
    input_bytes = drop len (input_bytes input),
    input_col   = input_col input + 1  -- Increment by 1 character, not bytes
}
```

**Trade-offs:**
- ✅ Human-friendly column numbers
- ⚠️ Slower lexing (UTF-8 decoding required)
- ⚠️ Still doesn't match terminal width (grapheme clusters)

### 6.3 Lean 4's Lean.Data.Lsp.Utf16

**Lean's approach:**

```lean
structure Utf16Pos where
  line : Nat
  character : Nat  -- UTF-16 code units

-- Conversion from byte positions
def Rope.utf16PosOf (rope : Rope) (bytePos : Nat) : Utf16Pos := ...

-- Precomputed offsets for fast conversion
structure Rope where
  text : String
  byteOffsets : Array Nat      -- Line start offsets
  utf16Offsets : Array Nat     -- Cumulative UTF-16 code units per line
```

**Key insight:** Lean uses a **rope data structure** with precomputed offsets. This makes conversions O(1) after initial construction.

---

## 7. Recommended Architecture for HWML

### 7.1 Three-Layer Design

**Layer 1: Internal (Byte-Based)**

```rust
// All internal positions are byte offsets
pub struct ByteRange {
    pub start: usize,
    pub end: usize,
}

// Lexer produces byte-based tokens
impl Lexer<'_> {
    pub fn next_token(&mut self) -> Option<(ByteRange, Token)> { ... }
}

// Parser consumes byte-based tokens
pub struct ParsedExpr {
    pub span: ByteRange,
    pub kind: ExprKind,
}
```

**Layer 2: Diagnostic Generation (Format-Agnostic)**

```rust
// Generate diagnostics with byte ranges
pub struct Diagnostic {
    pub severity: Severity,
    pub code: Code,
    pub message: String,
    pub labels: Vec<Label>,  // Labels reference byte ranges
    pub notes: Vec<String>,
    pub help: Option<String>,
}

pub struct Label {
    pub file_id: FileId,
    pub range: ByteRange,  // Byte offsets!
    pub message: String,
    pub style: LabelStyle,
}
```

**Layer 3: Rendering (Format-Specific)**

```rust
// CLI renderer (using miette)
impl CliRenderer {
    fn render(&self, diag: &Diagnostic, files: &FileDb) -> String {
        let source = files.get_source(diag.file_id);

        // Convert byte ranges to miette SourceSpans
        let spans = diag.labels.iter().map(|label| {
            miette::SourceSpan::new(
                label.range.start.into(),
                (label.range.end - label.range.start).into(),
            )
        });

        // miette handles grapheme counting and rendering
        let report = miette::MietteReport::new(diag.message.clone())
            .with_labels(spans)
            .with_source_code(source);

        format!("{:?}", report)
    }
}

// LSP renderer
impl LspRenderer {
    fn render(
        &self,
        diag: &Diagnostic,
        line_index: &LineIndex,
    ) -> lsp_types::Diagnostic {
        let range = match self.position_encoding {
            PositionEncoding::Utf8 => {
                line_index.byte_range_to_lsp_utf8(diag.primary_label().range)
            }
            PositionEncoding::Utf16 => {
                line_index.byte_range_to_lsp_utf16(diag.primary_label().range)
            }
        };

        lsp_types::Diagnostic {
            range,
            severity: Some(diag.severity.to_lsp()),
            message: diag.message.clone(),
            // ... map labels to related_information
            ..Default::default()
        }
    }
}
```

### 7.2 Position Encoding Module

**Centralized conversion logic:**

```rust
pub struct LineIndex {
    /// Source text (for reference)
    text: String,

    /// Byte offset of each line start
    line_starts: Vec<usize>,

    /// UTF-16 offsets (lazy, only for non-ASCII lines)
    utf16_cache: RefCell<HashMap<usize, Vec<u16>>>,
}

impl LineIndex {
    pub fn new(text: String) -> Self {
        let line_starts = std::iter::once(0)
            .chain(text.match_indices('\n').map(|(i, _)| i + 1))
            .collect();

        Self {
            text,
            line_starts,
            utf16_cache: RefCell::new(HashMap::new()),
        }
    }

    /// Convert byte offset to (line, byte_col)
    pub fn byte_to_line_col(&self, offset: usize) -> (usize, usize) {
        let line = self.line_starts.partition_point(|&start| start <= offset) - 1;
        let col = offset - self.line_starts[line];
        (line, col)
    }

    /// Convert byte offset to LSP Position (UTF-8 mode)
    pub fn byte_to_position_utf8(&self, offset: usize) -> Position {
        let (line, col) = self.byte_to_line_col(offset);
        Position {
            line: line as u32,
            character: col as u32,  // LSP UTF-8: byte offset = character offset
        }
    }

    /// Convert byte offset to LSP Position (UTF-16 mode)
    pub fn byte_to_position_utf16(&self, offset: usize) -> Position {
        let (line, byte_col) = self.byte_to_line_col(offset);
        let utf16_col = self.byte_col_to_utf16_col(line, byte_col);
        Position {
            line: line as u32,
            character: utf16_col as u32,
        }
    }

    fn byte_col_to_utf16_col(&self, line: usize, byte_col: usize) -> usize {
        let line_start = self.line_starts[line];
        let line_end = self.line_starts.get(line + 1).copied()
            .unwrap_or(self.text.len());
        let line_text = &self.text[line_start..line_end];

        // Count UTF-16 code units up to byte_col
        line_text[..byte_col].encode_utf16().count()
    }
}
```

### 7.3 InfoTree for Interactive LSP

```rust
pub struct InfoTree<'db> {
    root: InfoNode<'db>,
}

pub enum InfoNode<'db> {
    Context {
        range: ByteRange,
        context: Vec<(String, Type<'db>)>,
        children: Vec<InfoNode<'db>>,
    },
    Expression {
        range: ByteRange,
        expr: Expr<'db>,
        inferred_type: Type<'db>,
        children: Vec<InfoNode<'db>>,
    },
    Metavariable {
        range: ByteRange,
        meta_id: MetaId,
        origin: MetaOrigin<'db>,
    },
}

impl<'db> InfoTree<'db> {
    /// Query InfoTree at byte offset
    pub fn query(&self, offset: usize) -> Option<&InfoNode<'db>> {
        self.root.find_deepest_containing(offset)
    }
}

impl<'db> InfoNode<'db> {
    fn find_deepest_containing(&self, offset: usize) -> Option<&Self> {
        if !self.range().contains(offset) {
            return None;
        }

        // Try to find deeper match in children
        for child in self.children() {
            if let Some(deeper) = child.find_deepest_containing(offset) {
                return Some(deeper);
            }
        }

        // No child contains it, we're the deepest
        Some(self)
    }
}
```

---

## 8. Implementation Roadmap

### Phase 1: Foundation (Week 1)

**Goal:** Ensure byte-based lexing is correct and safe.

**Tasks:**
1. ✅ Verify `logos` lexer uses `&[u8]` (already done!)
2. Add explicit invalid UTF-8 error handling
3. Validate that column tracking uses byte offsets
4. Add tests for complex Unicode (emoji, combining characters, RTL text)

**Deliverables:**
- Lexer handles invalid UTF-8 gracefully
- All positions are byte-based internally
- Test suite covers Unicode edge cases

### Phase 2: Position Encoding (Week 2)

**Goal:** Build conversion infrastructure for LSP.

**Tasks:**
1. Implement `LineIndex` struct
2. Add `byte_to_position_utf8()` method
3. Add `byte_to_position_utf16()` method (lazy UTF-16 conversion)
4. Implement LSP position encoding negotiation
5. Add conversion tests

**Deliverables:**
- `LineIndex` can convert byte offsets to LSP positions
- Supports both UTF-8 and UTF-16 modes
- Unit tests for conversion correctness

### Phase 3: Structured Diagnostics (Week 3)

**Goal:** Decouple diagnostic generation from presentation.

**Tasks:**
1. Design `Diagnostic` and `Label` structs (byte-based)
2. Implement `CliRenderer` using `miette`
3. Implement `LspRenderer` using `LineIndex`
4. Update elaborator to generate structured diagnostics
5. Add integration tests

**Deliverables:**
- Single diagnostic format for all outputs
- CLI produces beautiful error messages
- LSP produces correct ranges (UTF-8 or UTF-16)
- Both use same underlying data

### Phase 4: LSP InfoTree (Week 4-5)

**Goal:** Support interactive queries for elaboration state.

**Tasks:**
1. Define `InfoTree` and `InfoNode` types
2. Instrument elaborator to build InfoTree
3. Implement custom RPC endpoint: `$/hwml/metavarInfo`
4. Implement custom RPC endpoint: `$/hwml/goalState`
5. Add toggle to disable InfoTree in batch mode

**Deliverables:**
- LSP server exposes elaboration state
- Clients can query metavariable information
- Works in VS Code, Neovim, Emacs
- Minimal performance impact when disabled

### Phase 5: Advanced Rendering (Week 6)

**Goal:** Handle edge cases and optimize performance.

**Tasks:**
1. Add grapheme cluster counting for terminal rendering
2. Optimize LineIndex with lazy UTF-16 conversion
3. Add caching for frequently-accessed positions
4. Test with pathological Unicode (ZWJ sequences, RTL, combining chars)
5. Benchmark conversion performance

**Deliverables:**
- Robust handling of all Unicode edge cases
- Fast LSP responses (<10ms for position conversions)
- Comprehensive Unicode test suite

---

## 9. Key Crates and Dependencies

### 9.1 Essential Crates

**For Lexing:**
- `bstr` (0.2+) - Byte string utilities, UTF-8 validation
- `logos` (0.13+) - Already in use! Supports `&[u8]` lexing

**For Position Encoding:**
- Standard library: `str::encode_utf16()` for UTF-16 conversion
- `unicode-segmentation` (1.10+) - Grapheme cluster iteration
- `unicode-width` (0.1+) - Terminal width calculation (best-effort)

**For Diagnostics:**
- `miette` (7.0+) - Modern diagnostic rendering with colors
- `ariadne` (0.4+) - Alternative, more minimal
- `codespan-reporting` (0.11+) - Lower-level, more control

**For LSP:**
- `lsp-types` (0.95+) - LSP type definitions
- `tower-lsp` (0.20+) - LSP server framework
- `lsp-server` (0.7+) - Alternative, lower-level

### 9.2 Optional Enhancements

**Terminal Detection:**
- `supports-color` - Detect color support
- `terminal_size` - Get terminal dimensions

**Performance:**
- `dashmap` - Concurrent HashMap for caching
- `once_cell` - Lazy static initialization
- `parking_lot` - Faster mutexes

### 9.3 Cargo.toml Example

```toml
[dependencies]
# Lexing (already present)
logos = "0.13"

# UTF-8 handling
bstr = "1.9"
unicode-segmentation = "1.11"
unicode-width = "0.1"

# Diagnostics
miette = { version = "7.2", features = ["fancy"] }

# LSP
lsp-types = "0.95"
tower-lsp = "0.20"

# Performance
dashmap = "5.5"
once_cell = "1.19"
```

---

## 10. Testing Strategy

### 10.1 Unicode Test Suite

**Test categories:**

```rust
#[cfg(test)]
mod unicode_tests {
    use super::*;

    #[test]
    fn test_ascii_only() {
        let source = "def foo = 42";
        // Byte offsets = character offsets
    }

    #[test]
    fn test_basic_unicode() {
        let source = "def café = 42";
        // é is 2 bytes (0xC3 0xA9)
        assert_eq!(byte_offset_of('='), 9);  // Not 8!
    }

    #[test]
    fn test_emoji() {
        let source = "def 🚀_speed = 299792";
        // 🚀 is 4 bytes (U+1F680)
        assert_eq!(byte_offset_of('_'), 8);
    }

    #[test]
    fn test_complex_emoji() {
        let source = "def 👩🏽‍💻_var = 1";
        // 👩🏽‍💻 is 11 bytes (4 code points, 1 grapheme)
        assert_eq!(byte_offset_of('_'), 15);
    }

    #[test]
    fn test_combining_characters() {
        let source = "def e\u{0301} = 1";  // é as e + combining acute
        // Base char + combining mark = 3 bytes
    }

    #[test]
    fn test_rtl_text() {
        let source = "def مرحبا = 42";  // Arabic "hello"
        // RTL text doesn't affect byte offsets
    }

    #[test]
    fn test_invalid_utf8() {
        let source = b"def \xFF\xFE = 42";
        // Should produce LexError::InvalidUtf8
    }

    #[test]
    fn test_zero_width_joiner() {
        let source = "def 👨‍👩‍👧‍👦 = family";
        // Family emoji: 4 people joined with ZWJ
        // 25 bytes, 7 code points, 1 grapheme
    }
}
```

### 10.2 Position Conversion Tests

```rust
#[cfg(test)]
mod position_tests {
    use super::*;

    #[test]
    fn test_utf8_encoding() {
        let source = "Hello 👩🏽‍💻 World";
        let index = LineIndex::new(source.to_string());

        // Position of 'W' (byte offset 18)
        let pos_utf8 = index.byte_to_position_utf8(18);
        assert_eq!(pos_utf8.character, 18);  // UTF-8: byte offset
    }

    #[test]
    fn test_utf16_encoding() {
        let source = "Hello 👩🏽‍💻 World";
        let index = LineIndex::new(source.to_string());

        // Position of 'W' (byte offset 18)
        let pos_utf16 = index.byte_to_position_utf16(18);
        assert_eq!(pos_utf16.character, 11);  // UTF-16: 5+1+5 code units
    }

    #[test]
    fn test_multiline() {
        let source = "line1\nliné2\nline3";
        let index = LineIndex::new(source.to_string());

        // Position of '2' in "liné2"
        let pos = index.byte_to_line_col(14);
        assert_eq!(pos, (1, 5));  // Line 1, byte column 5
    }
}
```

### 10.3 Diagnostic Rendering Tests

```rust
#[cfg(test)]
mod diagnostic_tests {
    use super::*;

    #[test]
    fn test_cli_rendering() {
        let diag = Diagnostic {
            severity: Severity::Error,
            message: "type mismatch".to_string(),
            labels: vec![
                Label {
                    range: ByteRange::new(10, 15),
                    message: "expected Nat".to_string(),
                    style: LabelStyle::Primary,
                },
            ],
            // ...
        };

        let output = CliRenderer::new().render(&diag);
        assert!(output.contains("type mismatch"));
        assert!(output.contains("expected Nat"));
    }

    #[test]
    fn test_lsp_rendering() {
        let diag = Diagnostic {
            severity: Severity::Error,
            message: "type mismatch".to_string(),
            labels: vec![
                Label {
                    range: ByteRange::new(10, 15),
                    message: "expected Nat".to_string(),
                    style: LabelStyle::Primary,
                },
            ],
            // ...
        };

        let line_index = LineIndex::new("def foo = 42".to_string());
        let lsp_diag = LspRenderer::new(PositionEncoding::Utf8)
            .render(&diag, &line_index);

        assert_eq!(lsp_diag.range.start.character, 10);
        assert_eq!(lsp_diag.range.end.character, 15);
    }
}
```

---

## 11. Performance Considerations

### 11.1 Lazy UTF-16 Conversion

**Problem:** Converting every position to UTF-16 is expensive.

**Solution:** Only convert when needed, cache results.

```rust
pub struct LineIndex {
    line_starts: Vec<usize>,
    utf16_cache: RefCell<HashMap<usize, Utf16LineData>>,
}

impl LineIndex {
    fn get_utf16_data(&self, line: usize) -> Utf16LineData {
        if let Some(cached) = self.utf16_cache.borrow().get(&line) {
            return cached.clone();
        }

        // Compute and cache
        let data = self.compute_utf16_data(line);
        self.utf16_cache.borrow_mut().insert(line, data.clone());
        data
    }
}
```

**Benchmark target:** <1ms for 1000 position conversions

### 11.2 InfoTree Toggle

**Problem:** Building InfoTree has overhead.

**Solution:** Only enable for LSP, disable for batch compilation.

```rust
pub struct ElaboratorConfig {
    pub build_info_tree: bool,  // false for CLI, true for LSP
}

impl Elaborator<'_> {
    fn elaborate_expr(&mut self, expr: &SurfaceExpr) -> Result<CoreExpr> {
        if self.config.build_info_tree {
            let ctx = self.capture_context();
            let result = self.elaborate_expr_inner(expr)?;
            self.info_tree.add_node(/* ... */);
            Ok(result)
        } else {
            // Skip InfoTree construction
            self.elaborate_expr_inner(expr)
        }
    }
}
```

**Benchmark target:** InfoTree overhead <10% when enabled

### 11.3 Grapheme Counting

**Problem:** Iterating graphemes is slower than byte operations.

**Solution:** Only count graphemes when rendering CLI output, not during LSP.

```rust
impl CliRenderer {
    fn align_underline(&self, text: &str, byte_col: usize) -> usize {
        // Count graphemes up to byte_col (slow, but only for CLI)
        text[..byte_col].graphemes(true).count()
    }
}

impl LspRenderer {
    fn byte_to_lsp_position(&self, offset: usize) -> Position {
        // No grapheme counting needed (fast)
        self.line_index.byte_to_position_utf8(offset)
    }
}
```

**Benchmark target:** CLI rendering <5ms per diagnostic

---

## 12. Current HWML Status and Gaps

### 12.1 What HWML Has ✅

From `crates/hwml-surface/src/lex.rs`:

- ✅ **Byte-level lexing** - `#[logos(source = [u8])]`
- ✅ **Unicode line break handling** - Supports LF, CR, CRLF, NEL, LS, PS
- ✅ **Byte-based positions** - Column tracking uses `slice.len()`
- ✅ **Lossless grammar** - All tokens preserved (whitespace, comments)

From `crates/hwml-support/src/line_info.rs`:

- ✅ **Line break tracking** - `LineInfo` struct
- ✅ **Byte offset to line:column** - `loc()` method
- ✅ **Multi-line support** - Handles CR, LF, CRLF

### 12.2 What HWML Lacks ❌

**Position Encoding:**
- ❌ No UTF-16 conversion (needed for LSP compatibility)
- ❌ No position encoding negotiation
- ❌ No grapheme cluster support

**Diagnostics:**
- ❌ No structured diagnostic type (only ad-hoc error messages)
- ❌ No multi-span support
- ❌ No CLI renderer (no `miette` integration)
- ❌ No LSP diagnostic conversion

**LSP:**
- ❌ No InfoTree for interactive queries
- ❌ No custom RPC endpoints
- ❌ No metavariable inspection

**Error Handling:**
- ❌ No explicit invalid UTF-8 handling
- ❌ Lexer panics on errors (see `panic!("Lexical error...")`)

### 12.3 Impact Assessment

**Current state:**
- ✅ **Good foundation** - Byte-based lexing is correct
- ⚠️ **Limited LSP support** - Will have position mismatches with non-ASCII text
- ⚠️ **Poor CLI errors** - No multi-span, no colors, no structure
- ❌ **No interactive features** - Can't query elaboration state

**Priority fixes:**
1. **High:** Add UTF-16 conversion for LSP
2. **High:** Integrate `miette` for CLI diagnostics
3. **Medium:** Add InfoTree for LSP queries
4. **Low:** Grapheme cluster support (nice-to-have for CLI)

---

## 13. References and Further Reading

### 13.1 Academic Papers

**Unicode and Text Processing:**
- Unicode Standard Annex #11 (UAX#11): "East Asian Width" - Terminal width properties
- Unicode Standard Annex #14 (UAX#14): "Unicode Line Breaking Algorithm"
- Unicode Standard Annex #29 (UAX#29): "Unicode Text Segmentation" (grapheme clusters)
- Unicode Standard Annex #31 (UAX#31): "Identifier and Pattern Syntax"

**Error Reporting:**
- **Zhang, Myers** (2014): "Toward General Diagnosis of Static Errors" (SHErrLoc)
- **Raghu et al.** (2024): "Getting into the Flow: Towards Better Type Error Messages" (POPL)
- See also: [[elaboration-error-messages]] for comprehensive error reporting research

### 13.2 LSP Specification

**Official Docs:**
- LSP Specification 3.17: https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/
- Position Encoding (Section 3.6): UTF-8 vs UTF-16 negotiation
- Diagnostic Protocol: `textDocument/publishDiagnostics`

**Key Sections:**
- `PositionEncodingKind`: UTF-8, UTF-16, UTF-32 support
- `DiagnosticRelatedInformation`: Multi-span errors
- `DocumentHighlight`: Semantic highlighting

### 13.3 Production Implementations

**rust-analyzer:**
- `crates/ide-db/src/line_index.rs` - UTF-16 conversion
- `crates/ide-diagnostics/` - Diagnostic generation
- Source: https://github.com/rust-lang/rust-analyzer

**Lean 4:**
- `src/Lean/Data/Lsp/Utf16.lean` - Position encoding
- `src/Lean/Elab/InfoTree/` - InfoTree architecture
- `src/Lean/Server/FileWorker.lean` - LSP server implementation
- Source: https://github.com/leanprover/lean4

**GHC (Haskell):**
- `compiler/GHC/Data/FastString.hs` - Efficient string handling
- `compiler/GHC/Parser/Lexer.x` - Alex lexer with UTF-8 support
- `compiler/GHC/Types/SrcLoc.hs` - Source location tracking
- Source: https://gitlab.haskell.org/ghc/ghc

**Idris 2:**
- `src/Parser/Lexer.idr` - UTF-8 lexing
- `src/Core/Error.idr` - Error messages with provenance
- Source: https://github.com/idris-lang/Idris2

### 13.4 Tools and Crates

**Rust Crates:**
- `bstr` (https://docs.rs/bstr/) - Byte string utilities
- `miette` (https://docs.rs/miette/) - Diagnostic rendering
- `ariadne` (https://docs.rs/ariadne/) - Alternative diagnostics
- `unicode-segmentation` (https://docs.rs/unicode-segmentation/) - Grapheme clusters
- `unicode-width` (https://docs.rs/unicode-width/) - Terminal width
- `tower-lsp` (https://docs.rs/tower-lsp/) - LSP framework

**Testing Tools:**
- `insta` - Snapshot testing for diagnostic output
- `proptest` - Property-based testing for Unicode edge cases

### 13.5 Related HWML Wiki Pages

**Architecture:**
- [[wiki/decisions/ADR-005-debug-information]] - Debug info strategy
- [[wiki/decisions/ADR-008-vfs-abstraction]] - Virtual file system
- [[wiki/implementation/location/streaming-lexer-advantage]] - Lossless lexing

**Research:**
- [[wiki/research/elaboration-error-messages]] - Error reporting (complements this doc)
- [[wiki/research/provenance-deep-dive]] - Metavariable origin tracking
- [[wiki/research/lsp-and-remote-compilation]] - LSP architecture

**Components:**
- `crates/hwml-surface/src/lex.rs` - Current lexer implementation
- `crates/hwml-support/src/line_info.rs` - Line break tracking
- `crates/hwml-vfs/src/lsp.rs` - LSP VFS

---

## 14. Recommendations for HWML

### 14.1 Immediate Actions (This Week)

**1. Fix lexer error handling:**
```rust
// Current (panics on error):
Err(_err) => {
    panic!("Lexical error at {}:{}", self.line, self.column);
}

// Recommended (structured error):
Err(err) => {
    return Some((
        span.start,
        Token::Error,
        span.end,
    ));
}
```

**2. Add UTF-8 validation helper:**
```rust
pub fn validate_identifier(bytes: &[u8]) -> Result<&str, InvalidUtf8Error> {
    std::str::from_utf8(bytes).map_err(|e| InvalidUtf8Error {
        bytes: bytes.to_vec(),
        error: e,
    })
}
```

**3. Add `miette` dependency:**
```toml
[dependencies]
miette = { version = "7.2", features = ["fancy"] }
```

### 14.2 Medium-Term (Next 2 Weeks)

**1. Create diagnostic infrastructure:**
- Define `Diagnostic` and `Label` types
- Implement `CliRenderer` with `miette`
- Update elaborator to generate structured diagnostics

**2. Add LSP position encoding:**
- Implement `LineIndex` with UTF-16 support
- Add position encoding negotiation in LSP handshake
- Update diagnostic conversion to use `LineIndex`

**3. Add comprehensive Unicode tests:**
- Test suite for emoji, combining characters, RTL text
- Benchmark UTF-16 conversion performance
- Validate LSP diagnostic alignment

### 14.3 Long-Term (Next Month)

**1. Implement InfoTree:**
- Design InfoTree structure
- Instrument elaborator to build InfoTree
- Add custom LSP RPC endpoints

**2. Advanced features:**
- Grapheme-aware CLI rendering
- Lazy UTF-16 conversion caching
- Performance profiling and optimization

**3. Documentation:**
- User guide for Unicode support
- Developer docs for adding new diagnostics
- LSP client integration guide (VS Code, Neovim, Emacs)

### 14.4 Non-Goals (What NOT to Do)

**❌ Don't try to perfectly align terminal output with emoji:**
- Terminal width calculation is fundamentally unreliable
- Accept that complex emoji may misalign by 1-2 columns
- Focus on correctness, not perfection

**❌ Don't use character-based positions internally:**
- Byte offsets are the source of truth
- Only convert at presentation layer
- Don't make lexer slower with UTF-8 decoding

**❌ Don't support legacy LSP clients without UTF-8:**
- LSP 3.17 (2021) added UTF-8 support
- Modern editors (VS Code 1.63+, Neovim 0.6+) support it
- Fallback to UTF-16 is nice-to-have, not essential

---

## 15. Key Takeaways

### 15.1 The Three Truths of UTF-8 in Compilers

1. **Bytes are the source of truth**
   - Store positions as byte offsets internally
   - Convert to other representations at boundaries
   - Never lose the byte-to-source mapping

2. **LSP is your friend**
   - Editors handle rendering, so alignment issues vanish
   - Negotiate UTF-8 encoding when possible
   - Structure over formatting

3. **Terminal rendering will always be imperfect**
   - Emoji width is inconsistent across terminals
   - Grapheme clusters don't map 1:1 to columns
   - Accept best-effort alignment with `miette`/`ariadne`

### 15.2 Architecture Principles

**Separation of Concerns:**
- **Generation:** Byte-based, format-agnostic diagnostics
- **Conversion:** Centralized position encoding (LineIndex)
- **Presentation:** Format-specific rendering (CLI, LSP, JSON)

**Lazy Optimization:**
- Don't compute UTF-16 offsets unless needed
- Don't build InfoTree for batch compilation
- Cache frequently-accessed conversions

**Robustness:**
- Handle invalid UTF-8 gracefully (don't panic)
- Test with pathological Unicode inputs
- Validate at boundaries, trust internally

### 15.3 Success Criteria

**For CLI:**
- ✅ Beautiful error messages with colors and multi-span
- ✅ Correct alignment for ASCII and most Unicode
- ⚠️ Acceptable misalignment for complex emoji (±1-2 columns)

**For LSP:**
- ✅ Zero alignment issues (editor handles rendering)
- ✅ Support both UTF-8 and UTF-16 encoding
- ✅ Fast position conversions (<10ms)
- ✅ Rich interactivity (metavariable inspection, goal state)

**For Compiler:**
- ✅ No panics on invalid UTF-8
- ✅ Deterministic byte-based positions
- ✅ Minimal performance overhead
- ✅ Comprehensive Unicode test coverage

---

## Appendix A: Quick Reference

### A.1 Position System Cheat Sheet

| Representation | Use Case | Example | Notes |
|----------------|----------|---------|-------|
| **Byte offset** | Internal storage | `45` | Source of truth |
| **Line:byte_col** | MLIR locations | `(3, 12)` | Fast, deterministic |
| **Line:grapheme_col** | Human display | `(3, 8)` | Slow, fragile |
| **LSP UTF-8** | Modern LSP | `{line: 3, character: 12}` | Same as byte col |
| **LSP UTF-16** | Legacy LSP | `{line: 3, character: 10}` | Requires conversion |

### A.2 Conversion Functions

```rust
// Internal → LSP (UTF-8)
fn byte_to_lsp_utf8(offset: usize) -> Position {
    let (line, col) = line_index.byte_to_line_col(offset);
    Position { line, character: col }
}

// Internal → LSP (UTF-16)
fn byte_to_lsp_utf16(offset: usize) -> Position {
    let (line, byte_col) = line_index.byte_to_line_col(offset);
    let utf16_col = count_utf16_units(&line_text[..byte_col]);
    Position { line, character: utf16_col }
}

// Internal → CLI (graphemes for display)
fn byte_to_grapheme_col(offset: usize) -> usize {
    let (_, byte_col) = line_index.byte_to_line_col(offset);
    line_text[..byte_col].graphemes(true).count()
}
```

### A.3 Common Pitfalls

| Mistake | Impact | Fix |
|---------|--------|-----|
| Using `char` count as column | LSP misalignment | Use byte offset |
| Counting graphemes in lexer | Slow, unnecessary | Count at render time |
| Panicking on invalid UTF-8 | Crashes compiler | Return error token |
| Skipping position encoding negotiation | Broken LSP with emoji | Always negotiate |
| Computing UTF-16 eagerly | Wasted CPU | Lazy conversion |

---

**END OF RESEARCH REPORT**

**Next Steps:**
1. Review this research with the team
2. Prioritize implementation phases
3. Begin Phase 1 (Foundation) with lexer error handling
4. Update [[wiki/index]] and [[wiki/log]] with this research

**Cross-References:**
- Complements: [[elaboration-error-messages]]
- Builds on: [[streaming-lexer-advantage]]
- Informs: Future ADR on diagnostic architecture
