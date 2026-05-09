# Detailed Code Changes for Cleanup

**Date:** 2026-05-06  
**Purpose:** Specific file changes to remove line:column tracking  

---

## File 1: `crates/hwml-surface/src/syntax.rs`

### Change 1.1: Remove LineColRange type

**Delete lines 4-33:**
```rust
/// Source location in Line:Column format (0-based)
/// This is more convenient for creating hwml_core::Location later
#[derive(Clone, Copy, Eq, PartialEq, Debug, Hash)]
pub struct LineColRange {
    pub start_line: usize,
    pub start_column: usize,
    pub end_line: usize,
    pub end_column: usize,
}

impl LineColRange {
    pub fn new(start_line: usize, start_column: usize, end_line: usize, end_column: usize) -> Self {
        LineColRange {
            start_line,
            start_column,
            end_line,
            end_column,
        }
    }

    /// Create from a byte range using ParserContext
    pub fn from_byte_range(
        start: usize,
        end: usize,
        ctx: &mut crate::parsing::ParserContext,
    ) -> Self {
        let (start_line, start_column, end_line, end_column) = ctx.range_to_line_col(start, end);
        LineColRange::new(start_line, start_column, end_line, end_column)
    }
}
```

### Change 1.2: Simplify Namespace struct

**Replace lines 50-80:**

**Before:**
```rust
#[derive(Clone, Eq, PartialEq, Debug, Hash)]
pub struct Namespace {
    pub loc: Range<usize>,      // Old byte range (for backward compat)
    pub line_col: LineColRange, // New line:column range
    pub name: Id,
    pub statements: Vec<Statement>,
}

impl Namespace {
    /// Old constructor using byte range (deprecated but kept for compatibility)
    pub fn new(loc: Range<usize>, name: Id, statements: Vec<Statement>) -> Self {
        // Default line_col to zeros - should be replaced with actual conversion
        Namespace {
            loc,
            line_col: LineColRange::new(0, 0, 0, 0),
            name,
            statements,
        }
    }

    /// New constructor using line:column range
    pub fn new_with_line_col(line_col: LineColRange, name: Id, statements: Vec<Statement>) -> Self {
        // Keep old loc as 0..0 for now - can be removed once all code migrated
        Namespace {
            loc: 0..0,
            line_col,
            name,
            statements,
        }
    }
}
```

**After:**
```rust
#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct Namespace {
    pub loc: Range<usize>,
    pub name: Id,
    pub statements: Vec<Statement>,
}
```

---

## File 2: `crates/hwml-surface/src/lex.rs`

### Change 2.1: Remove LocLexer

**Delete lines 266-327:**
```rust
/// Extended lexer that exposes line:column positions for each token.
/// Use this when you need location information during parsing.
pub struct LocLexer<'input> {
    inner: logos::Lexer<'input, Token>,
    line: usize,
    column: usize,
}

impl<'input> LocLexer<'input> {
    pub fn new(input: &'input [u8]) -> Self {
        Self {
            inner: Token::lexer(input),
            line: 1,
            column: 1,
        }
    }
}

/// The output: (Token, byte_span, start_line, start_column)
/// All values are 1-based to match MLIR/CIRCT conventions
pub type SpannedToken = (Token, std::ops::Range<usize>, usize, usize);

impl<'input> Iterator for LocLexer<'input> {
    type Item = SpannedToken;

    fn next(&mut self) -> Option<Self::Item> {
        let token = self.inner.next()?;
        let span = self.inner.span();
        let slice = self.inner.slice();

        // Capture location at START of token
        let out_line = self.line;
        let out_column = self.column;

        // Update state based on token consumed
        match token {
            Ok(Token::Newline) => {
                self.line += 1;
                self.column = 1;
            }
            Ok(Token::BlockComment) => {
                let newlines = slice.iter().filter(|&&b| b == b'\n').count();
                if newlines > 0 {
                    self.line += newlines;
                    let last_nl_idx = slice.iter().rposition(|&b| b == b'\n').unwrap();
                    self.column = slice.len() - last_nl_idx;
                } else {
                    self.column += slice.len();
                }
            }
            Ok(_) => {
                self.column += slice.len();
            }
            Err(_) => {
                // Still update column even on error
                self.column += slice.len();
            }
        }

        Some((token.unwrap_or(Token::Error), span, out_line, out_column))
    }
}
```

### Change 2.2: Update Lexer doc comment

**Replace lines 189-199:**

**Before:**
```rust
/// A streaming lexer that tracks line:column positions natively.
///
/// Because HWML uses a **lossless grammar** (every byte is tokenized,
/// including whitespace and comments), we can track line:column positions
/// incrementally as we stream tokens with ZERO overhead - no pre-computation,
/// no lookup tables, just a simple counter that updates based on tokens consumed.
pub struct Lexer<'input> {
    inner: logos::Lexer<'input, Token>,
    line: usize,   // Current line (1-based for MLIR/CIRCT)
    column: usize, // Current column (1-based for MLIR/CIRCT)
}
```

**After:**
```rust
/// Standard lexer for HWML surface syntax.
///
/// Returns byte-based spans (start_offset, Token, end_offset) suitable for LALRPOP.
/// Location tracking uses line and column internally for error reporting, but the
/// public API only exposes byte offsets. Convert to line:column lazily using
/// LineInfo when formatting diagnostics.
pub struct Lexer<'input> {
    inner: logos::Lexer<'input, Token>,
    line: usize,   // Current line (1-based, for error messages)
    column: usize, // Current column (1-based, for error messages)
}
```

---

## File 3: `crates/hwml-surface/src/parsing.rs`

### Change 3.1: Remove ParserContext entirely

**Delete lines 12-56:**
```rust
/// Helper struct to track line information during parsing.
///
/// **NEW APPROACH**: Because HWML uses a lossless grammar, the lexer now
/// tracks line:column natively as it streams tokens (see `LocLexer`).
/// This ParserContext now uses lazy LineInfo only as a fallback for
/// byte-offset-based grammar rules during migration.
pub struct ParserContext {
    /// Lazy-initialized LineInfo (only created if needed for byte offset conversion)
    line_info: Option<LineInfo>,
    /// Source input (for lazy LineInfo construction)
    input: Vec<u8>,
}

impl ParserContext {
    pub fn new(input: &[u8]) -> Self {
        ParserContext {
            line_info: None,
            input: input.to_vec(),
        }
    }

    /// Convert a byte offset to (line, column) - both 0-based
    ///
    /// **DEPRECATED**: Prefer using `LocLexer` which tracks line:column natively.
    /// This is only for backward compatibility during migration.
    pub fn offset_to_line_col(&mut self, offset: usize) -> (usize, usize) {
        let line_info = self
            .line_info
            .get_or_insert_with(|| LineInfo::from_bytes(&self.input));
        line_info.loc(offset)
    }

    /// Convert a byte range to (start_line, start_col, end_line, end_col) - all 0-based
    ///
    /// **DEPRECATED**: Prefer using `LocLexer` which provides start location directly.
    /// This is only for backward compatibility during migration.
    pub fn range_to_line_col(&mut self, start: usize, end: usize) -> (usize, usize, usize, usize) {
        let line_info = self
            .line_info
            .get_or_insert_with(|| LineInfo::from_bytes(&self.input));
        let (start_line, start_col) = line_info.loc(start);
        let (end_line, end_col) = line_info.loc(end);
        (start_line, start_col, end_line, end_col)
    }
}
```

### Change 3.2: Simplify parse function

**Replace lines 58-70:**

**Before:**
```rust
pub fn parse(input: &[u8]) -> Option<Program> {
    let mut ctx = ParserContext::new(input);
    let lexer = Lexer::new(input);
    let parser = ProgramParser::new();
    let result = parser.parse(input, &mut ctx, lexer);
    match result {
        Ok(program) => Some(program),
        Err(err) => {
            eprintln!("Error: {err:?}");
            None
        }
    }
}
```

**After:**
```rust
pub fn parse(input: &[u8]) -> Option<Program> {
    let lexer = Lexer::new(input);
    let parser = ProgramParser::new();
    let result = parser.parse(input, lexer);
    match result {
        Ok(program) => Some(program),
        Err(err) => {
            eprintln!("Error: {err:?}");
            None
        }
    }
}
```

### Change 3.3: Remove LineInfo import

**Update line 1:**

**Before:**
```rust
use hwml_support::LineInfo;
```

**After:**
```rust
// LineInfo not needed during parsing - used lazily for diagnostics
```

---

## File 4: `crates/hwml-surface/src/grammar.lalrpop`

### Change 4.1: Remove ParserContext from grammar parameters

**Line 7:**

**Before:**
```lalrpop
grammar<'input>(input: &'input [u8], ctx: &mut ParserContext);
```

**After:**
```lalrpop
grammar<'input>(input: &'input [u8]);
```

### Change 4.2: Simplify Namespace production

**Lines 33-40:**

**Before:**
```lalrpop
Namespace: Namespace = {
    <l:@L> "namespace" <name:Id> "{" <stmts:Stmt*> "}" <r:@R> => {
        // Convert byte range to line:column range during parsing
        let loc_range = ctx.range_to_line_col(l, r);
        let line_col = crate::syntax::LineColRange::new(loc_range.0, loc_range.1, loc_range.2, loc_range.3);
        Namespace::new_with_line_col(line_col, name, stmts)
    }
};
```

**After:**
```lalrpop
Namespace: Namespace = {
    <l:@L> "namespace" <name:Id> "{" <stmts:Stmt*> "}" <r:@R> => {
        Namespace::new(l..r, name, stmts)
    }
};
```

### Change 4.3: Remove ParserContext import

**Line 4:**

**Before:**
```lalrpop
use crate::parsing::ParserContext;
```

**After:**
```lalrpop
// No ParserContext needed - using byte ranges only
```

---

## Summary of Deletions

**Total lines removed: ~220**

| File | Lines Deleted | Description |
|------|---------------|-------------|
| `syntax.rs` | ~30 | LineColRange type |
| `syntax.rs` | ~20 | Namespace dual constructors |
| `lex.rs` | ~62 | LocLexer implementation |
| `parsing.rs` | ~45 | ParserContext |
| `grammar.lalrpop` | ~5 | Line:column conversion |
| `source_range.rs` | ~187 | Position and Location types |

**Result:** Cleaner, simpler codebase following byte-range-only pattern.

---

## File 5: `crates/hwml-core/src/source_range.rs`

### Change 5.1: Remove Position type

**Delete lines 87-124:**
```rust
// ============================================================================
// New Location Infrastructure (Line:Column based)
// ============================================================================

/// A position in source code (1-based line and column).
/// Column is a byte offset within the line (also 1-based).
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Position {
    /// Line number (1-based). Line 1 is the first line.
    pub line: u32,
    /// Column number (1-based byte offset). Column 1 is the first character.
    pub column: u32,
}

impl Position {
    pub fn new(line: u32, column: u32) -> Self {
        Position { line, column }
    }

    /// Convert from 0-based (internal LineInfo format) to 1-based (MLIR/Location format)
    pub fn from_zero_based(line: usize, column: usize) -> Self {
        Position {
            line: (line + 1) as u32,
            column: (column + 1) as u32,
        }
    }

    /// Convert to 0-based (for LineInfo lookups)
    pub fn to_zero_based(&self) -> (usize, usize) {
        ((self.line - 1) as usize, (self.column - 1) as usize)
    }

    /// Convert to LSP Position (0-based line, 0-based UTF-16 column)
    /// Note: This returns byte-based column; LSP servers must convert to UTF-16
    pub fn to_lsp_position(&self) -> (u32, u32) {
        (self.line - 1, self.column - 1)
    }
}
```

### Change 5.2: Remove LocationKind and Location

**Delete lines 126-273:**
```rust
/// Location data: either a file range or synthetic.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum LocationKind<'db> {
    /// A real source range with file, start line:col, and end line:col (1-based).
    /// Maps directly to MLIR's FileLineColRange.
    FileLineColRange {
        file: SourceFileId<'db>,
        start_line: u32,
        start_column: u32,
        end_line: u32,
        end_column: u32,
    },
    /// Synthetic/compiler-generated location with a descriptive label.
    /// Examples: "implicit_argument", "desugared", "metavar_?42"
    Synthetic { label: Word<'db> },
}

/// A location in source code, interned for efficiency.
/// This is the primary location type used throughout HWML.
#[salsa::interned]
pub struct Location {
    pub kind: LocationKind<'db>,
}

impl<'db> Location<'db> {
    /// Create a file-based location from line:column positions
    pub fn file_range<Db>(
        db: &'db Db,
        file: SourceFileId<'db>,
        start: Position,
        end: Position,
    ) -> Self
    where
        Db: salsa::Database,
    {
        Location::new(
            db,
            LocationKind::FileLineColRange {
                file,
                start_line: start.line,
                start_column: start.column,
                end_line: end.line,
                end_column: end.column,
            },
        )
    }

    /// Create a file-based location from line:column values
    pub fn file_range_values<Db>(
        db: &'db Db,
        file: SourceFileId<'db>,
        start_line: u32,
        start_column: u32,
        end_line: u32,
        end_column: u32,
    ) -> Self
    where
        Db: salsa::Database,
    {
        Location::new(
            db,
            LocationKind::FileLineColRange {
                file,
                start_line,
                start_column,
                end_line,
                end_column,
            },
        )
    }

    /// Create a synthetic location with a label
    pub fn synthetic<Db>(db: &'db Db, label: &str) -> Self
    where
        Db: salsa::Database,
    {
        let label_word = Word::new(db, label);
        Location::new(db, LocationKind::Synthetic { label: label_word })
    }

    /// Get the file ID if this is a file-based location
    pub fn file<Db>(&self, db: &'db Db) -> Option<SourceFileId<'db>>
    where
        Db: salsa::Database,
    {
        match self.kind(db) {
            LocationKind::FileLineColRange { file, .. } => Some(file),
            LocationKind::Synthetic { .. } => None,
        }
    }

    /// Check if this is a synthetic location
    pub fn is_synthetic<Db>(&self, db: &'db Db) -> bool
    where
        Db: salsa::Database,
    {
        matches!(self.kind(db), LocationKind::Synthetic { .. })
    }

    /// Get start position if this is a file-based location
    pub fn start_position<Db>(&self, db: &'db Db) -> Option<Position>
    where
        Db: salsa::Database,
    {
        match self.kind(db) {
            LocationKind::FileLineColRange {
                start_line,
                start_column,
                ..
            } => Some(Position::new(start_line, start_column)),
            LocationKind::Synthetic { .. } => None,
        }
    }

    /// Get end position if this is a file-based location
    pub fn end_position<Db>(&self, db: &'db Db) -> Option<Position>
    where
        Db: salsa::Database,
    {
        match self.kind(db) {
            LocationKind::FileLineColRange {
                end_line,
                end_column,
                ..
            } => Some(Position::new(end_line, end_column)),
            LocationKind::Synthetic { .. } => None,
        }
    }

    /// Create a Location from a byte range using LineInfo for conversion
    pub fn from_byte_range<Db>(
        db: &'db Db,
        file: SourceFileId<'db>,
        byte_range: Range<usize>,
        line_info: &hwml_support::LineInfo,
    ) -> Self
    where
        Db: salsa::Database,
    {
        let (start_line_0, start_col_0) = line_info.loc(byte_range.start);
        let (end_line_0, end_col_0) = line_info.loc(byte_range.end);

        let start = Position::from_zero_based(start_line_0, start_col_0);
        let end = Position::from_zero_based(end_line_0, end_col_0);

        Location::file_range(db, file, start, end)
    }
}
```

### Change 5.3: Verify SourceRange remains

**Keep lines 57-85 unchanged:**
```rust
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct SourceRange<'db> {
    pub source: Source<'db>,
    pub range: Range<usize>,  // Byte offsets
}

impl<'db> SourceRange<'db> {
    pub fn new(source: Source<'db>, range: Range<usize>) -> SourceRange<'db> {
        SourceRange { source, range }
    }
}

pub trait HasSourceRange<'db> {
    fn source_range(&self) -> Option<SourceRange<'db>>;
}

impl<'db> HasSourceRange<'db> for SourceRange<'db> {
    fn source_range(&self) -> Option<SourceRange<'db>> {
        self.clone().into()
    }
}

pub struct WithSourceRange<'db, A>(pub A, pub Option<SourceRange<'db>>);

impl<'db, A> HasSourceRange<'db> for WithSourceRange<'db, A> {
    fn source_range(&self) -> Option<SourceRange<'db>> {
        self.1.clone()
    }
}
```

**Note:** These types are used for error reporting and should remain.

---

## Verification Commands

After making all changes, run these commands to verify:

```bash
# 1. Rebuild surface parser (regenerates LALRPOP grammar)
cd crates/hwml-surface
cargo clean
cargo build

# 2. Check for any remaining references
cd ../..
rg "LineColRange|LocLexer|ParserContext" crates/ --type rust
rg "hwml_core::Position|hwml_core::Location" crates/ --type rust

# 3. Run all tests
cargo test

# 4. Check that LineInfo is still available
rg "LineInfo" crates/hwml-support/ --type rust
```

Expected results:
- No matches for `LineColRange`, `LocLexer`, `ParserContext`
- No matches for `Position`/`Location` (except MLIR FFI in hwml-circt-sys)
- `LineInfo` found only in `hwml-support/src/line_info.rs`
- All tests pass
