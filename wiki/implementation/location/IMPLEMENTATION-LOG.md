# Location Information Implementation Log

**Date Started:** 2026-05-05  
**Status:** Phase 1 - Foundation (In Progress)

---

## Completed Tasks

### ✅ Phase 1.1: Define `Location` Type (2026-05-05)

**File:** `crates/hwml-core/src/source_range.rs`

**What was implemented:**

1. **`Position` struct** - Represents a single 1-based line:column position
   ```rust
   pub struct Position {
       pub line: u32,      // 1-based
       pub column: u32,    // 1-based byte offset within line
   }
   ```
   - Conversion helpers: `from_zero_based()`, `to_zero_based()`, `to_lsp_position()`

2. **`LocationKind` enum** - The actual location data
   ```rust
   pub enum LocationKind<'db> {
       FileLineColRange {
           file: SourceFileId<'db>,
           start_line: u32,
           start_column: u32,
           end_line: u32,
           end_column: u32,
       },
       Synthetic { label: Word<'db> },
   }
   ```

3. **`Location` interned type** - Salsa-interned for efficiency
   ```rust
   #[salsa::interned]
   pub struct Location {
       pub kind: LocationKind<'db>,
   }
   ```

4. **Helper methods on `Location`:**
   - `file_range()` - Create from `Position` start/end
   - `file_range_values()` - Create from u32 line/col values
   - `synthetic()` - Create synthetic location with label
   - `file()` - Get `SourceFileId` if file-based
   - `is_synthetic()` - Check if synthetic
   - `start_position()` - Get start `Position`
   - `end_position()` - Get end `Position`
   - `from_byte_range()` - **Convert byte Range → Line:Column Location** (uses `LineInfo`)

**Key Design Decisions:**

- ✅ **1-based Line:Column** - Matches MLIR/CIRCT convention
- ✅ **Salsa interning** - Identical locations share storage (memory efficient)
- ✅ **Full ranges** - Store both start and end positions for better diagnostics
- ✅ **No byte offsets** - Native Line:Column eliminates conversion overhead
- ✅ **Synthetic locations** - First-class support for compiler-generated code

**Estimated Time:** 2 hours
**Actual Time:** ~2 hours

---

### ✅ Phase 1.2: Parser Tracks Line:Column During Parsing (2026-05-05)

**Files:** `crates/hwml-surface/src/parsing.rs`, `crates/hwml-surface/src/grammar.lalrpop`, `crates/hwml-surface/src/syntax.rs`

**What was implemented:**

1. **`ParserContext` struct** - Holds `LineInfo` during parsing
   ```rust
   pub struct ParserContext {
       pub line_info: LineInfo,
   }
   ```
   - Methods: `offset_to_line_col()`, `range_to_line_col()`
   - Created once per parse and passed through LALRPOP grammar

2. **`LineColRange` struct** in surface syntax
   ```rust
   pub struct LineColRange {
       pub start_line: usize,
       pub start_column: usize,
       pub end_line: usize,
       pub end_column: usize,
   }
   ```
   - Helper: `from_byte_range(start, end, ctx)` - converts during parsing

3. **Updated LALRPOP grammar** to accept `ParserContext`
   ```lalrpop
   grammar<'input>(input: &'input [u8], ctx: &ParserContext);
   ```

4. **Dual location storage** in syntax nodes (migration strategy)
   ```rust
   pub struct Namespace {
       pub loc: Range<usize>,           // Old (deprecated)
       pub line_col: LineColRange,       // New (preferred)
       pub name: Id,
       pub statements: Vec<Statement>,
   }
   ```
   - Two constructors: `new()` (old), `new_with_line_col()` (new)
   - Allows gradual migration

5. **Updated `Namespace` grammar rule** as proof-of-concept
   ```lalrpop
   Namespace: Namespace = {
       <l:@L> "namespace" <name:Id> "{" <stmts:Stmt*> "}" <r:@R> => {
           let loc_range = ctx.range_to_line_col(l, r);
           let line_col = LineColRange::new(loc_range.0, loc_range.1, loc_range.2, loc_range.3);
           Namespace::new_with_line_col(line_col, name, stmts)
       }
   };
   ```

**Key Design Decisions:**

- ✅ **Convert during parsing** - Byte offsets → Line:Column immediately (no lazy conversion)
- ✅ **Zero overhead** - `LineInfo` built once, lookups are O(log n) binary search
- ✅ **Gradual migration** - Dual storage allows incremental update of all syntax nodes
- ✅ **LALRPOP integration** - Pass `ParserContext` through grammar parameters

**Estimated Time:** 3-4 hours
**Actual Time:** ~2 hours

---

### ✅ Phase 1.2b: Streaming Line:Column Tracking in Lexer (2026-05-05) ⚡

**File:** `crates/hwml-surface/src/lex.rs`

**BREAKTHROUGH**: Discovered that because HWML uses a **lossless grammar** (every byte is tokenized, including whitespace and comments), we can track line:column positions **natively in the lexer** with **ZERO overhead** - no pre-computation, no lookup tables, just incremental counters!

**What was implemented:**

1. **Streaming `Lexer` with native line:column tracking**
   ```rust
   pub struct Lexer<'input> {
       inner: logos::Lexer<'input, Token>,
       line: usize,    // 1-based
       column: usize,  // 1-based
   }
   ```
   - Updates `line` and `column` as tokens are consumed
   - Only two tokens affect line: `Token::Newline` and `Token::BlockComment`
   - All other tokens just advance `column`

2. **`LocLexer` for explicit line:column access**
   ```rust
   pub type SpannedToken = (Token, Range<usize>, usize, usize);
   //                        ^       ^byte_span   ^line  ^column

   for (token, span, line, col) in LocLexer::new(input) {
       // line and col are 1-based and ready for MLIR FileLineColLoc
   }
   ```

3. **Zero-cost algorithm**
   - `Token::Newline` → `line += 1; column = 1`
   - `Token::BlockComment` → scan for `\n`, update accordingly
   - All others → `column += slice.len()` (byte-based column)

**Performance characteristics:**

- **Time complexity**: O(1) per token (just counter increments)
- **Space complexity**: O(1) (two `usize` counters)
- **Comparison to LineInfo approach**:
  - Old: O(N) pre-computation + O(log N) lookups
  - New: O(1) incremental updates + O(1) access
  - **Winner**: Streaming approach (no allocation, perfect cache locality)

**Key insights:**

- Lossless grammars are a **superpower** for location tracking
- Logos' stateless design allows wrapping with stateful tracking
- 1-based line:column matches MLIR/CIRCT expectations perfectly
- Can still fall back to `LineInfo` if needed during migration

**Estimated Time:** N/A (discovered during implementation)
**Actual Time:** ~1 hour

---

## Next Steps

### Phase 1.2: Extend `LineInfo` Integration

**File:** `crates/hwml-support/src/line_info.rs`

**Tasks:**
- [ ] Add reverse conversion: `line_col_to_offset(line, col) -> usize`
- [ ] Add position validation: `validate_position(pos) -> bool`
- [ ] Add text extraction: `span_text(start, end) -> &str`
- [ ] Create Salsa query: `line_info(db, file: SourceFile) -> LineInfo`

**Estimated Time:** 3 hours

---

### Phase 1.3: Parser Integration

**File:** `crates/hwml-surface/src/parsing.rs`

**Tasks:**
- [ ] Create `ParserContext` to hold `LineInfo` during parsing
- [ ] Add `Location<'db>` field to all surface syntax nodes
- [ ] Update parser actions to compute locations using `Location::from_byte_range()`
- [ ] Keep `Range<usize>` temporarily for backward compatibility

**Estimated Time:** 4 hours

---

## Design Notes

### Why 1-based?

MLIR/CIRCT uses 1-based line:column. LSP uses 0-based. We chose 1-based because:
1. **Fewer conversions** - Only convert at LSP boundary (once)
2. **CIRCT alignment** - Main output target expects 1-based
3. **Human-readable** - Users see "Line 1" not "Line 0"

### Why Salsa Interning?

- **Memory efficiency**: 1000 identical `Location::synthetic(db, "implicit_arg")` → 1 stored `LocationKind`
- **Fast equality**: Pointer comparison instead of struct comparison
- **Copy-able**: `Location<'db>` is just an ID, can copy freely

### Why Full Ranges?

- **Better errors**: Can highlight entire expression, not just start position
- **MLIR native**: Maps directly to `FileLineColRange`
- **Multi-line spans**: Can show where expression starts vs ends

---

## Verification

To verify Phase 1.1 is working:

```rust
#[test]
fn test_location_interning() {
    let db = TestDatabase::default();
    let file = create_test_file(&db);
    
    let loc1 = Location::file_range_values(&db, file, 1, 1, 1, 10);
    let loc2 = Location::file_range_values(&db, file, 1, 1, 1, 10);
    
    // Same data → same interned ID
    assert_eq!(loc1, loc2);
}

#[test]
fn test_position_conversion() {
    let pos = Position::from_zero_based(0, 0);
    assert_eq!(pos.line, 1);
    assert_eq!(pos.column, 1);
    
    let (line_0, col_0) = pos.to_zero_based();
    assert_eq!(line_0, 0);
    assert_eq!(col_0, 0);
}

#[test]
fn test_synthetic_location() {
    let db = TestDatabase::default();
    let loc = Location::synthetic(&db, "test_label");
    
    assert!(loc.is_synthetic(&db));
    assert!(loc.file(&db).is_none());
}
```

