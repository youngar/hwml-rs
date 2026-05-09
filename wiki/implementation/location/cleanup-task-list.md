# Location Tracking Cleanup Task List

**Date:** 2026-05-06  
**Purpose:** Remove experimental line:column tracking code  
**Status:** Ready to execute  
**Estimated Time:** 2-3 hours

---

## Overview

Remove all experimental line:column tracking infrastructure that was added but is not part of the final architecture. The final design uses **byte ranges only** with lazy `LineInfo` conversion for diagnostics.

**Keep:**
- ✅ `LineInfo` in `hwml-support` (needed for diagnostics)
- ✅ Byte ranges (`Range<usize>`) in surface AST
- ✅ `SourceRange` in `hwml-core` (used for error reporting)

**Remove:**
- ❌ `LineColRange` type
- ❌ `LocLexer` (streaming line:column tracker)
- ❌ `ParserContext` and its methods
- ❌ `line_col` field from `Namespace`
- ❌ `Position` and `Location` types from `hwml-core`
- ❌ LALRPOP grammar usage of line:column conversion

---

## Task List

### Phase 1: hwml-surface cleanup (30 min)

#### 1.1: Remove `LineColRange` type
**File:** `crates/hwml-surface/src/syntax.rs`
- [ ] Delete `LineColRange` struct (lines 7-33)
- [ ] Remove doc comment reference to `hwml_core::Location` (line 5)

#### 1.2: Remove `line_col` field from `Namespace`
**File:** `crates/hwml-surface/src/syntax.rs`
- [ ] Remove `line_col: LineColRange` field from `Namespace` struct (line 53)
- [ ] Update `Namespace::new()` to remove `line_col` initialization (lines 60-68)
- [ ] Delete `Namespace::new_with_line_col()` constructor (lines 70-80)
- [ ] Keep only `loc: Range<usize>` field

#### 1.3: Remove `LocLexer`
**File:** `crates/hwml-surface/src/lex.rs`
- [ ] Delete `LocLexer` struct (lines 268-273)
- [ ] Delete `LocLexer::new()` impl (lines 274-281)
- [ ] Delete `SpannedToken` type alias (line 286)
- [ ] Delete `LocLexer` Iterator impl (lines 288-327)
- [ ] Remove doc comment about streaming line:column tracking (lines 189-194)
- [ ] Update `Lexer` doc comment to clarify it's the only lexer (line 195-199)

#### 1.4: Remove `ParserContext`
**File:** `crates/hwml-surface/src/parsing.rs`
- [ ] Delete entire `ParserContext` struct (lines 18-56)
- [ ] Update `parse()` function signature to remove `ctx` parameter
- [ ] Remove `ctx` creation in `parse()` (line 59)
- [ ] Remove `ctx` parameter from `parser.parse()` call (line 62)

#### 1.5: Update LALRPOP grammar
**File:** `crates/hwml-surface/src/grammar.lalrpop`
- [ ] Remove `ctx: &mut ParserContext` from grammar parameters (line 7)
- [ ] Update `Namespace` production to use simple constructor (lines 33-40):
  ```lalrpop
  Namespace: Namespace = {
      <l:@L> "namespace" <name:Id> "{" <stmts:Stmt*> "}" <r:@R> => {
          Namespace::new(l..r, name, stmts)
      }
  };
  ```
- [ ] Verify all other productions use byte ranges only

### Phase 2: hwml-core cleanup (30 min)

#### 2.1: Remove `Position` type
**File:** `crates/hwml-core/src/source_range.rs`
- [ ] Delete `Position` struct (lines 94-124)
- [ ] Remove comment section "New Location Infrastructure" (lines 87-89)

#### 2.2: Remove `Location` and `LocationKind`
**File:** `crates/hwml-core/src/source_range.rs`
- [ ] Delete `LocationKind` enum (lines 128-141)
- [ ] Delete `Location` struct and salsa interned declaration (lines 146-148)
- [ ] Delete entire `Location` impl block (lines 150-273)

#### 2.3: Keep only `SourceRange`
**File:** `crates/hwml-core/src/source_range.rs`
- [ ] Verify `SourceRange` struct remains (lines 58-67)
- [ ] Verify `HasSourceRange` trait remains (lines 69-77)
- [ ] Verify `WithSourceRange` helper remains (lines 79-85)
- [ ] These are used for error reporting with byte ranges

### Phase 3: Update imports and dependencies (15 min)

#### 3.1: Check hwml-surface imports
**File:** `crates/hwml-surface/src/lib.rs`
- [ ] Verify no re-exports of `LineColRange`, `LocLexer`, `ParserContext`
- [ ] Update public API if needed

#### 3.2: Check hwml-core imports  
**File:** `crates/hwml-core/src/lib.rs`
- [ ] Verify no re-exports of `Position`, `Location`
- [ ] Ensure `SourceRange` is still exported

#### 3.3: Search for usage
- [ ] Run: `rg "LineColRange|LocLexer|ParserContext" crates/ --type rust`
- [ ] Run: `rg "hwml_core::Position|hwml_core::Location" crates/ --type rust`
- [ ] Verify no results (except in files being deleted)

### Phase 4: Verification (30 min)

#### 4.1: Rebuild grammar
- [ ] Run: `cd crates/hwml-surface && cargo build`
- [ ] Verify LALRPOP regenerates grammar successfully
- [ ] Check for any compilation errors

#### 4.2: Run tests
- [ ] Run: `cargo test -p hwml-surface`
- [ ] Run: `cargo test -p hwml-core`
- [ ] Run: `cargo test` (full workspace)
- [ ] Verify all tests pass

#### 4.3: Check examples
- [ ] Run: `cargo run --example <example_name>` for any surface parser examples
- [ ] Verify examples still work

### Phase 5: Keep LineInfo (verification only)

#### 5.1: Verify LineInfo is untouched
**File:** `crates/hwml-support/src/line_info.rs`
- [ ] Confirm file is NOT modified
- [ ] This is needed for diagnostic rendering
- [ ] Will be used lazily: `LineInfo::from_bytes(input)`

---

## Testing Strategy

After cleanup, verify the architecture works:

```rust
// Example: Error reporting with byte ranges
fn example_error_reporting() {
    let input = b"def foo = 42";
    let ast = parse(input).unwrap();
    
    // AST nodes have byte ranges
    let def_span: Range<usize> = ast.statements[0].loc();
    
    // Convert to line:column ONLY when displaying error
    let line_info = LineInfo::from_bytes(input);
    let (line, col) = line_info.loc(def_span.start);
    
    eprintln!("Error at {}:{}", line + 1, col + 1);
}
```

---

## Success Criteria

- ✅ Code compiles without warnings
- ✅ All tests pass
- ✅ No references to `LineColRange`, `LocLexer`, `ParserContext`
- ✅ No references to `Position`, `Location` (except MLIR FFI in hwml-circt)
- ✅ Surface AST only has `loc: Range<usize>` fields
- ✅ LALRPOP grammar uses `@L` and `@R` directly
- ✅ `LineInfo` remains available for diagnostic rendering

---

## Notes

**Why keep `LineInfo`?**
- Used for converting byte offsets to line:column for display
- Needed for LSP integration (UTF-8/UTF-16 position encoding)
- Needed for MLIR FileLineColLoc (1-based line:column)
- Built lazily only when needed (not during parsing)

**Why remove `Position` and `Location`?**
- Not used anywhere in the codebase
- Experimental types that didn't fit final architecture
- Would encourage storing line:column in AST (wrong pattern)
