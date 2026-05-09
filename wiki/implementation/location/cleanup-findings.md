# Location Tracking Cleanup - Code Search Findings

**Date:** 2026-05-06  
**Purpose:** Document all experimental line:column code found in codebase  
**Status:** Ready for cleanup

---

## Executive Summary

**Total experimental code found: ~349 lines across 5 files**

All experimental line:column tracking code is isolated to:
- `hwml-surface` crate (syntax, lexer, parser, grammar)
- `hwml-core` crate (source_range.rs only)

**Good news:**
- ✅ No usage in elaborator (`hwml-elab`)
- ✅ No usage in CIRCT backend (`hwml-circt`) except MLIR FFI
- ✅ No usage in workspace/VFS/DB layers
- ✅ Clean separation - easy to remove

---

## Detailed Findings

### 1. hwml-surface/src/syntax.rs

**Experimental code:**
- `LineColRange` struct (lines 7-33) - 27 lines
- `Namespace::line_col` field (line 53) - 1 line
- `Namespace::new_with_line_col()` constructor (lines 71-80) - 10 lines
- Modified `Namespace::new()` with dummy line_col (lines 60-68) - 9 lines

**Total:** ~47 lines to remove/modify

**Keep:**
- All other syntax nodes (they only have `loc: Range<usize>`)
- `Id` and `Num` with `Box<str>` (validated UTF-8)

---

### 2. hwml-surface/src/lex.rs

**Experimental code:**
- `LocLexer` struct (lines 268-273) - 6 lines
- `LocLexer::new()` impl (lines 274-281) - 8 lines
- `SpannedToken` type alias (line 286) - 1 line
- `LocLexer` Iterator impl (lines 288-327) - 40 lines
- Misleading doc comments (lines 189-194) - 6 lines

**Total:** ~61 lines to remove

**Keep:**
- Standard `Lexer` struct (only lexer needed)
- Three-tier token design (UTF-8 validation)
- Line/column tracking in `Lexer` (for error messages only)

**Note:** The standard `Lexer` has line/column fields, but these are only used
internally for error reporting (e.g., "Lexical error at 5:10"). The public API
only exposes byte offsets.

---

### 3. hwml-surface/src/parsing.rs

**Experimental code:**
- `ParserContext` struct (lines 18-23) - 6 lines
- `ParserContext::new()` (lines 25-32) - 8 lines
- `ParserContext::offset_to_line_col()` (lines 35-42) - 8 lines
- `ParserContext::range_to_line_col()` (lines 46-55) - 10 lines
- Usage in `parse()` function (lines 59-62) - 4 lines
- Import: `use hwml_support::LineInfo;` (line 1) - 1 line

**Total:** ~45 lines to remove

**Keep:**
- `parse()` function (simplified without ctx parameter)
- All test code (should continue working)

---

### 4. hwml-surface/src/grammar.lalrpop

**Experimental code:**
- `ctx: &mut ParserContext` parameter (line 7) - 1 line
- `use crate::parsing::ParserContext;` import (line 4) - 1 line
- `Namespace` production line:column conversion (lines 36-38) - 3 lines

**Total:** ~5 lines to remove

**Pattern found:**
Only `Namespace` production uses line:column conversion. All other productions
correctly use byte ranges directly (e.g., `Def::new(l..r, ...)`).

**Keep:**
- All other grammar productions (already correct)
- `@L` and `@R` usage throughout

---

### 5. hwml-core/src/source_range.rs

**Experimental code:**
- Comment "New Location Infrastructure" (lines 87-89) - 3 lines
- `Position` struct (lines 94-99) - 6 lines
- `Position` impl (lines 101-124) - 24 lines
- `LocationKind` enum (lines 128-141) - 14 lines
- `Location` struct with salsa interned (lines 146-148) - 3 lines
- `Location` impl (lines 150-273) - 124 lines

**Total:** ~187 lines to remove

**Keep:**
- `SourceFileId` (lines 6-21) - needed
- `SourceInfo` (lines 23-41) - needed
- `Source` (lines 43-55) - needed
- `SourceRange` (lines 57-67) - **needed for error reporting**
- `HasSourceRange` trait (lines 69-77) - needed
- `WithSourceRange` helper (lines 79-85) - needed

**Not used anywhere:**
- `Position` - zero references found
- `Location` - zero references found (except comment in syntax.rs)
- `LocationKind` - zero references found

---

## Search Results

### Search 1: Direct type references
```bash
$ grep -r "LineColRange|LocLexer|ParserContext" crates/ --include="*.rs" -l
crates/hwml-surface/src/parsing.rs
crates/hwml-surface/src/lex.rs
crates/hwml-surface/src/syntax.rs
```

### Search 2: Method calls
```bash
$ grep -r "new_with_line_col|range_to_line_col|offset_to_line_col" crates/ --include="*.lalrpop" -n
crates/hwml-surface/src/grammar.lalrpop:36:let loc_range = ctx.range_to_line_col(l, r);
crates/hwml-surface/src/grammar.lalrpop:38:Namespace::new_with_line_col(line_col, name, stmts)
```

### Search 3: Position/Location usage
```bash
$ grep -r "hwml_core::Position|hwml_core::Location|source_range::Position|source_range::Location" crates/ --include="*.rs" -n
crates/hwml-surface/src/syntax.rs:5:/// This is more convenient for creating hwml_core::Location later
```

**Result:** Only a comment referencing `Location`, no actual usage!

### Search 4: MLIR Location (hwml-circt)
```bash
$ grep -r "Location" crates/hwml-circt/src/context.rs
pub fn unknown_location(&self) -> MlirLocationWrapper { ... }
pub fn create_module(&self, location: MlirLocationWrapper) -> MlirModuleWrapper { ... }
```

**Result:** These are MLIR FFI types (`MlirLocationWrapper`), not our `Location` type. Safe to ignore.

---

## Dependencies

**hwml-support:**
- ✅ `LineInfo` - **KEEP** (needed for diagnostics)
- No other location-related code

**Imports to clean up:**
```rust
// In syntax.rs
// DELETE: comment about hwml_core::Location

// In parsing.rs  
// DELETE: use hwml_support::LineInfo;

// In grammar.lalrpop
// DELETE: use crate::parsing::ParserContext;
```

---

## Impact Analysis

**Affected crates:**
- `hwml-surface` - Main impact, ~158 lines removed
- `hwml-core` - Secondary impact, ~187 lines removed
- **Total:** ~345 lines removed

**Unaffected crates:**
- `hwml-elab` - No changes needed ✅
- `hwml-circt` - No changes needed ✅
- `hwml-vfs` - No changes needed ✅
- `hwml-db` - No changes needed ✅
- `hwml-workspace` - No changes needed ✅
- `hwml-support` - No changes needed ✅

**Risk:** LOW
- Code is isolated and unused
- No complex refactoring needed
- Tests should pass with minimal changes

---

## Recommended Order

1. **hwml-surface** first (most interconnected changes)
   - Syntax.rs
   - Lex.rs
   - Parsing.rs
   - Grammar.lalrpop
   
2. **hwml-core** second (independent)
   - Source_range.rs

3. **Verify** everything still works

---

## Next Steps

1. Review `cleanup-task-list.md` for detailed steps
2. Review `cleanup-code-changes.md` for exact code snippets
3. Use `CLEANUP-CHECKLIST.md` for execution tracking
4. Execute cleanup in order
5. Run tests
6. Commit changes

**Estimated time:** 2-3 hours for careful execution
