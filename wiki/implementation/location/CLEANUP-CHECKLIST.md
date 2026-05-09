# Location Tracking Cleanup - Quick Checklist

**Date:** 2026-05-06  
**Goal:** Remove experimental line:column code, keep byte-range-only architecture  
**Time:** ~2-3 hours

---

## Quick Reference

**What to DELETE:**
- ❌ `LineColRange` type
- ❌ `LocLexer` class  
- ❌ `ParserContext` class
- ❌ `Position` type (hwml-core)
- ❌ `Location` type (hwml-core)
- ❌ `LocationKind` enum

**What to KEEP:**
- ✅ `LineInfo` (hwml-support)
- ✅ `SourceRange` (hwml-core)
- ✅ `Lexer` (standard byte-based)
- ✅ Byte ranges (`Range<usize>`) in AST

---

## Execution Checklist

### Pre-flight
- [ ] Read `cleanup-task-list.md` for full details
- [ ] Read `cleanup-code-changes.md` for exact code snippets
- [ ] Backup current code: `git checkout -b cleanup-location-tracking`

### Phase 1: hwml-surface (30 min)
- [ ] Edit `crates/hwml-surface/src/syntax.rs`
  - [ ] Delete `LineColRange` struct (lines 4-33)
  - [ ] Simplify `Namespace` struct (remove `line_col` field, dual constructors)
- [ ] Edit `crates/hwml-surface/src/lex.rs`
  - [ ] Delete `LocLexer` struct and impl (lines 266-327)
  - [ ] Update `Lexer` doc comment (clarify byte-only)
- [ ] Edit `crates/hwml-surface/src/parsing.rs`
  - [ ] Delete `ParserContext` struct (lines 12-56)
  - [ ] Simplify `parse()` function (remove ctx parameter)
  - [ ] Remove `LineInfo` import
- [ ] Edit `crates/hwml-surface/src/grammar.lalrpop`
  - [ ] Remove `ctx: &mut ParserContext` from grammar parameters (line 7)
  - [ ] Simplify `Namespace` production (lines 33-40)
  - [ ] Remove `ParserContext` import (line 4)
- [ ] Rebuild: `cd crates/hwml-surface && cargo build`

### Phase 2: hwml-core (30 min)
- [ ] Edit `crates/hwml-core/src/source_range.rs`
  - [ ] Delete `Position` struct (lines 87-124)
  - [ ] Delete `LocationKind` enum (lines 126-141)
  - [ ] Delete `Location` struct and impl (lines 143-273)
  - [ ] Verify `SourceRange` remains (lines 57-85)
- [ ] Rebuild: `cd crates/hwml-core && cargo build`

### Phase 3: Verification (30 min)
- [ ] Search for stragglers: `rg "LineColRange|LocLexer|ParserContext" crates/ --type rust`
  - Expected: No results
- [ ] Search for Position/Location: `rg "hwml_core::Position|hwml_core::Location" crates/ --type rust`
  - Expected: No results
- [ ] Verify LineInfo exists: `rg "LineInfo" crates/hwml-support/ --type rust`
  - Expected: Found in `line_info.rs`
- [ ] Run all tests: `cargo test`
  - Expected: All pass
- [ ] Check examples: `cargo run --bin hwml -- --help`
  - Expected: Runs without error

### Phase 4: Cleanup (15 min)
- [ ] Remove import statements referencing deleted types
- [ ] Check for compiler warnings: `cargo clippy`
- [ ] Format code: `cargo fmt`
- [ ] Commit: `git commit -m "Remove experimental line:column tracking code"`

---

## Success Criteria

✅ **Code compiles** without errors or warnings  
✅ **All tests pass**  
✅ **No references** to deleted types (LineColRange, LocLexer, ParserContext, Position, Location)  
✅ **LineInfo still available** in hwml-support  
✅ **SourceRange still available** in hwml-core  
✅ **Surface AST uses** `loc: Range<usize>` only  
✅ **Grammar uses** `@L` and `@R` directly  

---

## Rollback Plan

If something breaks:
```bash
# Restore previous state
git checkout main
git branch -D cleanup-location-tracking

# Or restore specific file
git checkout main -- crates/hwml-surface/src/syntax.rs
```

---

## After Cleanup

Update documentation:
- [ ] Mark `wiki/implementation/location/` as completed
- [ ] Update `wiki/index.md` to reflect cleanup is done
- [ ] Add note to ADR-014 that cleanup is complete

Test the new pattern:
```rust
// Example: Using byte ranges with lazy LineInfo
let input = b"def foo = 42";
let ast = parse(input).unwrap();

// Get byte range from AST
let span: Range<usize> = ast.statements[0].loc();

// Convert to line:column ONLY for display
let line_info = LineInfo::from_bytes(input);
let (line, col) = line_info.loc(span.start);
eprintln!("Error at {}:{}", line + 1, col + 1);
```

---

## Files Modified Summary

| File | Lines Deleted | Lines Changed |
|------|---------------|---------------|
| `hwml-surface/src/syntax.rs` | ~50 | Clean `Namespace` |
| `hwml-surface/src/lex.rs` | ~62 | Remove `LocLexer` |
| `hwml-surface/src/parsing.rs` | ~45 | Remove `ParserContext` |
| `hwml-surface/src/grammar.lalrpop` | ~5 | Simplify productions |
| `hwml-core/src/source_range.rs` | ~187 | Remove `Position`/`Location` |
| **Total** | **~349** | - |

---

## Quick Command Reference

```bash
# Rebuild everything
cargo build --workspace

# Run all tests
cargo test --workspace

# Search for references
rg "LineColRange|LocLexer|ParserContext" crates/
rg "Position|Location" crates/hwml-core/

# Format and lint
cargo fmt --all
cargo clippy --workspace

# Check dependencies
cargo tree | grep hwml

# Clean build artifacts
cargo clean
```

---

**Ready to execute?** Follow the phases in order, checking off each item. Good luck! 🚀
