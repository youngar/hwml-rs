# Cleanup and Next Steps

**Date**: 2026-05-09  
**Current State**: LSP type checking fix implemented, 14 commits from previous session staged

---

## Immediate Cleanup Tasks

### 1. Commit the LSP Type Checking Fix

**Files to commit:**
- `crates/hwml-db/src/diagnostics.rs` - Made `convert_elab_error_to_diagnostic` public
- `crates/hwml-lsp-server/src/main.rs` - Added elaboration to `compile_file`
- `crates/hwml-lsp-server/Cargo.toml` - Added `hwml_core` and `hwml_elab` dependencies
- `Cargo.lock` - Updated dependencies

**Suggested commit message:**
```
feat(lsp): Add type checking error reporting

The LSP server now reports both parse errors and type checking errors
to the client. This is implemented as a quick fix that runs elaboration
outside the Salsa query system.

Changes:
- Make convert_elab_error_to_diagnostic public
- Run elaboration in LSP compile_file method
- Add hwml_core and hwml_elab dependencies to LSP server

Trade-off: Elaboration is not cached (re-runs on every edit), but this
is acceptable for MVP. Future work: integrate elaboration into Salsa
queries for incremental type checking.

Related: LSP-DIAGNOSTICS-ISSUE.md, LSP-TYPE-CHECKING-FIX.md
```

---

### 2. Clean Up Root Directory Documentation Files

**Move to `docs/sessions/` or `wiki/implementation/`:**
```
CODE-REVIEW-SUPPLEMENT.md → wiki/implementation/provenance/
COMMIT-SUMMARY.md → docs/sessions/2026-05-09-interned-filepaths.md
IMPROVEMENTS-IMPLEMENTED.md → wiki/implementation/provenance/
INTERNED-FILEPATH-CODE-REVIEW.md → wiki/implementation/provenance/
LSP-DIAGNOSTICS-ISSUE.md → wiki/implementation/lsp/
LSP-TYPE-CHECKING-FIX.md → wiki/implementation/lsp/
SESSION-SUMMARY-LSP-FIX.md → docs/sessions/2026-05-09-lsp-diagnostics.md
```

**Archive old status/planning docs:**
```
FRONTEND-ROADMAP.md → design/to-ingest/
IMPLEMENTATION_PLAN_UTF8_VALIDATED_STRS.md → design/to-ingest/
LENIENT-ERROR-HANDLING-IMPLEMENTATION.md → design/to-ingest/
LOCATION_DESIGN_SUMMARY.md → design/to-ingest/
MIXFIX_*.md → design/to-ingest/
MODULE-SYSTEM-*.md → design/to-ingest/
PHASE1_IMPLEMENTATION_STATUS.md → design/to-ingest/
... (and other status docs)
```

---

### 3. Remove Temporary Files

**Delete:**
- `crates/hwml-elab/src/program.rs.bak` (sed backup file)
- `patch` (temporary file)
- `hwml/` (if empty or redundant)

---

### 4. Organize Wiki Documentation

**Create LSP implementation directory:**
```
wiki/implementation/lsp/
├── README.md (overview of LSP architecture)
├── DIAGNOSTICS-ISSUE.md (moved from LSP-DIAGNOSTICS-ISSUE.md)
├── TYPE-CHECKING-FIX.md (moved from LSP-TYPE-CHECKING-FIX.md)
└── ROADMAP.md (future improvements)
```

---

## Code Quality Improvements

### 1. Add Tests for LSP Diagnostics

**Create:** `crates/hwml-lsp-server/tests/diagnostics_test.rs`

```rust
#[test]
fn test_lsp_shows_parse_errors() {
    // Test that parse errors are reported
}

#[test]
fn test_lsp_shows_type_errors() {
    // Test that type checking errors are reported
}

#[test]
fn test_lsp_shows_both_error_types() {
    // Test that both parse and type errors work together
}
```

---

### 2. Suppress Unused Warning in diagnostics.rs

**In `crates/hwml-db/src/diagnostics.rs:204`:**

Current:
```rust
let _ = parse_result.program; // Suppress unused warning
```

Better:
```rust
// Elaboration integration is TODO - see LSP-DIAGNOSTICS-ISSUE.md
let _ = &parse_result.program;
```

---

### 3. Add Documentation Comments

**In `crates/hwml-lsp-server/src/main.rs:299`:**

```rust
/// Compile a file and publish diagnostics to the LSP client.
///
/// This collects both parse errors (from Salsa) and elaboration errors
/// (run directly outside Salsa). The elaboration step is not cached,
/// which is acceptable for MVP but should be optimized in the future
/// by integrating elaboration into the Salsa query system.
///
/// See: `wiki/implementation/lsp/DIAGNOSTICS-ISSUE.md`
fn compile_file(&self, db: &HwmlDatabase, uri: &Uri, file: SourceFile) {
    ...
}
```

---

## Next Steps / Future Work

### Priority 1: Test the LSP in VS Code ⭐

**Action items:**
1. Build the LSP server: `cargo build --release -p hwml_lsp_server`
2. Install in VS Code using the existing extension
3. Test with files containing type errors
4. Verify diagnostics appear correctly

**Test cases:**
```hwml
// Test 1: Type mismatch
def foo : Bit := 42  // Should show error

// Test 2: Undefined variable
def bar : Nat := undefined_var  // Should show error

// Test 3: Parse error
def baz : Nat :=  // Should show error
```

---

### Priority 2: Performance Profiling 📊

**Measure:**
- Time to elaborate small files (<100 lines)
- Time to elaborate medium files (100-500 lines)
- Time to elaborate large files (>500 lines)

**Action:**
```rust
// Add timing in compile_file
let start = std::time::Instant::now();
let elab_result = elab_program_with_source(...);
eprintln!("Elaboration took: {:?}", start.elapsed());
```

**Goal**: Determine if performance is acceptable or if we need Priority 3.

---

### Priority 3: Salsa-Integrated Elaboration (Long Term) 🔧

**If performance is an issue**, implement Option 1 from `LSP-DIAGNOSTICS-ISSUE.md`:

1. Add `?Sized` to all elaboration functions
2. Move elaboration into `file_diagnostics` Salsa query
3. Benefit from incremental type checking

**Estimated effort**: 2-3 hours  
**Performance gain**: 2-5x faster on edits

---

### Priority 4: Workspace-Level Elaboration 🏗️

**Future enhancement**: Elaborate entire workspace at once (like CLI does)

**Benefits:**
- Proper cross-file dependencies
- Shared stub table across files
- More accurate type checking

**Complexity**: High - requires architectural design

---

## Suggested Git Workflow

```bash
# 1. Commit the LSP fix
git add crates/hwml-db/src/diagnostics.rs
git add crates/hwml-lsp-server/
git add Cargo.lock
git commit -m "feat(lsp): Add type checking error reporting

The LSP server now reports both parse errors and type checking errors.
See LSP-TYPE-CHECKING-FIX.md for details."

# 2. Clean up documentation
mkdir -p wiki/implementation/lsp
git mv LSP-DIAGNOSTICS-ISSUE.md wiki/implementation/lsp/
git mv LSP-TYPE-CHECKING-FIX.md wiki/implementation/lsp/
git mv SESSION-SUMMARY-LSP-FIX.md docs/sessions/2026-05-09-lsp-diagnostics.md

# 3. Remove temp files
rm crates/hwml-elab/src/program.rs.bak
rm patch

# 4. Commit cleanup
git add -u
git add wiki/implementation/lsp/
git add docs/sessions/
git commit -m "docs: Organize LSP and provenance documentation"
```

---

## Summary

**Immediate (5-10 minutes):**
1. ✅ Commit the LSP type checking fix
2. ✅ Move documentation to proper directories
3. ✅ Remove temporary files

**Short term (1-2 hours):**
1. Test LSP in VS Code
2. Add LSP diagnostic tests
3. Profile elaboration performance

**Long term (optional):**
1. Salsa-integrated elaboration (if performance is an issue)
2. Workspace-level elaboration (for cross-file dependencies)

---

**Status**: Ready for cleanup and testing! 🚀
