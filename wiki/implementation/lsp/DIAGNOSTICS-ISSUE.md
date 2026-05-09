# LSP Diagnostics Issue: Type Checking Errors Not Shown

**Date**: 2026-05-09  
**Status**: ⚠️ Partially Fixed

---

## Problem

The HWML LSP server is **only reporting parsing errors**, not type checking (elaboration) errors.

Users see:
- ✅ **Parse errors** (syntax mistakes)
- ❌ **Type checking errors** (type mismatches, unification failures, etc.)

---

## Root Cause

The `file_diagnostics` Salsa query (in `crates/hwml-db/src/diagnostics.rs`) currently:
1. ✅ Collects parse errors from `parse_surface_program_with_errors`
2. ❌ **Skips elaboration errors** due to architectural limitations

### Architectural Issue

**Problem**: Elaboration functions require concrete database types (`&HwmlDatabase`), but Salsa queries only provide trait objects (`&dyn salsa::Database`).

**Current signatures**:
```rust
// ❌ Doesn't work with `&dyn salsa::Database`
pub fn elab_program_with_source<'db, Db>(
    db: &'db Db,
    global: &mut GlobalEnv<'db>,
    program: &Program,
    source: Option<Source<'db>>,
) -> ElabProgramResult<'db>
where
    Db: salsa::Database,  // ❌ Requires Sized (concrete type)
{...}
```

**Inside Salsa query**:
```rust
#[salsa::tracked]
pub fn file_diagnostics(db: &dyn salsa::Database, source: SourceFile) -> Arc<Vec<Diagnostic>> {
    // ❌ Can't call elab_program_with_source because db is &dyn salsa::Database (not Sized)
}
```

---

## Why It Fails

Rust requires type parameters to be `Sized` by default. When we try to call:
```rust
elab_program_with_source(db, &mut global, program, Some(source))
```

We get:
```
error[E0277]: the size for values of type `dyn Database` cannot be known at compilation time
```

To fix this, we'd need to add `?Sized` to `Db` in all elaboration functions:
```rust
where
    Db: salsa::Database + ?Sized,
```

But this would require changes to **~50+ functions** across:
- `crates/hwml-elab/src/program.rs` (~12 functions)
- `crates/hwml-elab/src/elab/decl.rs`
- `crates/hwml-elab/src/elab/expr.rs`
- `crates/hwml-elab/src/kernel/mod.rs`
- Helper functions throughout the elaboration codebase

---

## Current Workaround

**In `crates/hwml-db/src/diagnostics.rs:195-204`**:
```rust
// TODO: Collect elaboration errors (type checking errors)
// The elaboration system currently requires concrete database types (&HwmlDatabase)
// but Salsa queries only provide &dyn salsa::Database. This needs architectural work.
// For now, elaboration errors are only available via the CLI, not LSP.
```

**Impact**:
- ✅ LSP shows **parse errors**
- ❌ LSP does **not** show **type checking errors**
- ✅ CLI (`cargo run -- --file ...`) **does** show both parse and type checking errors

---

## Solution Options

### Option 1: Add `?Sized` Bounds (Recommended, High Effort)

**Changes**:
1. Add `?Sized` to all elaboration function `where` clauses
2. Estimated ~50-100 functions across 5-10 files
3. Run elaboration inside `file_diagnostics` Salsa query

**Pros**:
- ✅ Clean architectural solution
- ✅ Enables incremental type checking via Salsa
- ✅ LSP gets full diagnostics

**Cons**:
- ⚠️ Large refactor (~2-3 hours)
- ⚠️ Touches many files, potential for errors

**Implementation**:
```bash
# Automated first pass
sed -i 's/Db: salsa::Database,$/Db: salsa::Database + ?Sized,/g' crates/hwml-elab/src/*.rs
sed -i 's/Db: salsa::Database,$/Db: salsa::Database + ?Sized,/g' crates/hwml-elab/src/elab/*.rs

# Then fix any helper functions manually
cargo build  # Fix errors iteratively
```

---

### Option 2: Separate Elaboration Query (Quick Fix)

**Changes**:
1. Create a new function `elab_program_for_diagnostics` that accepts `&HwmlDatabase` directly
2. Call it from LSP server's `compile_file` method instead of from the Salsa query

**Pros**:
- ✅ Quick to implement (~30 minutes)
- ✅ Minimal changes

**Cons**:
- ❌ Bypasses Salsa caching for elaboration
- ❌ Less incremental - re-elaborates entire files
- ❌ Duplicates some logic between CLI and LSP

**Implementation**:
```rust
// In crates/hwml-lsp-server/src/main.rs:299
fn compile_file(&self, db: &HwmlDatabase, uri: &Uri, file: hwml_db::db::SourceFile) {
    let diagnostics = hwml_db::diagnostics::file_diagnostics(db, file);  // Parse errors only
    
    // Add elaboration errors separately
    if let Some(program) = parse_result.program {
        let mut global = hwml_core::val::GlobalEnv::new();
        let elab_result = hwml_elab::program::elab_program_with_source(db, &mut global, &program, Some(source));
        
        for elab_error in &elab_result.errors {
            // Convert to LSP diagnostics
        }
    }
    
    self.send_diagnostics(uri.clone(), lsp_diagnostics);
}
```

---

### Option 3: Workspace-Level Elaboration (Future)

**Changes**:
1. Elaborate entire workspace at once (like CLI does)
2. Distribute errors back to individual files

**Pros**:
- ✅ Handles cross-file dependencies properly
- ✅ Matches CLI behavior exactly

**Cons**:
- ⚠️ Requires significant architectural design
- ⚠️ May be slower for large workspaces

---

## Recommendation

**Short term (now)**: Implement **Option 2** to unblock users  
**Medium term (next week)**: Refactor to **Option 1** for proper Salsa integration

---

## Test Case

Create `test-error.hwml`:
```hwml
def foo : Bit := 42
```

**Expected**:
- Parse error: ❌ (none - parses fine)
- Type error: `Type mismatch: expected Bit, found Nat`

**Actual (LSP)**:
- No errors shown ❌

**Actual (CLI)**:
- Type error shown ✅

---

**Next Steps**: Implement Option 2 to fix LSP diagnostics immediately.
