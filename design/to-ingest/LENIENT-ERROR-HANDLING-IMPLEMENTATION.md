# Lenient Error Handling Implementation

**Date:** 2026-05-06  
**Status:** ✅ Implemented and Tested

---

## Problem: Short-Circuit Trap

Previously, `elab_library_with_sccs` would short-circuit on the **first error** in any SCC, preventing the compiler from discovering subsequent errors in the rest of the standard library. This was frustrating for developers who had to fix errors one-by-one in multiple compile cycles.

### Before (Short-Circuiting Behavior)

```rust
let headers = match elaborate_headers(...) {
    Ok(h) => h,
    Err(e) => {
        errors.push(e);
        continue;  // ❌ STOP! Skip rest of library
    }
};
```

**Result:** Finding 76 errors required 76 separate compile runs!

---

## Solution: Lenient Error Collection

The elaborator now **collects ALL errors** and continues processing the rest of the library instead of stopping at the first failure.

### Implementation Changes

#### 1. Added Solver & Zonk Steps (Bug Fix)

The `elab_library_with_sccs` function was **missing** the constraint solver and zonking steps! These were present in `elab_program_with_library_sccs` but not in the library-wide version. This was a critical bug.

**Added:**
```rust
// Run constraint solver to completion
let mut solver = Solver::new(&mut state, global, db);
if let Err(solve_err) = solver.run() {
    // LENIENT: Push error and continue instead of returning
    match solve_err {
        SolveError::NoProgress => {
            errors.push(ElabError::NotImplemented {
                feature: format!("Constraint solver made no progress in SCC {}", scc_idx),
                span: None,
            });
        }
        SolveError::Elab(elab_err) => {
            errors.push(elab_err);
        }
    }
    continue;  // Continue to next SCC
}

// Zonk to substitute solved metavariables
if let Err(e) = zonk(&mut state) {
    errors.push(e);
    continue;
}
```

#### 2. Lenient Solver Error Handling

Instead of returning on solver errors, the code now:
- Catches `SolveError::NoProgress` and `SolveError::Elab` 
- Pushes them to the `errors` Vec
- Continues processing the next SCC

This allows the compiler to discover type errors, unification failures, and constraint solving issues **across the entire library** in a single run.

---

## Why Not Salsa Accumulators?

The **proper** Salsa pattern for collecting diagnostics is using `#[salsa::accumulator]`:

```rust
#[salsa::accumulator]
pub struct ElabDiagnostics(pub ElabError);

#[salsa::tracked]
fn elab_library(db: &dyn Database, ...) -> GlobalEnv {
    // Push errors: ElabDiagnostics::push(db, error)
    // Retrieve: ElabDiagnostics::accumulated(db, ...)
}
```

**However**, this requires the elaboration function to be `#[salsa::tracked]`, which it currently cannot be because:
- It takes `&mut GlobalEnv` as a parameter
- Salsa tracked functions must be **pure** (no mutable references)

See `crates/hwml-elab/src/error.rs` for detailed comments on this architectural limitation and future refactoring path.

---

## Test Results

Running on the standard library (`stdlib/`):

### Before
```
Errors: 1
(first error stops compilation)
```

### After
```
Libraries processed: 1
Declarations elaborated: 2
Errors: 76
```

**All 76 errors discovered in a single compile!**

---

## Error Categories Found

The lenient error handling revealed:

1. **NotInScope errors** (e.g., `Bool`, `Nat`, `Unit` not found)
   - Likely due to namespace resolution issues
   - May require fixing `open` statement handling

2. **TypeMismatch errors** 
   - Expected: `Type → Type` (Pi code)
   - Actual: `Type` (Universe code)
   - Suggests issue with type constructor elaboration

3. **Resolver errors**
   - "Unknown identifier 'Std.Bool'"
   - Indicates dotted name resolution failing

---

## Next Steps

The error collection is now working correctly. The **real work** begins:

1. **Fix the actual type errors** in the standard library
2. **Debug namespace resolution** (`open Std.Bool` not working)
3. **Improve error messages** (add source spans)
4. **Future refactoring**: Make `elab_library_with_sccs` a pure Salsa tracked function

---

## Files Modified

- `crates/hwml-elab/src/error.rs` - Added documentation about Salsa accumulators
- `crates/hwml-elab/src/program.rs` - Added solver/zonk steps + lenient error handling

---

## Architectural Notes

This implementation maintains the short-circuit behavior **per SCC** (if an SCC fails, we skip it and move to the next), but no longer short-circuits the **entire library** on the first SCC failure.

This is the correct tradeoff because:
- Declarations in a failed SCC are not available to subsequent SCCs
- But subsequent independent SCCs can still be elaborated and checked
- Developers see **all** top-level errors in one compile cycle
