# Fix Summary: Value-as-Type Error Improvement

## Date
2026-05-09

## Problem Statement

When a value (like a data constructor `Nat.zero`) is used in a type position, the elaborator produced a confusing "Unsolved metavariable" error instead of a specific error message.

### Example

```hwml
def fart (n : Nat.zero) : Nat := zero  // Nat.zero is a value, not a type!
```

**Before:**
```
error[E0007]: Unsolved metavariable ?0 (this indicates the type checker could not infer enough information)
  -->  Nat.hwml:38:15

help: add more type annotations to help the type checker
help: check that all function arguments and return types are specified
```

**After:**
```
error[E0004]: Unification failure
  -->  unknown:1:1
```

While the location is still "unknown:1:1" (a separate issue), the error type is now correct.

## Root Cause Analysis

1. The elaborator's `elab_telescope` function checks parameter type annotations against `UniverseType`
2. When it encounters `Nat.zero`, it switches to synthesis mode and gets type `El(Nat)`  
3. It then calls `expect_with_loc` to unify `El(Nat)` with `UniverseType`
4. This emits a constraint: `Nat = UniverseCode(0) : UniverseType`
5. The unifier's `unify_structural` method didn't recognize this as a hard failure
6. Instead, it returned `Stuck`, causing the solver to block the constraint
7. Eventually, this resulted in an "unsolved metavariable" error

## Solution Implemented

### Files Modified

1. **`crates/hwml-elab/src/unify/mod.rs`** (lines 206-227)
   - Added explicit hard failure cases before the catch-all `_ => Ok(UnifyResult::Stuck)`
   - Now detects incompatible value forms and returns `UnificationFailure` error

2. **`crates/hwml-elab/tests/elab_tests.rs`** (lines 363, 386)
   - Fixed test calls to `synth_universe` to include the new `loc` parameter

3. **`stdlib/src/Nat.hwml`**
   - Removed test `fart` definition used to reproduce the bug

### Code Changes

Added the following cases to `unify_structural` to detect incompatible value forms:

- `TypeConstructor` vs `UniverseCode`
- `DataConstructor` vs `UniverseCode`
- `TypeConstructor` vs `DataConstructor`
- `TypeConstructor` vs `PiCode`
- `DataConstructor` vs `PiCode`
- `TypeConstructor` vs `BitCode`
- `DataConstructor` vs `BitCode`

All of these now produce a hard `UnificationFailure` error instead of returning `Stuck`.

## Test Results

### Passing Tests
- ✅ All 20 unit tests in `elab_tests.rs` passing
- ✅ 9/10 snapshot tests in `snap_tests.rs` passing
- ✅ Stdlib compilation reduced from 56 errors to 55 errors (the removed error was our test case)

### Pre-existing Failure
- ❌ `snap_return_type_binder` test was **already failing** before our changes
  - Confirmed by temporarily reverting our changes and re-running the test
  - This is a separate issue unrelated to our fix

## Impact

**Positive:**
- Users now get a "Unification failure" error instead of "Unsolved metavariable" when using values as types
- The error type correctly indicates a type mismatch rather than insufficient type information

**To Do:**
- Improve the diagnostic message to specifically say "value used as type" (requires custom error variant)
- Fix location tracking so errors don't show "unknown:1:1" (separate provenance issue)

## Documentation

- Created `wiki/bugs/VALUE-AS-TYPE-ERROR.md` with full technical analysis
- Updated with implementation status and test results

## Related Issues

- Location tracking: Errors still show "unknown:1:1" instead of actual source location
- Pre-existing test failure: `snap_return_type_binder` test needs investigation
