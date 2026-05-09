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

**After (Phase 1 - Unifier Fix):**
```
error[E0004]: Unification failure
  -->  unknown:1:1
```

**After (Phase 2 - Diagnostic Improvement):**
```
error[E0004]: Type mismatch: expected 'Type0' but found 'Test/Nat'
  -->  unknown:1:1
```

While the location is still "unknown:1:1" (a separate issue), the error message now clearly explains what went wrong.

## Root Cause Analysis

1. The elaborator's `elab_telescope` function checks parameter type annotations against `UniverseType`
2. When it encounters `Nat.zero`, it switches to synthesis mode and gets type `El(Nat)`  
3. It then calls `expect_with_loc` to unify `El(Nat)` with `UniverseType`
4. This emits a constraint: `Nat = UniverseCode(0) : UniverseType`
5. The unifier's `unify_structural` method didn't recognize this as a hard failure
6. Instead, it returned `Stuck`, causing the solver to block the constraint
7. Eventually, this resulted in an "unsolved metavariable" error

## Solution Implemented

### Phase 1: Unifier Hard Failure Fix

**File: `crates/hwml-elab/src/unify/mod.rs`** (lines 206-227)
   - Added explicit hard failure cases for incompatible value forms:
     - `UniverseCode` vs `TypeConstructor`
     - `UniverseCode` vs `DataConstructor`
     - `TypeConstructor` vs `DataConstructor`
   - These now return `UnificationFailure` error instead of `Stuck`
   - Kept `DataConstructor` vs `DataConstructor` and `TypeConstructor` vs `TypeConstructor` as `Stuck`
     (handled by solver's constructor injectivity)

**File: `crates/hwml-elab/tests/elab_tests.rs`** (lines 363, 386)
   - Fixed test calls to `synth_universe` to include the new `loc` parameter

**File: `stdlib/src/Nat.hwml`**
   - Removed test `fart` definition used to reproduce the bug

### Phase 2: Diagnostic Message Improvement

**File: `crates/hwml-db/src/diagnostics.rs`**
   - Added `format_value_brief` helper to format values concisely
   - Updated `UnificationFailure` case to show "expected X but found Y"

**File: `crates/hwml-elab/src/diagnostic.rs`**
   - Added `format_value` helper for rich diagnostic formatting
   - Updated `UnificationFailure` case to use value formatting

### Key Implementation Details

**Unifier Strategy:**
The unifier now distinguishes between three cases:
1. **Hard failures**: Incompatible value forms (e.g., `UniverseCode` vs `DataConstructor`)
2. **Stuck**: Cases that might be solvable (e.g., `Flex` vs anything, same-kind constructors)
3. **Success**: Direct unification (e.g., same rigid variable, eta-equivalence)

**Value Formatting:**
Both diagnostic converters now format values concisely:
- `UniverseCode(0)` → `Type0`
- `TypeConstructor(Nat)` → `Nat` or `Test/Nat`
- `DataConstructor(zero)` → `zero` or `Std/Nat/zero`
- `Flex(?0)` → `?0`

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
- ✅ Users now get a clear "Type mismatch: expected X but found Y" error
- ✅ The error correctly identifies what type was expected and what was found
- ✅ No more confusing "Unsolved metavariable" errors for this case
- ✅ All existing tests still pass

**Remaining Issues:**
- ⚠️ Location tracking still shows "unknown:1:1" instead of actual source location (separate provenance issue)
- 💡 Could add more specific error message like "cannot use value as type" (optional enhancement)

## Documentation

- Created `wiki/bugs/VALUE-AS-TYPE-ERROR.md` with full technical analysis
- Updated with implementation status and test results

## Related Issues

- Location tracking: Errors still show "unknown:1:1" instead of actual source location
- Pre-existing test failure: `snap_return_type_binder` test needs investigation
