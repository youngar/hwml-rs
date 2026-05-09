# Bug: Confusing "Unsolved Metavariable" Error When Value Used as Type

## Summary

When a value (like a data constructor) is used in a type position, the elaborator produces a confusing "Unsolved metavariable" error instead of a clear message like "Expected a type, but `Nat.zero` is a value with type `Nat`".

## Example

```hwml
def fart (n : Nat.zero) : Nat := zero
```

**Current error:**
```
error[E0007]: Unsolved metavariable ?0 (this indicates the type checker could not infer enough information)
  -->  Nat.hwml:38:15
```

**Expected error:**
```
error: Expected a type, but `Nat.zero` is a data constructor with type `Nat`
  -->  Nat.hwml:38:15
   |
38 | def fart (n : Nat.zero) : Nat := zero
   |               ^^^^^^^^ this is a value, not a type
```

## Root Cause

### Elaboration Flow

1. **`elab_telescope`** (in `crates/hwml-elab/src/elab/decl.rs:451`):
   - Checks parameter type annotation against `UniverseType`
   - Calls: `check(db, &mut inner, &group.ty, Rc::new(Ty::UniverseType))`

2. **`check_impl`** (in `crates/hwml-elab/src/elab/expr.rs:449-463`):
   - Expression doesn't match expected type's form
   - **Switches to synthesis mode** (the "switch rule")
   - Synthesizes type of `Nat.zero` → gets `El(Nat)` (data constructor has type `Nat`)
   - Calls `expect_with_loc(UniverseType, (syn, El(Nat)), loc)`

3. **`expect_with_loc`** (in `crates/hwml-elab/src/kernel/mod.rs:539-580`):
   - Extracts type codes:
     - `expected_code` = `UniverseCode(0)` (from `UniverseType`)
     - `actual_code` = `Nat` (a `TypeConstructor` value)
   - Emits constraint: `Nat = UniverseCode(0) : UniverseType` (line 575)

4. **Solver `step_eq`** (in `crates/hwml-elab/src/solver.rs:102-171`):
   - Identity check fails (line 117)
   - Calls unifier (line 131)
   - Unifier returns `Stuck` (see next step)
   - Pi/constructor injectivity don't apply
   - **Blocks constraint** on metas (line 168) instead of failing

5. **`unify_structural`** (in `crates/hwml-elab/src/unify/mod.rs:113-208`):
   - Tries to unify `Nat` (TypeConstructor) with `UniverseCode(0)`
   - Doesn't match any explicit cases (lines 163-205)
   - Hits catch-all: `_ => Ok(UnifyResult::Stuck)` (line 206)
   - **Should error here instead!**

### The Problem

The unifier's catch-all case (line 206) returns `Stuck` for **any** unhandled value forms, even when they're fundamentally incompatible (like `TypeConstructor` vs `UniverseCode`).

## Proposed Fix

### Option 1: Improve Unifier (Recommended)

Add explicit cases in `unify_structural` to detect "hard" mismatches:

```rust
// In crates/hwml-elab/src/unify/mod.rs, around line 206

// Before catch-all, add:
(Value::TypeConstructor(_), Value::UniverseCode(_)) |
(Value::UniverseCode(_), Value::TypeConstructor(_)) => {
    Err(ElabError::UnificationFailure {
        lhs: lhs.clone(),
        rhs: rhs.clone(),
        span: None,
        elab_backtrace: Vec::new(),
    })
}

(Value::DataConstructor(_), Value::UniverseCode(_)) |
(Value::UniverseCode(_), Value::DataConstructor(_)) => {
    Err(ElabError::UnificationFailure {
        lhs: lhs.clone(),
        rhs: rhs.clone(),
        span: None,
        elab_backtrace: Vec::new(),
    })
}

_ => Ok(UnifyResult::Stuck),
```

### Option 2: Improve Error Message Conversion

Add a new `ElabError` variant specifically for "value used as type":

```rust
pub enum ElabError<'db> {
    // ... existing variants
    ValueUsedAsType {
        elab_backtrace: Vec<ElabFrame<'db>>,
        value: RcValue<'db>,
        value_type: RcTy<'db>,
        span: Option<SourceRange<'db>>,
    },
}
```

Then detect this case in `expect_with_loc` before emitting the constraint.

### Option 3: Combination (Best UX)

1. Fix the unifier to fail hard on incompatible forms
2. Add custom diagnostic conversion to detect `TypeConstructor/DataConstructor = UniverseCode` failures
3. Produce a narrative error message explaining the mistake

## Implementation Priority

**High** - This is a common beginner mistake and the current error message provides no actionable guidance.

## Implementation Status

✅ **IMPLEMENTED** - Option 1 (Improve Unifier)

### Changes Made

1. **File**: `crates/hwml-elab/src/unify/mod.rs` (lines 206-227)
   - Added explicit hard failure cases before the catch-all `_ => Ok(UnifyResult::Stuck)`
   - Now detects incompatible value forms and returns `UnificationFailure` error
   - Covers these incompatible combinations:
     - `TypeConstructor` vs `UniverseCode`
     - `DataConstructor` vs `UniverseCode`
     - `TypeConstructor` vs `DataConstructor`
     - `TypeConstructor` vs `PiCode`
     - `DataConstructor` vs `PiCode`
     - `TypeConstructor` vs `BitCode`
     - `DataConstructor` vs `BitCode`

### Result

**Before:**
```
error[E0007]: Unsolved metavariable ?0
  -->  Nat.hwml:38:15
```

**After:**
```
error[E0004]: Unification failure
  -->  unknown:1:1
```

While still at "unknown:1:1" (a separate location tracking issue), the error type is now correct. Future work should improve the diagnostic message to specifically mention "value used as type".

## Related Files

- `crates/hwml-elab/src/elab/decl.rs` (telescope elaboration)
- `crates/hwml-elab/src/elab/expr.rs` (switch rule)
- `crates/hwml-elab/src/kernel/mod.rs` (`expect_with_loc`)
- `crates/hwml-elab/src/solver.rs` (constraint solving)
- `crates/hwml-elab/src/unify/mod.rs` (unification logic) ← **Fixed here**
- `crates/hwml-elab/src/error.rs` (error types)
- `crates/hwml-db/src/diagnostics.rs` (error message formatting)
