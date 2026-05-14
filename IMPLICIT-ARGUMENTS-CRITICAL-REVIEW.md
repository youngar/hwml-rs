# Critical Architectural Review - Implicit Arguments Implementation

**Date:** 2026-05-13  
**Reviewer:** User (Expert in NbE and Type Theory)  
**Status:** ✅ CRITICAL ISSUES IDENTIFIED AND CORRECTED

---

## Summary

The initial implementation plan had **3 critical architectural flaws** that would have caused:
1. **Quotation failures** (implicit lambdas printing as explicit)
2. **Performance degradation** (type inference in NbE hot path)
3. **Silent bugs** (no Icit validation during application)

All issues have been identified and corrected in the updated plan.

---

## Critical Issue #1: Lambda Missing Icit Flag

### The Problem

Original plan stated:
> `// Lambda body is a Binding<RcSyntax>`  
> `// Bindings will track Icit through their usage context`  
> `// No change to Lambda struct itself`

**This is WRONG.**

### Why It's Critical

1. **Quotation Failure:**
   - When quoting `Value::Lambda` back to `Syntax`, we need to know if it's `λ {A}` or `λ A`
   - Without Icit in Lambda, all lambdas quote as explicit
   - Implicit function `λ {A}. λ x. x` would print as `λ A. λ x. x` ❌

2. **Sanity Check Impossible:**
   - During β-reduction, need to verify application Icit matches lambda Icit
   - Applying explicit arg to implicit lambda is a compiler bug
   - Without Icit in Lambda, cannot detect this ❌

3. **Pretty Printing:**
   - User sees wrong function signatures
   - Debugging becomes impossible

### The Fix

```rust
// ✅ CORRECTED: Lambda tracks its own visibility
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct Lambda<'db> {
    pub icit: Icit,  // ← MUST BE HERE
    pub body: BindingSyntax<'db>,
}

// ✅ Value domain too
#[derive(Clone, Debug)]
pub struct Lambda<'db> {
    pub icit: Icit,  // ← MUST BE HERE
    pub body: Closure<'db>,
}
```

**Impact:** ~30 lines changed across syntax.rs, val.rs, eval.rs, quote.rs

---

## Critical Issue #2: Type Inference in Evaluator

### The Problem

Original plan suggested:
```rust
Syntax::Application(app) => {
    let fun_val = eval(env, &app.function)?;
    let arg_val = eval(env, &app.argument)?;
    let arg_ty = // ... infer or annotate arg type ...  // ❌ PERFORMANCE TRAP
    let arg_normal = Normal::new(arg_ty, arg_val);
    apply(env.global, fun_val, arg_normal, app.icit)
}
```

**This is a PERFORMANCE TRAP.**

### Why It's Critical

1. **NbE is the Hot Path:**
   - Evaluator called thousands of times during unification
   - Must be computationally pure and fast
   - Type inference adds significant overhead

2. **Architecture Already Correct:**
   - For **neutrals** (Rigid/Flex): type comes from their Pi type (fast pattern match)
   - For **lambdas**: β-reduction doesn't need types (just substitute)
   - Current architecture is optimal ✅

### The Fix

```rust
// ✅ CURRENT ARCHITECTURE - KEEP IT!
fn apply_rigid(global, rigid, arg, arg_icit) -> Result {
    // Extract type from Pi (FAST - no inference!)
    let Value::PiCode(source_ty, pi_icit, target) = rigid.ty.as_ref() else {
        return Err(BadApplication);
    };
    
    // Type is already there, just use it
    let arg_normal = Normal::new(source_ty.clone(), arg.clone());
    // ...
}

fn apply_lambda(global, lambda, arg, arg_icit) -> Result {
    // Sanity check
    debug_assert_eq!(lambda.icit, arg_icit);
    
    // Just β-reduce (NO TYPE NEEDED)
    run_closure(global, &lambda.body, [arg])
}
```

**Key insight:** Don't add type inference to eval. Types come from:
- Neutrals: extract from their Pi type (already there)
- Lambdas: don't need types for β-reduction

**Impact:** No changes needed - just avoided a major mistake!

---

## Critical Issue #3: No Icit Validation

### The Problem

Original plan had no sanity checks during application.

### Why It's Critical

Applying explicit argument to implicit lambda (or vice versa) is a **catastrophic compiler bug**.
Must catch this during NbE to prevent cascading failures.

### The Fix

```rust
// ✅ SANITY CHECK in apply_lambda
pub fn apply_lambda<'db>(
    global: &GlobalEnv<'db>,
    lambda: &val::Lambda<'db>,
    arg: RcValue<'db>,
    arg_icit: Icit,  // ← Pass Icit through
) -> Result<RcValue<'db>, Error<'db>> {
    // CRITICAL: Verify Icit matches
    debug_assert_eq!(
        lambda.icit, arg_icit,
        "Compiler bug: Applied {:?} argument to {:?} lambda",
        arg_icit, lambda.icit
    );
    
    run_closure(global, &lambda.body, [arg])
}

// ✅ Similar checks in apply_rigid, apply_flex
fn apply_rigid(global, rigid, arg, arg_icit) -> Result {
    let Value::PiCode(source_ty, pi_icit, target) = rigid.ty.as_ref() else {
        return Err(BadApplication);
    };
    
    debug_assert_eq!(*pi_icit, arg_icit, "Icit mismatch in rigid application");
    // ...
}
```

**Benefits:**
- Zero runtime cost in release builds (`debug_assert`)
- Catches bugs immediately during development
- Prevents silent type system violations

---

## Corrected Implementation Plan

✅ **All corrections applied to:**
- `IMPLICIT-ARGUMENTS-IMPLEMENTATION-PLAN.md` (880 lines, complete Phase 1)

### What Changed

| Section | Original | Corrected |
|---------|----------|-----------|
| Task 1.2 | Lambda without Icit | Lambda with Icit field |
| Task 1.3 | Value Lambda without Icit | Value Lambda with Icit |
| Task 1.4 | Type inference in eval | No inference, use Pi types |
| Task 1.4 | No Icit validation | debug_assert checks |
| Task 1.5 | Quote lambda (no Icit) | Quote with preserved Icit |

---

## Next Steps

1. ✅ Review corrected plan
2. ⏭️ Begin Phase 1 implementation
3. ⏭️ Validate all 510 tests still pass
4. ⏭️ Move to Phase 2 (parser)

---

**Status:** Ready for implementation with architectural flaws corrected.
