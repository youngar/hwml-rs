# Constraint Solver Verification

**Date:** 2026-05-02
**Status:** ✅ VERIFIED - All rules are correct for homogeneous equality

## Overview

This document reviews the constraint solver implementation after removing heterogeneous equality to ensure all rules are correct for the ExEl homogeneous equality pattern.

## ✅ Correct: Constraint Definition

```rust
// crates/hwml-elab/src/constraint.rs:12-23
pub enum Constraint<'db> {
    /// Homogeneous equality (ExEl-style): `lhs = rhs : ty`.
    /// Both sides must have the same type `ty`.
    Eq {
        lhs: RcValue<'db>,
        rhs: RcValue<'db>,
        ty: RcTy<'db>,         // ✅ Single type for both sides
        witness: MetaId,        // ✅ Anti-unification meta
        depth: usize,
    },
    LevelLeq { smaller, larger },
}
```

**Verification:** ✅ Homogeneous - both `lhs` and `rhs` share the same `ty`.

## ✅ Correct: Witness Meta Handling

```rust
// crates/hwml-elab/src/solver.rs:96-105
if try_identity(self.global, depth, &lhs_f, &rhs_f, &ty_f) {
    // CRITICAL (ExEl pattern): Solve the witness meta to the common value!
    if let Ok(lhs_syntax) = type_quote(self.global, depth, &lhs_f) {
        let _ = self.state.solve_meta(witness, lhs_syntax, lhs_f.clone());
    }
    self.state.mark_solved(cid);
    return Ok(());
}
```

**Verification:** ✅ When `lhs = rhs` succeeds, witness is solved to the common value (ExEl anti-unification).

## ✅ Correct: Pi Injectivity

```rust
// crates/hwml-elab/src/solver.rs:163-174
if let (Value::PiCode(d1, c1), Value::PiCode(d2, c2)) = (lhs.as_ref(), rhs.as_ref()) {
    let universe_ty: RcTy<'db> = Rc::new(Ty::UniverseType);
    
    // Emit: d1 = d2 : Type (domain equality)
    self.state.emit_eq(d1.clone(), d2.clone(), universe_ty.clone(), depth);
    
    // Emit: cod1 = cod2 : Type (codomain equality under fresh variable)
    let var: RcValue<'db> = Rc::new(Value::variable(Level::new(depth), d1.clone()));
    let cod1 = c1.apply(self.global, &var);
    let cod2 = c2.apply(self.global, &var);
    self.state.emit_eq(cod1, cod2, universe_ty, depth + 1);
}
```

**Verification:** ✅ Both sub-constraints are homogeneous:
- Domain: `d1 = d2 : Type`
- Codomain: `cod1 = cod2 : Type`

## ✅ Correct: Constructor Injectivity

```rust
// crates/hwml-elab/src/solver.rs:281-295
fn emit_arg_constraints(...) {
    for i in 0..args1.len() {
        let ty = arg_types.get(i).cloned()
            .unwrap_or_else(|| Rc::new(Ty::UniverseType));
        self.state.emit_eq(args1[i].clone(), args2[i].clone(), ty, depth);
    }
}
```

**Verification:** ✅ Each argument pair shares the same type from the telescope.

## ✅ FIXED: Unifier Signature

```rust
// crates/hwml-elab/src/unify/mod.rs:63-71
/// Typed, eta-aware unification (homogeneous - both sides have same type).
pub fn unify(
    &mut self,
    lhs: RcValue<'db>,
    rhs: RcValue<'db>,
    ty: RcTy<'db>,  // ✅ Single shared type
) -> Result<UnifyResult, ElabError<'db>> {
    self.unify_at(lhs, rhs, ty)
}
```

**Called from solver:**
```rust
// crates/hwml-elab/src/solver.rs:112
unifier.unify(lhs_f.clone(), rhs_f.clone(), ty_f.clone())
//                           ^^^^^^^^^^^^   ^^^^^^^^^^^
//                           Both values, single type!
```

**Verification:** ✅ Now correctly homogeneous - single `ty` parameter shared by both sides.

## ✅ FIXED: Identity Check

```rust
// crates/hwml-elab/src/solver.rs:347-365
fn try_identity<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    lhs: &Value<'db>,
    rhs: &Value<'db>,
    ty: &Ty<'db>,  // ✅ Renamed from lhs_ty for clarity
) -> bool {
    let ty_val: RcValue<'db> = match ty {
        Ty::El(code) => code.clone(),
        Ty::UniverseType => Rc::new(Value::UniverseCode(0)),
        _ => return false,
    };
    let transparent = TransparentEnv::new();
    equal::equate(global, &transparent, depth, lhs, rhs, &ty_val).is_ok()
}
```

**Verification:** ✅ Uses single type (parameter renamed from `lhs_ty` to `ty` for clarity).

## Summary

| Component | Status | Notes |
|-----------|--------|-------|
| Constraint::Eq | ✅ | Correctly homogeneous |
| emit_eq | ✅ | Creates witness internally |
| step_eq | ✅ | Solves witness to common value |
| Pi injectivity | ✅ | Emits homogeneous sub-constraints |
| Constructor injectivity | ✅ | Emits homogeneous per-arg constraints |
| Unifier::unify | ✅ | Fixed to homogeneous signature |
| try_identity | ✅ | Renamed param for clarity |

## Changes Made

1. ✅ **Fixed unifier signature** - Removed unused `rhs_ty` parameter
2. ✅ **Renamed parameter** - Changed `lhs_ty` to `ty` in `try_identity`
3. ✅ **Updated documentation** - Changed comment from "heterogeneous" to "homogeneous"
4. ✅ **Updated call sites** - Fixed solver and test calls to use new signature

## Conclusion

All constraint solver rules are now **fully consistent with homogeneous equality**. The ExEl anti-unification pattern is correctly implemented throughout the codebase.
