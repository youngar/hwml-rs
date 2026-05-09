# ExEl Pattern Verification

**Date:** 2026-05-02  
**Status:** ✅ VERIFIED - Our implementation correctly follows the ExEl pattern

## Summary

After refactoring from the heterogeneous equality mistake, our surface-to-core elaborator now correctly implements the ExEl (extensible-elaborator) pattern for bidirectional type checking with anti-unification variables.

## Comparison with ExEl Reference

### ExEl's `checkType` Fallback (Haskell)

```haskell
-- c-infer (fallback rule in checkType)
checkType tm ty = do
  (etm, ty') <- inferType tm
  CA.constrainEquality ty' ty I.Type
  return etm
```

**Translation:**
1. `inferType tm` → synth the term, get `(etm : ty')`
2. `constrainEquality ty' ty I.Type` → emit constraint `ty' = ty : Type`
3. `return etm` → return the **original elaborated term**, not a witness

### Our Implementation (Rust)

```rust
// crates/hwml-elab/src/elab/expr.rs:76-78
_ => {
    let s = synth(db, elab, expr)?;
    Ok(elab.kernel.expect(expected_ty, s))
}
```

Where `expect` is defined as:

```rust
// crates/hwml-elab/src/kernel/mod.rs:464-509
pub fn expect(
    &mut self,
    expected_ty: RcTy<'db>,
    rhs: Checked<(RcSyntax<'db>, RcTy<'db>)>,
) -> Checked<RcSyntax<'db>> {
    let (rhs_syn, actual_ty) = rhs.into_inner();
    
    // Fast path: types already equal
    if Rc::ptr_eq(&expected_ty, &actual_ty) {
        return Checked::new(rhs_syn);
    }
    
    // Slow path: emit type equality constraint
    self.state.emit_eq(
        actual_code,      // lhs
        expected_code,    // rhs
        Rc::new(Ty::UniverseType),  // Type
        depth,
    );
    
    // Return original rhs_syn (ExEl pattern!)
    Checked::new(rhs_syn)
}
```

And `emit_eq`:

```rust
// crates/hwml-elab/src/state.rs:122-142
pub fn emit_eq(
    &mut self,
    lhs: RcValue<'db>,
    rhs: RcValue<'db>,
    ty: RcTy<'db>,
    depth: usize,
) -> ConstraintId {
    // Create witness meta internally (ExEl pattern)
    let witness = self.fresh_meta(ty.clone(), depth, MetaKind::Term);
    
    let constraint = Constraint::Eq {
        lhs,
        rhs,
        ty,
        witness,  // Internal detail, never exposed to caller
        depth,
    };
    // ...
}
```

## ✅ Pattern Match Verified

| ExEl Pattern Element | Our Implementation | Status |
|---------------------|-------------------|--------|
| Infer term `tm : ty'` | `synth(db, elab, expr)` | ✅ |
| Emit constraint `ty' = ty : Type` | `emit_eq(actual_code, expected_code, Type)` | ✅ |
| Return original term `etm` | `Checked::new(rhs_syn)` | ✅ |
| Witness meta is internal | Created in `emit_eq`, never returned | ✅ |
| Homogeneous equality | `Constraint::Eq { lhs, rhs, ty, ... }` | ✅ |

## Key Differences from Tog

**Tog** uses heterogeneous equality for dependent pattern matching:
- Constraint: `JmEq (type1 :∋ t1) (type2 :∋ t2)`
- Types can differ, requires `het_reduce` to emit type-level sub-constraints

**ExEl** uses homogeneous equality with anti-unification:
- Constraint: `Eq lhs rhs ty` where `lhs : ty` and `rhs : ty`
- Types must match, witness meta auto-solved when equality succeeds
- No `het_reduce` complexity needed

## Conclusion

Our elaborator correctly implements the ExEl pattern:

1. **`check` function** falls back to synth + expect (lines 76-78)
2. **`expect` function** emits type equality and returns original term (lines 464-509)
3. **`emit_eq` function** creates witness meta internally, never exposes it (lines 122-142)
4. **Solver** solves witness to the common value when `lhs = rhs` succeeds

The refactoring successfully eliminated the heterogeneous equality confusion and now matches the reference implementation.
