# ✅ Implicit Arguments Research Complete

## Decision
✅ **Use Dynamic Order Elaboration (DOE)**

## Why DOE?
- ✅ Simplest solution (~150 LOC)
- ✅ No core syntax changes
- ✅ Single-pass traversal
- ✅ Stronger than Quick Look
- ✅ Production-proven (sixty language)

## What Changes?
1. **Add Icit enum** to track Explicit vs Implicit
2. **Update AST nodes**: PiCode, Lambda, Application
3. **Update Value domain**: Spines store Icit
4. **Add postponing**: Check delayed when type is meta-headed
5. **Placeholder metas**: Represent postponed results

## Hardware Impact?
✅ **ZERO** - implicit args erased during lowering!

## Implementation Timeline
- **Week 1:** Icit infrastructure
- **Week 2:** Basic insertion (known types)  
- **Week 3-4:** DOE postponing
- **Week 5:** Testing with elaboration-zoo examples

## Your Questions Answered

### 1. AST Structure?
- Uses `Rc<Syntax<'db>>` (reference counting)
- Adding Icit = just another field
- **Trivial change**

### 2. Spine Representation?
```rust
pub struct Spine<'db>(pub Vec<Eliminator<'db>>);
pub struct Application<'db> {
    pub argument: Normal<'db>,
    pub icit: Icit,  // ← ADD THIS
}
```

### 3. Metavariable State?
- Uses `HashMap<MetaId, MetaEntry>`
- Pattern unification exists
- **Recommend strict Icit matching** in unification

### 4. Hardware Backend?
- ✅ **All implicit args erased** during lowering
- ✅ CIRCT sees only saturated applications
- ✅ **Zero backend changes needed**

## DOE Algorithm (30-second version)

```rust
fn check(term, ty) {
    match ty.head() {
        PiCode(_, Implicit, _) => insert_lambda(),
        PiCode(_, Explicit, _) => check_explicit(),
        Flex(meta, _) => POSTPONE(term, ty, meta),  // ← Key insight!
    }
}

fn solve_meta(meta) {
    // Solve meta
    // Retry all postponed checks blocked on meta
}

fn finish_file() {
    // Process remaining postponed checks
    // Assume explicit (no insertion)
}
```

## Example

**Input:**
```
let foo : Maybe ({A} → A → A) = Just (λ x. x)
```

**Without DOE:** ❌ Error - `Maybe (?1 → ?1)` ≠ `Maybe ({A} → A → A)`

**With DOE:** ✅ Elaborate to:
```
Just {{A : U} → A → A} (λ {A : U} (x : A). x)
```

## Documentation
📖 **Full research:** `wiki/research/implicit-arguments-first-class-polymorphism.md`
📋 **Summary:** `IMPLICIT-ARGUMENTS-RESEARCH-SUMMARY.md`
🔗 **Source:** [elaboration-zoo/06-first-class-poly](https://github.com/AndrasKovacs/elaboration-zoo/tree/master/06-first-class-poly)

## Next Steps
1. ✅ Research complete (this document)
2. ⏭️ Create ADR for DOE decision
3. ⏭️ Begin Phase 1 implementation (Icit infrastructure)
