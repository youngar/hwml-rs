# Heterogeneous Equality Mistake Analysis

## The Problem

Our elaborator has mistakenly implemented **heterogeneous equality** (tog-style `JmEq`) instead of following the **anti-unification variable** approach from ExEl (extensible-elaborator). This is a fundamental architectural mistake.

## What We Should Have Done: ExEl's Approach

### ExEl's Equality Constraint

```haskell
data EqualityConstraint e =
  EqualityConstraint Syntax.Term Syntax.Term Syntax.Type Syntax.MetaVarId
--                   ^ t1        ^ t2        ^ typ       ^ anti-unification meta
```

**Key insight**: The constraint is `t1 = t2 : typ` where **both sides have the SAME type `typ`**. This is **homogeneous equality**.

### How ExEl's Anti-Unification Works

1. When you need to check `rhs : actual_ty` against `expected_ty`:
   - Create a fresh meta `?witness : expected_ty`
   - Emit constraint: `?witness = rhs : ????`
   - **BUT WAIT**: What type do we use for the constraint?

2. The **anti-unification variable** strategy:
   - The equality constraint requires a **single type** for both sides
   - When `expected_ty` and `actual_ty` differ, we need to **first unify the types**
   - The solver will **automatically solve type metas** to make types equal
   - Only then can we emit a homogeneous equality constraint

3. The witness meta enforces **strict ordering**:
   - We can't solve `?witness` until the types unify
   - We can't proceed with elaboration until `?witness` is solved
   - This creates a **dependency chain** that enforces correct evaluation order

### ExEl's Identity Solver

```haskell
identityEqualitySolver constr = do
  let (Just (EqualityConstraint t1 t2 _ m)) = match @EqualityConstraint constr
  solveMeta m t1  -- Solve the anti-unification meta to t1!
  return True
```

**Critical**: When `t1 = t2` is definitionally equal, the solver **solves the witness meta `m` to `t1`**. This is the "anti-unification" - the witness meta gets the common value.

## What We Actually Implemented: A Confused Hybrid

### Our HetEq Constraint

```rust
pub enum Constraint<'db> {
    /// Heterogeneous equality (tog JmEq): `lhs : lhs_ty ≡ rhs : rhs_ty`.
    HetEq {
        lhs: RcValue<'db>,
        lhs_ty: RcTy<'db>,     // ← Different types!
        rhs: RcValue<'db>,
        rhs_ty: RcTy<'db>,     // ← Different types!
        witness: MetaId,       // ← This is confusing!
        depth: usize,
    },
    ...
}
```

**The mistake**: We're carrying around **two separate types** (heterogeneous) BUT also a witness meta (ExEl-style).

### Our Expect Implementation

```rust
pub fn expect(...) -> Checked<RcSyntax<'db>> {
    let (rhs_syn, actual_ty) = rhs.into_inner();

    // Create witness meta with expected_ty
    let witness_id = self.state.fresh_meta(expected_ty.clone(), depth, MetaKind::Term);
    let (t_syn, _) = self.synth_meta(witness_id)...;

    // Emit HetEq(witness : expected_ty, rhs : actual_ty)
    self.state.emit_het_eq(witness_val, expected_ty, rhs_val, actual_ty, ...);

    // Return the WITNESS META syntax (not rhs_syn!)
    Checked::new(t_syn)
}
```

**This is wrong!** We're:
1. Creating a witness meta and returning it (unlike ExEl which returns the original term)
2. Using heterogeneous equality (unlike ExEl which uses homogeneous)
3. Making the witness meta part of the constraint API (it should be internal to the constraint)

### Why Tog Needs Heterogeneous Equality

Tog implements John Major equality (JmEq) for dependent pattern matching:

```haskell
data Constraint t = JmEq SrcLoc (Ctx t) (Type t :∋ Term t) (Type t :∋ Term t)
```

They need to compare terms at different types because of their specific design goals around pattern matching and type equality proofs.

**We don't need this complexity!** ExEl shows we can avoid it entirely.

## The Consequences

1. **Unnecessary complexity**: We're implementing heterogeneous equality when we only need homogeneous equality
2. **Type reduction in constraints**: Our `step_het_eq` has to check if types are equal before proceeding
3. **Het-reduce complexity**: We emit type equality sub-constraints to unify types (see `solver.rs:170-176`)
4. **Confusion**: The comments say "ExEl-style witness" but the implementation is tog-style heterogeneous

## The Fix

We need to refactor to **true ExEl-style homogeneous equality**:

### New Constraint Design

```rust
pub enum Constraint<'db> {
    /// Homogeneous equality: `lhs = rhs : ty`
    /// The witness meta gets solved to the common value when lhs = rhs.
    Eq {
        lhs: RcValue<'db>,
        rhs: RcValue<'db>,
        ty: RcTy<'db>,          // ← Single type for both sides
        witness: MetaId,         // ← Anti-unification variable
        depth: usize,
    },
    ...
}
```

### How ExEl Actually Implements CheckType (The Real Pattern!)

Looking at ExEl's actual code:

```haskell
checkType tm ty = do
  (etm, ty') <- inferType tm      -- Infer the term, get its actual type ty'
  constrainEquality ty' ty I.Type  -- Emit: ty' = ty : Type
  return etm                       -- Return etm (which has type ty')
```

**This is the key insight!** There's **no witness meta** in `checkType` at all!

- The constraint `ty' = ty : Type` has a witness meta (created inside `constrainEquality`)
- But we don't use it! We just return `etm` which has type `ty'`
- The constraint ensures `ty' = ty`, so `etm : ty'` implies `etm : ty`

### How ExEl's ConstrainEquality Works

```haskell
constrainEquality t1 t2 ty = do
  t <- getCtx  -- Get current telescope
  m <- createMetaVar (MetaVarTag (Telescope t) ty)  -- Create witness meta
  raiseConstraint $ EqualityConstraint t1 t2 ty m   -- Emit constraint
```

The **witness meta `m`** is created, but:
1. It has type `ty` (the type at which we're comparing `t1` and `t2`)
2. When the solver determines `t1 = t2`, it solves `m := t1` (or `t2`, they're equal)
3. But the **caller doesn't use `m`** - it's just there to enforce ordering!

### New Expect Implementation (Corrected)

```rust
pub fn expect(
    &mut self,
    expected_ty: RcTy<'db>,
    rhs: Checked<(RcSyntax<'db>, RcTy<'db>)>,
) -> Checked<RcSyntax<'db>> {
    let (rhs_syn, actual_ty) = rhs.into_inner();

    // Fast path: same type
    if types_equal(&expected_ty, &actual_ty) {
        return Checked::new(rhs_syn);
    }

    // Slow path: emit type equality constraint
    // This is just: constrainEquality actual_ty expected_ty Type
    let depth = self.ctx.depth();

    // Emit homogeneous constraint: actual_ty = expected_ty : Type
    // The witness meta is created INSIDE emit_eq (not by us!)
    let actual_code = type_to_code(&actual_ty);   // El(c) -> c
    let expected_code = type_to_code(&expected_ty);
    self.state.emit_eq(
        actual_code,
        expected_code,
        Rc::new(Ty::UniverseType),  // Comparing at Type
        depth
    );

    // Return rhs_syn unchanged!
    // It has type actual_ty, but the constraint ensures actual_ty = expected_ty
    Checked::new(rhs_syn)
}
```

### New emit_eq Implementation

```rust
impl<'db> SolverState<'db> {
    pub fn emit_eq(
        &mut self,
        lhs: RcValue<'db>,
        rhs: RcValue<'db>,
        ty: RcTy<'db>,  // Single type for both sides!
        depth: usize,
    ) -> ConstraintId {
        // Create witness meta internally
        let witness_id = self.fresh_meta(ty.clone(), depth, MetaKind::Term);

        let cid = ConstraintId(self.next_constraint);
        self.next_constraint += 1;
        let constraint = Constraint::Eq { lhs, rhs, ty, witness: witness_id, depth };
        self.constraints.insert(cid, ConstraintEntry::new(cid, constraint));
        self.active_queue.push_back(cid);
        cid
    }
}
```

**Critical insights**:
1. We don't create a witness for the *term*, only for the *type equality*
2. The term `rhs_syn` is returned as-is!
3. The witness meta is an **internal implementation detail** of the constraint
4. The caller never sees or uses the witness meta directly

### New Solver Logic

```rust
fn step_eq(
    &mut self,
    cid: ConstraintId,
    lhs: RcValue<'db>,
    rhs: RcValue<'db>,
    ty: RcTy<'db>,  // ← Single type!
    witness: MetaId,
    depth: usize,
) -> Result<(), SolveError<'db>> {
    // Force both sides
    let lhs_f = force_deep(self.state, self.global, lhs);
    let rhs_f = force_deep(self.state, self.global, rhs);
    
    // Try definitional equality
    if def_equal(&lhs_f, &rhs_f, &ty) {
        // SOLVE THE WITNESS META to lhs_f (or rhs_f, they're equal)
        self.state.solve_meta(witness, lhs_f_syntax, lhs_f);
        self.state.mark_solved(cid);
        return Ok(());
    }
    
    // Try unification (pattern unification, etc.)
    // ...
    
    // If we make progress, solve the witness accordingly
}
```

## Wait, But What About Anti-Unification Variables for Terms?

You might ask: "In `expect`, don't we need a witness meta for the **term** to enforce evaluation order?"

**NO!** Here's why:

### The ExEl Strategy

When we do `checkType tm expected_ty`:

1. We synthesize `(tm_elab, actual_ty) ← inferType tm`
2. We emit constraint: `actual_ty = expected_ty : Type`  (with internal witness meta)
3. We return `tm_elab` **unchanged**

**The term `tm_elab` itself doesn't need a witness!** Why?

- `tm_elab` has type `actual_ty`
- The constraint ensures `actual_ty = expected_ty`
- By substitution, `tm_elab : expected_ty`
- The witness meta inside the constraint enforces that we can't use this equality until it's solved

### When DO We Need Witness Metas for Terms?

Actually, **we might not need them at all in the ExEl approach!** The original description of "anti-unification variables for terms" might have been misleading.

Let me re-read the user's description:

> "The anti unification variables are metavariables that are solved automatically when an equality constraint is solved. For example, `?t <- A = B : Type; ?u <- a = b : ?t` where `?t` is an antiunificaiton variable."

OK so in this example:
- `?t` is the witness meta for `A = B : Type`
- `?u` is the witness meta for `a = b : ?t`

When the first constraint is solved (A and B unify to some common value C), the witness `?t` gets solved to `C`.
Then the second constraint can proceed: `a = b : C`.

**But the second constraint also has its own witness meta `?u`!** When `a = b` at type `C`, the witness `?u` gets solved to `a` (or `b`, they're equal).

So the anti-unification variables **are just the witness metas in the equality constraints**. There's no separate "witness meta for terms" that we return from `expect` or `checkType`.

### Implications for Our Implementation

We should:
1. **Never return witness metas from `expect` or `checkType`**
2. **Only create witness metas internally in `emit_eq`**
3. **Always return the original term**, trusting that the constraint enforces type equality

## Action Items

1. ✅ Analyze the codebase and identify the mistake
2. ⬜ Refactor `Constraint` enum to remove heterogeneous equality
3. ⬜ Refactor `expect` to NOT create or return witness metas
4. ⬜ Move witness meta creation into `emit_eq` (make it internal)
5. ⬜ Refactor solver to solve witness metas correctly
6. ⬜ Remove all het-reduce and type-equality-in-constraint logic
7. ⬜ Update tests to match new design
8. ⬜ Verify against ExEl's approach

## References

- `external/extensible-elaborator/exel/src/TypeCheck/Constraints.hs` - ExEl's constraint definition
- `external/extensible-elaborator/exel/src/TypeCheck/ConstraintsActions.hs` - How to emit constraints
- `external/extensible-elaborator/exel/src/TypeCheck/Solver/Identity.hs` - How witness metas are solved
- `external/togt/` - Tog's heterogeneous equality (what we DON'T want)
