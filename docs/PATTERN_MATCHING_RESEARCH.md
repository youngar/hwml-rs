# Pattern Matching in Dependent Type Theory

## Executive Summary

Pattern matching in dependent type systems is fundamentally different from ML-style pattern matching because:

1. **The type of the scrutinee constrains which patterns are possible**
2. **Pattern matching refines type information** (type dependencies flow from scrutinee to branches)
3. **Exhaustiveness checking requires unification**, not just constructor enumeration
4. **Type annotations are sometimes required** when the return type depends on the scrutinee

## Core Concepts

### 1. Eliminators and Motives

**Key Paper**: "Elimination with a Motive" (McBride, 2002)

In dependent type theory, pattern matching is compiled to **eliminators** (like `nat_elim`, `vec_elim`). An eliminator has:

- **Motive (return clause)**: A function describing the result type for each possible pattern
  - Type: `(x : T) → Type` where `x` is the scrutinee
  - Example for `Vec A n`: `(n : Nat) → (v : Vec A n) → Type`
  
- **Methods**: One for each constructor, showing how to compute the result for that constructor
  
**Example** (Agda-style):
```agda
-- Simple case (non-dependent)
isZero : Nat → Bool
isZero zero    = true
isZero (succ n) = false

-- Compiles to:
nat_elim (λ n → Bool)    -- motive
         true            -- zero case
         (λ n rec → false)  -- succ case
```

### 2. Dependent Pattern Matching

**Key Papers**: 
- Coquand "Pattern Matching with Dependent Types" (1992)
- Goguen, McBride, McKinna "Eliminating Dependent Pattern Matching" (2006)
- Cockx et al. "Unifiers as Equivalences" (2016)

When the return type **depends on the scrutinee**, we need dependent elimination:

```agda
-- Return type depends on n!
head : {A : Type} → {n : Nat} → Vec A (succ n) → A
head (vcons x xs) = x

-- The type signature says: we only match vectors with length (succ n)
-- So the only possible pattern is vcons (which produces succ n)
```

**Motive**: `(n : Nat) → Vec A (succ n) → A`

The pattern `vcons` refines `n` to some `m` such that `succ m = succ n`, thus `m = n`.

### 3. Unification in Pattern Matching

**Key Insight**: Coverage checking requires unifying constructor indices with scrutinee indices.

#### Algorithm (from Agda/Cockx 2016):

For each data constructor `c : (x : A) → ... → D params indices_c`:

1. **Unify** `indices_c` with `indices_scrutinee`
2. **Outcome**:
   - **Success**: Constructor is reachable, must be covered
   - **Conflict**: Constructor is impossible (unification fails), don't need to cover
   - **Stuck**: Unification blocked on metavariable, error (need annotation)

**Example**:
```agda
inductive Vec (A : Type) : Nat → Type where
  | vnil : Vec A zero
  | vcons : (n : Nat) → A → Vec A n → Vec A (succ n)

tail : {A : Type} → {n : Nat} → Vec A (succ n) → Vec A n
tail v = match v with
  | vnil => ???      -- Unify: zero =? succ n  → CONFLICT (impossible)
  | vcons x xs => xs -- Unify: succ m =? succ n → SUCCESS (m = n)
```

Coverage: Only need `vcons` case because `vnil` is impossible!

### 4. When Type Annotations Are Required (Coq Perspective)

**Source**: Coq Reference Manual, Chapter 17

Coq requires explicit `return` clauses when:

#### 4.1. **Multiple branches have different types**

```coq
Definition concat {A : Type} {m n : Nat} (v1 : Vec A m) (v2 : Vec A n) : Vec A (m + n) :=
  match v1 return Vec A (m + n) with
  | vnil => v2           (* Type: Vec A (0 + n) = Vec A n *)
  | vcons x xs => vcons x (concat xs v2)  (* Type: Vec A (succ m' + n) *)
  end.
```

Without `return Vec A (m + n)`, Coq cannot synthesize that both branches should have this type.

#### 4.2. **Pattern matching on non-variables (complex expressions)**

```coq
(* Matching on a non-variable *)
match (foo x) with ... end

(* Requires: *)
match (foo x) as y return P y with ... end
```

The `as` clause binds the scrutinee to a name, allowing the return type to reference it.

#### 4.3. **Dependent indices need to be exposed**

```coq
match v in (Vec _ n) return P n with
  | vnil => ...
  | vcons x xs => ...
end
```

The `in` clause exposes the index `n` so it can appear in the motive `P n`.

### 5. Exhaustiveness Checking Algorithm

**Key Papers**:
- McBride "Dependently Typed Functional Programs and their Proofs" (2000)
- Coquand "Pattern Matching with Dependent Types" (1992)
- "Lower Your Guards" (Sestoft-style for Haskell, 2020)

#### Classic Algorithm (Coquand/McBride):

**Input**: List of patterns, scrutinee type `T = D params indices`

**Output**: Coverage tree OR missing patterns

**Steps**:
```
1. Get all constructors C₁, ..., Cₙ of datatype D

2. For each constructor Cᵢ:
   a. Unify constructor indices with scrutinee indices
   b. If conflict: constructor is impossible, skip
   c. If success: constructor is reachable, MUST be covered
   d. If stuck: error (need to refine types or add annotation)

3. Check user-provided patterns cover all reachable constructors

4. For each branch:
   a. Run unification to get refined context
   b. Recursively check sub-patterns in refined context
   c. Type-check RHS in refined context with substitutions
```

**Example** (from our Vec type):
```
tail : Vec A (succ n) → Vec A n
tail v = match v with ...

Constructors:
  - vnil : Vec A zero
  - vcons : (m : Nat) → A → Vec A m → Vec A (succ m)

Coverage check:
  1. vnil: Unify [zero] with [succ n]
     → CONFLICT (zero ≠ succ n)
     → Skip, not reachable

  2. vcons: Unify [succ m] with [succ n]
     → SUCCESS with substitution [m ↦ n]
     → Must be covered!

Required: {vcons}
Provided: {vcons}
✓ Exhaustive
```

### 6. Miller Pattern Unification

**Key Paper**: Miller "A Logic Programming Language with Lambda-Abstraction..." (1991)

Used during elaboration for metavariable solving, not pattern matching!

**Miller Pattern**: `?M x₁ ... xₙ = t` where:
- Variables x₁...xₙ are distinct (no repetition)
- All appear linearly in the spine
- RHS `t` only contains variables from {x₁...xₙ}

**Algorithm**:
1. Check spine is linear (all distinct variables)
2. Invert: compute substitution [x₁ ↦ y₁, ..., xₙ ↦ yₙ]
3. Rename RHS: replace variables using inverted substitution
4. Occurs check: ensure ?M doesn't appear in renamed RHS
5. Solve: ?M := λx₁...xₙ. renamed_rhs

**Not the same** as pattern unification for coverage! That's first-order constructor unification.

### 7. Implementation in Our System

From `crates/hwml-core/src/pattern_unify.rs`:

```rust
pub enum PatternUnifyOutcome<'db> {
    Success(PatternUnifyResult<'db>),  // Constructor reachable, get bindings
    Conflict,                          // Constructor impossible
    Stuck(MetaVariableId),            // Blocked on unsolved meta
}

pub fn unify_pattern<'db>(
    tcon_info: &TypeConstructorInfo<'db>,
    tcon_args: &[RcValue<'db>],        // e.g., [A, succ n] for Vec A (succ n)
    dcon_info: &DataConstructorInfo<'db>,
    base_depth: usize,
) -> Result<PatternUnifyOutcome<'db>, Error<'db>>
```

**Process**:
1. Evaluate constructor return type in parameter context
2. Extract constructor indices
3. Unify with scrutinee indices using first-order unification
4. Return Success (with substitutions), Conflict, or Stuck

### 8. Current Issues in Our Implementation

From `stdlib/src/*.hwml` errors:

**Problem**: Match expressions report "Cannot infer type"

**Cause**: When checking `match e with ...`, we need:
1. Type of scrutinee (`e : T`)
2. Motive (return type as function of patterns)

Currently: We're switching to synth mode, but match can't synthesize without annotations!

**Solution** (from Coq/Agda):
- In **check mode**: Use expected type as motive
- In **synth mode**:
  - If all branches have same type, use that
  - Otherwise: ERROR, need explicit `return` clause

**Example** (Bool.hwml line 12):
```
def not (b : Bool) : Bool :=
    match b with
    | true ~> false
    | false ~> true
    end
```

Expected type: `Bool` (from signature)
Motive: `(b : Bool) → Bool` (constant, doesn't depend on b)

Should work in **check mode**! But currently errors.

### 9. Recommendations

1. **Fix match checking**: Don't switch to synth for match
   - Check branches against expected type
   - Use expected type as motive

2. **Implement motive inference**: For simple cases
   - If expected type doesn't depend on scrutinee: use it directly
   - Otherwise: may need annotation

3. **Add return clause syntax**: For complex dependent matches
   ```
   match v return (λ n. Vec A n) with
     | vnil => ...
     | vcons x xs => ...
   end
   ```

4. **Better error messages**: When unification is stuck
   - Show which constructor failed to unify
   - Suggest type annotations

5. **Coverage checking**: Already implemented in `pattern_unify.rs`
   - Used during type-checking
   - Reports non-exhaustive matches

## References

1. Coquand, T. (1992). Pattern Matching with Dependent Types.
2. McBride, C. (2000). Dependently Typed Functional Programs and their Proofs. PhD Thesis.
3. McBride, C. (2002). Elimination with a Motive. TYPES 2000.
4. Goguen, H., McBride, C., McKinna, J. (2006). Eliminating Dependent Pattern Matching.
5. Cockx, J., Devriese, D., Piessens, F. (2016). Unifiers as Equivalences. ICFP.
6. Coq Development Team. Extended Pattern Matching (Coq Manual Chapter 17).
7. Agda Documentation. Coverage Checking.


