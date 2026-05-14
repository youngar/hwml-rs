# Implicit Arguments and First-Class Polymorphism

**Created:** 2026-05-13  
**Type:** Survey + Implementation Analysis  
**Confidence:** 0.95  
**Status:** Research complete, ready for implementation planning

---

## Executive Summary

**Problem:** How to implement implicit function arguments (`{A : Type} → A → A`) in a bidirectional type checker when the checking type is unknown (meta-headed)?

**Key Challenge:** The **lambda insertion problem** - when checking `λ x. x` against a meta-headed type `?M`, should we insert implicit lambdas?

**Best Solution:** **Dynamic Order Elaboration (DOE)** - postpone checking when ambiguous, process once metadata is solved.

**Recommendation for HWML:** Implement DOE as it's the simplest, most practical solution (~150 LOC overhead).

---

## The Problem in Detail

### Lambda Insertion Problem

Consider:
```
let foo : Maybe ({A} → A → A) = Just (λ x. x)
```

**What goes wrong without first-class polymorphism:**
1. Infer type for `Just (λ x. x)`
2. Insert meta: `Just {?0} : ?0 → Maybe ?0`
3. Check `λ x. x` against `?0` (meta-headed, unknown!)
4. **Assume no insertion needed**, infer `?1 → ?1` for `λ x. x`
5. Solve `?0 := ?1 → ?1`
6. Unify `Maybe (?1 → ?1)` with `Maybe ({A} → A → A)` → **FAILS**

**What we want:**
```
Just {{A : U} → A → A} (λ {A : U} (x : A). x)
```

### Why Meta-Headed Types Are Ambiguous

- **Explicit function type** `A → B`: no insertion, check body against `A → B`
- **Implicit function type** `{A} → B`: insert lambda `λ {A}. ...`, check body against `B`
- **Meta-headed type** `?M spine`: **don't know yet** - could be either!

Later, `?M` might be solved to:
- An implicit function → should have inserted lambda ❌ too late!
- Not a function → correct to skip insertion ✅
- Another meta → still ambiguous 🤷

---

## Solutions Landscape

### 1. Dynamic Order Elaboration (DOE) ⭐ **RECOMMENDED**

**Invented by:** András Kovács (2020)  
**Source:** [elaboration-zoo/06-first-class-poly](https://github.com/AndrasKovacs/elaboration-zoo/tree/master/06-first-class-poly)

**How it works:**
1. When checking type is meta-headed → **postpone** checking
2. Create **placeholder meta** `?P` to represent the eventual result
3. Track which metas each postponed check is **blocked on**
4. When a meta is solved → retry all blocked checks
5. At end of elaboration → process remaining checks (assume no insertion)

**Advantages:**
- ✅ **Simplest solution** (~150 LOC overhead)
- ✅ **No core syntax changes** (no telescopes, no special nodes)
- ✅ **Single-pass traversal** (just reordered)
- ✅ **Orthogonal to type system** (works for System F, MLTT, etc.)
- ✅ **Stronger than Quick Look** (see comparison below)

**Disadvantages:**
- ⚠️ **Less precise than FCIF** (guesses at the end)
- ⚠️ **Placeholder metas** can occasionally block pattern unification

**Production use:** [sixty language](https://github.com/ollef/sixty)

---

### 2. FCIF (First-Class Implicit Functions)

**Invented by:** András Kovács (2020)  
**Paper:** [Elaboration with First-Class Implicit Function Types (ICFP 2020)](https://dl.acm.org/doi/10.1145/3408983)  
**Code:** [implicit-fun-elaboration](https://github.com/AndrasKovacs/implicit-fun-elaboration)

**How it works:**
1. Add **telescope types** to core syntax: `Tel` universe
2. Insert lambda with **telescope binder** when ambiguous
3. Telescope computes to zero or more implicit functions during unification
4. Add **constancy constraints** to avoid non-dependent implicits

**Core typing rules (definitional currying):**
```
() → A  ≡  A
((x : (a : A) * Γ a) → B x)  ≡  ({a : A} → (γ : Γ a) → B (a, γ))
```

**Advantages:**
- ✅ **Most precise** (never guesses)
- ✅ **No postponing** (marches forward)
- ✅ **Theoretically elegant**

**Disadvantages:**
- ❌ **Complex** (requires core syntax changes)
- ❌ **Telescope normalization** overhead
- ❌ **Constancy constraints** add complexity
- ❌ **Fails on some cases DOE handles** (see comparison)

---

### 3. Quick Look (GHC 9.2+)

**Source:** [GHC Proposal #274](https://github.com/ghc-proposals/ghc-proposals/blob/master/proposals/0274-quick-look-impredicativity.rst)  
**Paper:** [A Quick Look at Impredicativity](https://www.microsoft.com/en-us/research/publication/a-quick-look-at-impredicativity/)

**How it works:**
1. Before checking, do a **quick look pass** over neutral spines
2. Gather meta solutions from simple unifications
3. Then do **proper elaboration** with solved metas

**Advantages:**
- ✅ **No core changes**
- ✅ **Works for GHC's needs**

**Disadvantages:**
- ❌ **Duplicates elaboration logic** (two passes)
- ❌ **Quadratic traversal** (without memoization)
- ❌ **Restricted to neutral spines** (variables, constructors, applications)
- ❌ **Strictly weaker than DOE**

**Why DOE is better:**
- DOE is **exact**: postpones only when needed
- QL is **eager approximation**: always pre-processes
- DOE quick-looks into **arbitrary expressions**
- QL limited to **neutral spines**

---

### 4. Application Insertion Problem (UNSOLVED)

**The dual problem:**
```
let f = λ g. (g true, g zero)
```

**Desired type:** `({A} → A → A) → Pair Bool Nat`

**Problem:** Need to **invent** implicit function types, not just insert lambdas.

**Why it's hard:**
- Infinite choices: `({A} → A → Bool) → Pair Bool Bool`
- No minimal/obvious choice
- Requires inventing out of thin air

**Solutions:**
- ❌ **No practical system solves this generally**
- ⚠️ **MLF** has partial support, but extremely complex and doesn't scale to dependent types

**HWML Decision:** Don't attempt application insertion - require explicit annotations for this case.

---

## Terminology Clarification

### "Impredicativity" Confusion

**Type Theory meaning:** Universe is impredicative if `∀x:A. B : U` when `B : U`, regardless of `A`.
- Example: Coq's `Prop` universe

**Elaboration meaning:** Can solve metas to implicit function types.
- Example: `?M` solved to `{A} → B`

**Historical collision:** These used to coincide but are now **orthogonal**:
- **Coq:** Predicative elaboration, impredicative universes
- **Agda:** Impredicative elaboration, predicative universes
- **GHC <9.2:** Predicative elaboration, impredicative `*`

**Recommendation:** Use "first-class polymorphism" or "polymorphic instantiation" to avoid confusion.

---

## DOE Algorithm Details

### Core Data Structures

```rust
struct PostponedCheck<'db> {
    /// The term to check
    preterm: Expression,
    /// The (meta-headed) checking type
    expected_ty: RcTy<'db>,
    /// Placeholder meta representing the result
    placeholder: MetaId,
    /// Meta we're blocked on
    blocked_on: MetaId,
}

struct ElabState<'db> {
    /// All postponed checks
    postponed: Vec<PostponedCheck<'db>>,
    /// Which checks are blocked on which metas
    blocked_checks: HashMap<MetaId, Vec<usize>>,
    // ... existing state ...
}
```

### Algorithm Steps

**1. During checking:**
```rust
fn check(ctx, term, ty) {
    match ty.head() {
        // Known function type - insert if implicit
        PiCode(_, Implicit, _) => insert_lambda_and_check(),
        PiCode(_, Explicit, _) => check_without_insertion(),

        // Meta-headed - postpone!
        Flex(meta_id, spine) => {
            let placeholder = fresh_meta(ty);
            postponed.push(PostponedCheck {
                preterm: term,
                expected_ty: ty,
                placeholder,
                blocked_on: meta_id,
            });
            blocked_checks[meta_id].push(postponed.len() - 1);
            return placeholder;
        }
    }
}
```

**2. After solving a meta:**
```rust
fn solve_meta(meta_id, solution) {
    // Solve the meta
    metas[meta_id] = Some(solution);

    // Retry all blocked checks
    for check_idx in blocked_checks[meta_id] {
        let check = &postponed[check_idx];

        // Force the checking type (substitute solved meta)
        let ty_forced = force(check.expected_ty);

        match ty_forced.head() {
            // Now we know - actually check!
            PiCode(_, _, _) | Other => {
                let result = check(ctx, check.preterm, ty_forced);
                unify(check.placeholder, result);
            }
            // Still meta-headed - reblock on new meta
            Flex(new_meta, _) => {
                check.blocked_on = new_meta;
                blocked_checks[new_meta].push(check_idx);
            }
        }
    }
}
```

**3. At end of file:**
```rust
fn finish_elaboration() {
    // Process remaining postponed checks
    while let Some(check) = postponed.pop() {
        // Assume no insertion (guess)
        let result = check_assuming_explicit(check.preterm, check.expected_ty);
        unify(check.placeholder, result);
    }
}
```

### Key Insight: Placeholder Metas

**Why placeholders are critical:**
- Without: postponing creates **cascading blockage**
- With: downstream code can **unify** with placeholder
- Placeholder acts as a **promise** - filled in later

**Example:**
```
let foo : ?M = ?P  -- ?P is placeholder for postponed check
... unify ?M with Bool ...  -- This works!
-- Later: actually check and solve ?P
```

---

## Comparison Matrix

| Feature | DOE | FCIF | Quick Look | Agda (current) |
|---------|-----|------|------------|----------------|
| **Complexity** | Low (~150 LOC) | High | Medium | Medium |
| **Core changes** | None | Telescopes | None | None |
| **Traversals** | 1 pass | 1 pass | 2+ passes | 1 pass |
| **Precision** | High | Highest | Medium | Low |
| **Production use** | sixty | None | GHC 9.2+ | Agda |

### Concrete Examples

**DOE succeeds, FCIF fails:**
```
let foo : (({A} → A → A) → Bool × Nat) = id (λ f. (f true, f zero))
```
- FCIF tries to infer type for `λ f. ...` → fails
- DOE postpones over the lambda → succeeds when checking with known type

**FCIF succeeds, DOE fails:**
```
let foo = λ f x y. f x y
```
- DOE: placeholder meta blocks pattern unification
- FCIF: telescopes allow refinement

**Both succeed:**
```
let foo : Maybe ({A} → A → A) = Just (λ x. x)
```

---

## Implementation Roadmap for HWML

### Phase 1: Core Infrastructure (Week 1)

**1. Add Icit enum:**
```rust
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Icit {
    Explicit,
    Implicit,
}
```

**2. Update Syntax:**
- `PiCode(RcSyntax, Icit, BindingSyntax)`
- `Application { function, argument, icit }`
- Parser: `{x : A} → B` syntax

**3. Update Value domain:**
- `PiCode(RcValue, Icit, Closure)`
- `Eliminator::Application { argument, icit }`
- Spine: `Vec<Eliminator>` (Icit embedded in Application)

### Phase 2: Basic Insertion (Week 2)

**1. Implement insertion without postponing:**
```rust
fn check(term, ty) {
    match ty {
        PiCode(_, Implicit, body) => {
            // Insert implicit lambda
            check_lambda_body(term, body)
        }
        _ => check_explicit(term, ty)
    }
}
```

**2. Test with known types:**
```
def id : {A : Type} → A → A = λ x. x
-- Elaborates to: λ {A} x. x
```

### Phase 3: DOE Implementation (Week 3-4)

**1. Add postponed check infrastructure:**
- `PostponedCheck` struct
- `ElabState.postponed` queue
- `blocked_checks` map

**2. Implement placeholder metas:**
- Create placeholder when postponing
- Return placeholder to caller
- Unify placeholder with result later

**3. Meta solving hooks:**
- Hook into `solve_meta`
- Retry blocked checks
- Handle reblocking on new metas

**4. End-of-file processing:**
- Process remaining postponed checks
- Assume no insertion (explicit)

### Phase 4: Testing & Refinement (Week 5)

**Test suite from elaboration-zoo:**
- [examples.txt](https://github.com/AndrasKovacs/elaboration-zoo/blob/master/06-first-class-poly/examples.txt)
- Standard benchmark for first-class polymorphism

**Error messages:**
- Report insertion ambiguity clearly
- Show which meta is blocking

---

## References

### Primary Sources

1. **DOE Algorithm:** [elaboration-zoo/06-first-class-poly](https://github.com/AndrasKovacs/elaboration-zoo/tree/master/06-first-class-poly)
2. **FCIF Paper:** [Elaboration with First-Class Implicit Function Types (ICFP 2020)](https://dl.acm.org/doi/10.1145/3408983)
3. **Quick Look:** [GHC Proposal #274](https://github.com/ghc-proposals/ghc-proposals/blob/master/proposals/0274-quick-look-impredicativity.rst)
4. **Agda Implementation:** [TypeChecking.Implicit](https://agda.github.io/agda/src/Agda.TypeChecking.Implicit.html)

### Related Issues

- [Agda #4105](https://github.com/agda/agda/issues/4105) - Better support for impredicative instantiation
- [Agda #1079](https://github.com/agda/agda/issues/1079) - Canonical implicit lambda insertion issue
- [Agda #4751](https://github.com/agda/agda/issues/4751) - Conversion checker implicit insertion (design flaw)

---

## HWML-Specific Considerations

### Hardware Erasure

**Good news:** Implicit arguments are **erased during lowering**, so no backend changes needed!

From our previous analysis:
- Hardware lowering (`saturate_value`) beta-reduces **all** lambdas
- CIRCT translation sees only **saturated applications**
- Wire generation **unaffected** by Icit

**Implication:** Icit is purely a **type-checking time** concern.

### Interaction with Provenance

DOE's postponing integrates naturally with provenance tracking:
- Postponed checks have clear **origin** (source location)
- Placeholder metas have **provenance** (created for what?)
- Error messages: "Could not infer implicit arguments for X"

### Integration with Constraint Solver

HWML already has a constraint solver (`SolverState`, constraint queue).

**DOE fits perfectly:**
- Postponed checks = special constraint type
- Blocked on meta = existing dependency tracking
- End-of-file processing = existing solver finalization

**Implementation:** Add `ConstraintKind::PostponedCheck` variant.

---

## Decision

**Status:** ✅ **Adopt DOE for HWML**

**Rationale:**
1. ✅ Simplest solution (~150 LOC)
2. ✅ No core syntax changes
3. ✅ Fits existing constraint solver architecture
4. ✅ Stronger than alternatives (except FCIF)
5. ✅ Production-proven (sixty language)
6. ✅ Theoretical backing (András Kovács)

**Next Steps:**
1. Create ADR documenting this decision
2. Implement Phase 1 (Icit infrastructure)
3. Implement Phase 2 (basic insertion)
4. Implement Phase 3 (DOE postponing)
5. Test with elaboration-zoo examples

---

**See also:**
- [[ADR-002-bidirectional-typing]] - Current bidirectional typing implementation
- [[provenance-deep-dive]] - Provenance tracking (integrates with postponing)
- [[extensible-elaborator]] - Constraint-based elaboration (similar architecture)

