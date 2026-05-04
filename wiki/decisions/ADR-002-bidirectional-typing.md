# ADR-002: Bidirectional Type Checking

**Status:** Approved and Implemented  
**Date:** 2026-03-12  
**Phase:** Phase 1 (Complete)  
**Confidence:** 0.95

---

## Context

HWML is a dependently-typed language where type inference is undecidable in the general case. We need a type checking algorithm that:
- Works for dependent types
- Provides good type inference where possible
- Gives clear error messages when inference fails
- Integrates with the LCF kernel architecture

**Problem:** What type checking algorithm should HWML use?

---

## Alternatives Considered

### Option 1: Pure Type Synthesis (Bottom-Up Only)
Every term synthesizes its type. No checking mode.

**Pros:**
- Simple conceptual model
- Always produces types

**Cons:**
- Requires full type annotations everywhere
- Poor user experience (too verbose)
- Doesn't work well for lambdas

**Verdict:** **Rejected** - Too verbose for practical use

### Option 2: Full Hindley-Milner Inference
Use constraint generation and solving like Haskell.

**Pros:**
- Excellent type inference
- Minimal annotations needed

**Cons:**
- Doesn't scale to dependent types
- Complex constraint solver needed
- Unpredictable inference failures

**Verdict:** **Rejected** - Doesn't work for dependent types

### Option 3: Bidirectional Type Checking (Chosen)
Two modes: **check** (top-down) and **synth** (bottom-up).

**Pros:**
- Works for dependent types
- Predictable: users know when annotations are needed
- Local type inference (no global constraints)
- Clean separation of concerns
- Well-studied (Pierce, Turner, Dunfield/Krishnaswami)

**Cons:**
- Requires some type annotations (lambdas, lets)
- Two modes to implement instead of one

**Verdict:** **Best fit for dependent types**

### Option 4: Elaboration with Metavariables
Use unification variables for missing information.

**Pros:**
- More inference than pure bidirectional
- Can delay decisions

**Cons:**
- Adds complexity
- Can still fail to infer

**Verdict:** **We do this in addition to bidirectional** (See [[ADR-003-async-elaboration]])

---

## Decision

Implement **bidirectional type checking** with two modes:

### Check Mode (⇐)
**Given:** Term `t` and type `T`  
**Verify:** `t` has type `T`  
**Used for:** Lambdas, lets, any term with known expected type

### Synth Mode (⇒)
**Given:** Term `t`  
**Produce:** Type `T` such that `t : T`  
**Used for:** Variables, applications, annotated terms

**Key invariant:** Every typing judgment is either `Γ ⊢ t ⇐ T` (check) or `Γ ⊢ t ⇒ T` (synth).

---

## Typing Rules

### Check Mode Rules

**Lambda (Check):**
```
Γ, x : A ⊢ body ⇐ B
──────────────────────────── (Lambda-Check)
Γ ⊢ λx. body ⇐ (x : A) → B
```

**Subsumption (Check via Synth):**
```
Γ ⊢ t ⇒ T'    T' ≡ T
────────────────────── (Check-Synth)
Γ ⊢ t ⇐ T
```

### Synth Mode Rules

**Variable:**
```
x : T ∈ Γ
───────── (Var-Synth)
Γ ⊢ x ⇒ T
```

**Application:**
```
Γ ⊢ f ⇒ (x : A) → B    Γ ⊢ a ⇐ A
─────────────────────────────────── (App-Synth)
Γ ⊢ f a ⇒ B[a/x]
```

**Annotation:**
```
Γ ⊢ T ⇐ U_i    Γ ⊢ t ⇐ T
──────────────────────────── (Anno-Synth)
Γ ⊢ (t : T) ⇒ T
```

**Universe:**
```
────────────────── (Universe-Synth)
Γ ⊢ U_i ⇒ U_{i+1}
```

---

## Rationale

### Why Bidirectional?

1. **Dependent types require it**
   - Type of application `f a` depends on value of `a`
   - Need to check `a` against expected type from `f`

2. **Predictable inference**
   - Users know: lambdas need annotations, applications don't
   - Clear rules for when types are needed

3. **Local reasoning**
   - No global constraint solving
   - Type errors are local and immediate

4. **Integrates with LCF kernel**
   - Check/synth modes map cleanly to kernel API
   - Evidence tokens (`CheckedTerm`, `SynthesizedTerm`) match modes

### How It Works in Practice

**Example 1: Application (needs no annotation)**
```hwml
map successor [1, 2, 3]
```
- `map` synthesizes type `(A → B) → Vec A n → Vec B n`
- `successor` is checked against `Nat → Nat`
- `[1, 2, 3]` is checked against `Vec Nat 3`
- Result synthesizes `Vec Nat 3`

**Example 2: Lambda (needs annotation)**
```hwml
λx : Nat. x + 1
```
- Lambda checks against expected `Nat → Nat`
- Parameter type `Nat` is required
- Body `x + 1` is checked against `Nat`

**Example 3: Subsumption (automatic)**
```hwml
def id : Nat → Nat := λx : Nat. x
```
- Right side `λx. x` synthesizes `Nat → Nat`
- Synthesized type compared with declared type
- Types are equal (after normalization)

---

## Implementation

**Crate:** `hwml-core/src/kernel/`  
**Files:**
- `judgements.rs` - Implements check/synth rules
- `tokens.rs` - Evidence tokens for each mode

**Evidence Tokens:**
```rust
// Check mode: proves Γ ⊢ term ⇐ ty
pub struct CheckedTerm<'db> {
    term: RcSyntax<'db>,
    ty: RcValue<'db>,  // The type it was checked against
}

// Synth mode: proves Γ ⊢ term ⇒ ty
pub struct SynthesizedTerm<'db> {
    term: RcSyntax<'db>,
    ty: RcValue<'db>,  // The synthesized type
}
```

**Kernel API:**
```rust
// Check mode
pub async fn check_lambda<'db>(
    ctx: &mut KernelContext<'db>,
    param_ty: WellFormedType<'db>,
    body: impl FnOnce(&mut Kernel Context<'db>) -> Result<CheckedTerm<'db>>,
) -> Result<CheckedTerm<'db>>

// Synth mode
pub async fn synth_app<'db>(
    ctx: &mut KernelContext<'db>,
    func: SynthesizedTerm<'db>,
    arg: CheckedTerm<'db>,
) -> Result<SynthesizedTerm<'db>>
```

---

## Consequences

### Positive
✅ **Predictable inference** - Users know when annotations needed  
✅ **Works for dependent types** - Proven approach  
✅ **Local type checking** - No global solver  
✅ **Clear error messages** - Failed check/synth is immediate  
✅ **Kernel integration** - Evidence tokens match modes  
✅ **Well-studied** - Extensive literature and implementations

### Negative
❌ **Some annotations required** - Lambdas, some lets  
❌ **Two modes to implement** - More complexity than one mode

### Trade-offs
- **Predictability over inference** - Better UX for dependent types
- **Local reasoning over global** - Simpler implementation
- **Annotations when needed** - Clarity over terseness

---

## Integration with Other Systems

### With NbE ([[entities/nbe]])
Type equality uses normalization:
```rust
async fn types_equal(ty1, ty2) -> bool {
    let ty1_whnf = whnf(ty1).await;
    let ty2_whnf = whnf(ty2).await;
    values_equal(ty1_whnf, ty2_whnf)
}
```

### With Metavariables ([[ADR-003-async-elaboration]])
When type isn't known, insert metavariable:
```rust
// If expected type unknown
let meta_ty = ctx.new_meta(Universe(0));
let checked = check(term, meta_ty).await?;
```

### With LCF Kernel ([[ADR-001-lcf-kernel]])
Evidence tokens prove check/synth succeeded:
```rust
let checked: CheckedTerm<'db> = check_lambda(...);
// `checked` is proof that lambda has expected type
```

---

## Sources

**Primary:**
- `design/ARCHITECTURE.md` - Bidirectional rules encoded in kernel

**Research Papers:**
- Pierce & Turner: "Local Type Inference" (2000) - Original bidirectional
- Dunfield & Krishnaswami: "Complete and Easy Bidirectional Typechecking for Higher-Rank Polymorphism" (2013)
- Abel, Pientka: Bidirectional with dependent types
- Coquand: NbE for type checking

**Implementations:**
- Agda - Uses bidirectional checking
- Lean 4 - Bidirectional with elaborate metavariable solving
- Idris 2 - Bidirectional type checking

---

## Related

**Decisions:**
- [[ADR-001-lcf-kernel]] - Kernel enforces bidirectional rules
- [[ADR-003-async-elaboration]] - Extends bidirectional with metavariables

**Entities:**
- [[entities/bidirectional-typing]] - Detailed explanation
- [[entities/nbe]] - Type normalization for equality checking

**Components:**
- [[components/kernel]] - Implements the typing rules
- [[components/elaborator]] - Uses check/synth modes

---

## Status History

- **2026-03-12:** Bidirectional chosen as type checking approach
- **2026-03-15:** Kernel judgements implemented
- **2026-03-20:** Evidence tokens added
- **2026-04-10:** Phase 1 complete, production use
