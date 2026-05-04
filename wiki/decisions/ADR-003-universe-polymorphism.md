# ADR-003: Universe Polymorphism Strategy

**Status:** Proposed  
**Date:** 2026-05-03  
**Deciders:** HWML Core Team  
**Related:** [[research/crude-but-effective-stratification]], [[research/extensible-elaborator]]

---

## Context and Problem Statement

HWML needs a predicative type theory to ensure soundness and avoid paradoxes like Girard's paradox. This requires a stratified universe hierarchy (Set₀ : Set₁ : Set₂ : ...). However, managing universe levels explicitly is verbose and error-prone, creating friction for users who want to focus on hardware design rather than type theory internals.

**The tension:**
- **Need:** Predicative type theory for soundness
- **Want:** Convenient polymorphism over universe levels
- **Problem:** Existing approaches are either unsafe (Set : Set) or syntactically heavy (explicit level parameters everywhere)

**Key questions:**
1. What approach to universe polymorphism should HWML adopt?
2. Should we use explicit level parameters (Agda-style) or displacement-based stratification (McBride)?
3. How do we balance safety, expressiveness, and usability?

---

## Decision Drivers

### Must Have
- **Soundness:** Type system must be consistent (no paradoxes)
- **Predicativity:** Required for proof relevance and computational interpretation
- **Usability:** Hardware engineers shouldn't need deep type theory knowledge
- **Hardware hierarchies:** Must handle natural hardware type hierarchies (signals → protocols → modules)

### Nice to Have
- **Minimal annotations:** Less clutter in type signatures
- **Familiar semantics:** Similar to other dependently typed languages
- **Extensibility:** Easy to add new universe levels or constraints later
- **Performance:** Efficient elaboration and type checking

### Constraints
- Must integrate with bidirectional type checking (ADR-002)
- Must work with planned module system
- Should support future extensibility (ExEl-style plugins)

---

## Considered Options

### Option 1: Set : Set Hack (Inconsistent)

**Description:** Single universe with Set : Set

**Pros:**
- Simplest for users (no level management)
- Fastest to implement
- Maximum convenience

**Cons:**
- **Inconsistent** - leads to logical paradoxes
- Cannot be trusted for proofs
- Not a long-term solution
- Community would not accept an unsound proof assistant

**Verdict:** ❌ Rejected for production use (but acceptable for early prototypes)

---

### Option 2: Agda-Style Explicit Levels

**Description:** Explicit `Level` type with level parameters

**Example:**
```agda
Signal : {ℓ : Level} → Nat → Set ℓ → Set ℓ
Protocol : {ℓ₁ ℓ₂ : Level} → ClockDomain → Set ℓ₁ → Set ℓ₂
```

**Pros:**
- ✅ Well-understood (Agda, Coq)
- ✅ Fully expressive (can abstract over levels)
- ✅ Proven in practice (Agda standard library)
- ✅ Good error messages (can show level mismatches)
- ✅ Easy to implement (standard algorithm)

**Cons:**
- ❌ Verbose (level parameters everywhere)
- ❌ Exposes type theory to users
- ❌ Level constraints can be confusing
- ❌ Doesn't leverage hardware's natural hierarchies

**Verdict:** ✅ **Strong candidate** - proven, safe, implementable

---

### Option 3: Crude but Effective Stratification (McBride/Favonia)

**Description:** Define at lowest level, use displacement operations to shift upward

**Example:**
```hwml
-- Define once at level 0
Signal : Nat → Set₀ → Set₀

-- Use at any level (elaborator inserts displacement)
xs : Signal↑² 8 Bool↑²  -- At level 2
```

**Pros:**
- ✅ Clean user-facing syntax (no explicit levels)
- ✅ Sound (predicative, formalized by Favonia et al.)
- ✅ Fits hardware hierarchies naturally
- ✅ Users focus on hardware, not type theory
- ✅ Has formal semantics (displacement algebras)

**Cons:**
- ❌ More complex elaborator (displacement constraint solving)
- ❌ Less expressive (can't abstract over arbitrary displacements)
- ❌ Newer approach (less battle-tested than Agda)
- ❌ Explicit displacements in core language (larger terms)
- ❌ Requires sophisticated constraint solver

**Verdict:** ✅ **Promising** - elegant, but needs validation

---

### Option 4: Typical Ambiguity (Coq Classic)

**Description:** Infer universe levels silently, never show them to users

**Pros:**
- ✅ Clean syntax (no level annotations)
- ✅ Proven in Coq

**Cons:**
- ❌ Mysterious failures when inference fails
- ❌ Hard to debug universe errors
- ❌ Less predictable than explicit approaches
- ❌ Coq itself moved away from this (algebraic universes)

**Verdict:** ❌ Rejected - predictability is important for hardware design

---

## Decision

**Adopt Sterling's approach with McBride stratification:**

### Core Principles

1. **Reliable Unification First** (Sterling): Use Kovács-style nested pattern unification
2. **Explicit Universe Polymorphism** (Sterling): User controls coercions with explicit casts
3. **Work Down from Top** (Sterling): Define large by default, specialize when needed
4. **Displacement as Enhancement** (McBride): Add crude but effective as opt-in syntactic sugar

### Phase 1 (Immediate): Large-by-Default with Explicit Polymorphism

**Timeline:** Initial implementation (next 6 months)

**Sterling's Key Insight:** Don't program with respect to a universe at all if you don't need it.

**Implementation:**
```hwml
-- Large types by default (no universe annotations)
theory Category where
  ob : Type
  hom : ob → ob → Type
  -- operations...

-- Specialize when you need smallness
theory SmallCategory where
  U : Universe
  ob : U  -- Now constrained to universe U
  inherit Category / {ob => ob, hom => hom}

-- Level type for when you need explicit abstraction
Level : Type  -- External to all universes
lzero : Level
lsuc : Level → Level
_⊔_ : Level → Level → Level

Set : Level → Type
```

**User experience:**
```hwml
-- Most definitions don't mention universes at all!
Signal : Nat → Type → Type

-- When you need universe polymorphism, use explicit levels
SignalPoly : {ℓ : Level} → Nat → Set ℓ → Set ℓ

-- When you need to constrain sizes, specialize:
SmallSignal : Nat → Set₀ → Set₀
SmallSignal = Signal / {result : Set₀}
```

### Phase 2 (6-12 months): Add Displacement Syntax

**Timeline:** After Phase 1 experience

**McBride's Enhancement:** Displacement operations for convenience

**Implementation:**
```hwml
-- Displacement operator (syntactic sugar)
(↑) : {A : Set ℓ} → Set ℓ → Set (lsuc ℓ)

-- Core semantics: every top-level definition is secretly polymorphic
-- in a displacement variable δ : Displacement

-- User writes at lowest level:
Vector : Nat → Set₀ → Set₀

-- Elaborator supports displacement:
bigVec : Vector↑² 8 Bool↑²  -- At level 2
-- Desugars to: Vector {δ := shift 2} 8 Bool {δ := shift 2}
```

**Constraints collected during elaboration:**
```rust
// Displacement constraints
enum DisplacementConstraint {
    // δ₁ ≤ δ₂ (displacement ordering)
    Leq(DisplacementVar, DisplacementVar),

    // δ must shift all occurrences of level ℓ by n
    ShiftBy(DisplacementVar, Level, usize),

    // δ₁ ⊙ δ₂ = δ₃ (composition)
    Compose(DisplacementVar, DisplacementVar, DisplacementVar),
}

// Displacement algebra (Favonia et al.)
struct Displacement {
    shift: i64,  // Can be negative (McBride's extension)
}

impl Displacement {
    fn identity() -> Self { Displacement { shift: 0 } }
    fn compose(&self, other: &Self) -> Self {
        Displacement { shift: self.shift + other.shift }
    }
    fn apply_to_level(&self, level: Level) -> Level {
        match self.shift {
            n if n >= 0 => level.add_n(n as usize),
            n => level.sub_n((-n) as usize),  // May fail
        }
    }
}
```

### Phase 3 (Future): Unified Constraint Solver

**Timeline:** After Phase 2 validation

**Integration:** Combine level constraints with displacement constraints

**Constraint solving:**
```rust
enum UniverseConstraint<'db> {
    // Level constraints (from Phase 1)
    LevelLeq {
        smaller: Level<'db>,
        larger: Level<'db>,
        reason: ConstraintOrigin,
    },
    LevelEq {
        lhs: Level<'db>,
        rhs: Level<'db>,
        reason: ConstraintOrigin,
    },

    // Displacement constraints (from Phase 2)
    DisplacementLeq {
        smaller: DisplacementVar,
        larger: DisplacementVar,
        reason: ConstraintOrigin,
    },
    DisplacementShift {
        var: DisplacementVar,
        base_level: Level<'db>,
        amount: i64,
        reason: ConstraintOrigin,
    },

    // Combined: level must be in universe after displacement
    InUniverse {
        ty: RcValue<'db>,
        universe: Level<'db>,
        displacement: DisplacementVar,
        reason: ConstraintOrigin,
    },
}

// Solver produces minimal satisfying assignment
struct UniverseSolution {
    level_assignment: HashMap<LevelVar, Level>,
    displacement_assignment: HashMap<DisplacementVar, Displacement>,
}
```

---

## Concrete Constraint Examples

### Example 1: Simple Level Inference

**User code:**
```hwml
id : {A : Set _} → A → A
id x = x
```

**Constraints generated:**
```rust
// From {A : Set _}:
Constraint::LevelEq {
    lhs: Level::Meta(?ℓ0),
    rhs: Level::Meta(?ℓ1),  // Universe of A
    reason: "implicit parameter type must be in some universe",
}

// From A → A:
Constraint::LevelLeq {
    smaller: ?ℓ1,
    larger: ?ℓ2,  // Result universe
    reason: "function type universe",
}

// Solution: ?ℓ0 := lzero, ?ℓ1 := lzero, ?ℓ2 := lzero
// Final type: {A : Set₀} → A → A
```

### Example 2: Displacement Constraints

**User code (Phase 2):**
```hwml
Vec : Nat → Set₀ → Set₀
Vec n A = <implementation>

-- User wants this at level 2
bigVec : Vec 8 Bool at level 2
```

**Desugared:**
```hwml
bigVec : Vec↑² 8 Bool↑²
```

**Constraints generated:**
```rust
// Vec definition has implicit displacement δ_Vec
// Bool has implicit displacement δ_Bool

Constraint::DisplacementShift {
    var: δ_Vec,
    base_level: Level::Const(0),
    amount: 2,
    reason: "Vec↑² requires shifting from level 0 by 2",
}

Constraint::DisplacementShift {
    var: δ_Bool,
    base_level: Level::Const(0),
    amount: 2,
    reason: "Bool↑² requires shifting from level 0 by 2",
}

// Both must shift by same amount for type to be well-formed
Constraint::DisplacementEq {
    lhs: δ_Vec,
    rhs: δ_Bool,
    reason: "application requires argument at correct level",
}

// Solution: δ_Vec := Displacement { shift: 2 }
//           δ_Bool := Displacement { shift: 2 }
```

### Example 3: Combined Level and Displacement

**User code:**
```hwml
replicate : {ℓ : Level} {n : Nat} {A : Set ℓ} → A → Vec n A

-- Want to use at level 2
example = replicate {ℓ := lsuc lsuc lzero} true
```

**With displacement sugar:**
```hwml
example' = (replicate↑²) true
```

**Constraints generated:**
```rust
// Explicit version:
Constraint::LevelEq {
    lhs: ?ℓ,
    rhs: Level::Succ(Level::Succ(Level::Zero)),
    reason: "explicit level parameter",
}

// Displacement version:
Constraint::DisplacementShift {
    var: δ_replicate,
    base_level: ?ℓ_base,  // Original definition level
    amount: 2,
    reason: "replicate↑² syntax",
}

Constraint::LevelEq {
    lhs: ?ℓ_base + 2,  // After displacement
    rhs: Level::Succ(Level::Succ(Level::Zero)),
    reason: "must match explicit level",
}

// Solution: ?ℓ_base := lzero, δ_replicate := shift 2
```

### Example 4: Hardware Hierarchy (Sterling's Approach)

**User code:**
```hwml
-- Define large by default
Signal : ClockDomain → Type → Type
Protocol : Signal → Type
Module : Protocol → Type

-- Specialize when needed
SmallSignal : {U : Universe} → ClockDomain → U → U
SmallSignal {U} clk A = Signal clk A / {result in U}

-- No universe management in most code!
Counter : Signal sync (UInt 32)
AXI : Protocol Counter
CPU : Module AXI
```

**Constraints:**
```rust
// No universe constraints at all for Counter, AXI, CPU!
// They work at the "large" level (Type)

// Only when we specialize to SmallSignal:
Constraint::InUniverse {
    ty: Signal clk A,
    universe: U,
    displacement: δ_none,  // No displacement
    reason: "SmallSignal constraint",
}

// Result: User wrote zero universe annotations,
// but can specialize when needed
```

### Example 5: Universe Cumulativity (via Explicit Cast)

**Sterling's key insight:** Don't make cumulativity implicit!

**User code:**
```hwml
-- This FAILS (good - predictable!)
promote : {A : Set₀} → A → Set₁
promote x = x  -- Error: expected Set₁, got Set₀

-- This SUCCEEDS (user is explicit)
promote' : {A : Set₀} → A → Set₁
promote' x = cast x  -- Explicit upcast

-- Constraint for cast:
Constraint::LevelLeq {
    smaller: Level::Const(0),
    larger: Level::Const(1),
    reason: "explicit cast from Set₀ to Set₁",
}
```

**Why this is good:**
- Unification never silently inserts coercions
- User knows exactly when size changes happen
- No order-sensitivity in constraint solving
- Reliable, predictable elaboration

---

## Consequences

### Positive

**Sterling's Approach (Phase 1):**
- ✅ **Predictable elaboration** - Unification never silently inserts coercions
- ✅ **Reliable unification** - Kovács-style nested pattern unification
- ✅ **Most code universe-free** - Define large by default, specialize when needed
- ✅ **User control** - Explicit `cast` means users know when size changes
- ✅ **No mystery errors** - Never see "could not unify Set₀ with Set₀"
- ✅ **Hardware-friendly** - Natural types like `Signal : Type → Type` just work

**McBride Enhancement (Phase 2):**
- ✅ **Syntactic convenience** - `Vec↑²` instead of explicit level passing
- ✅ **Backward compatible** - Pure syntactic sugar over Phase 1
- ✅ **Formalized** - Displacement algebras proven sound (Favonia et al.)
- ✅ **Flexible** - Negative displacements for advanced use

**Combined Benefits:**
- ✅ **Best of both worlds** - Reliability + convenience
- ✅ **Incremental adoption** - Phase 2 is opt-in
- ✅ **Proven approach** - Sterling implementing in Pterodactyl, McBride formalized
- ✅ **Addresses fundamental issue** - Solves unification+coercion scheduling problem

### Negative

**Phase 1:**
- ❌ **Explicit casts required** - `cast x` instead of silent coercion
- ❌ **No typical ambiguity** - Can't rely on inference for universe levels
- ❌ **More annotations than Coq** - When you do need universes, must be explicit

**Phase 2:**
- ❌ **Displacement solver complexity** - New constraint domain to implement
- ❌ **Learning curve** - Users must understand displacement syntax
- ❌ **Negative levels subtle** - Advanced feature, easy to misuse

### Neutral

- **Tradeoff:** Explicit casts vs. order-sensitive implicit coercion
  - We choose **predictability** over **terseness**
  - Sterling: "Obviously not dream code, but not bad to write `cast` once in a while"
- **Documentation critical:** Must explain when to use large types vs. small types
- **Error messages:** Show constraint origins, suggest fixes
- **Standard library design:** Set good patterns for universe usage

### Why This Addresses Concerns

**Concern 1: "Universe levels are painful"**
- ✅ Sterling: Most code doesn't mention universes at all
- ✅ McBride: When you do, displacement reduces annotation burden

**Concern 2: "Unification + cumulativity is unreliable"**
- ✅ Sterling: Explicit casts separate concerns
- ✅ Kovács: Reliable unification orthogonal to coercion

**Concern 3: "Agda-style is too verbose"**
- ✅ Sterling: Large-by-default reduces 90% of annotations
- ✅ McBride: Displacement handles the remaining 10%

**Concern 4: "Set : Set is convenient"**
- ✅ Sterling: Large types give convenience without inconsistency
- ❌ But: Can't fully eliminate universe management

---

## Validation

### Success Metrics (Phase 1)

**Reliability (Sterling's Goal):**
- [ ] Unification never silently inserts universe coercions
- [ ] `cast` explicitly required for all size changes
- [ ] No order-sensitive constraint solving
- [ ] Error messages never show "Set₀ ≠ Set₀" confusion

**Usability (Large-by-Default):**
- [ ] ≥80% of user code mentions zero universe annotations
- [ ] Common patterns (Signal, Protocol, Module) work universe-free
- [ ] Only specialization (SmallSignal) requires annotations
- [ ] Hardware engineers can ignore universes in typical code

**Functional:**
- [ ] Universe stratification prevents Set : Set paradoxes
- [ ] Nested pattern unification works reliably
- [ ] Level constraints solve with clear error messages
- [ ] Standard library compiled successfully

### Decision Criteria (Phase 2: Displacement)

**Add Displacement Syntax if:**
1. Users report annotation burden in specialized code (SmallX definitions)
2. Repetitive level passing in polymorphic libraries
3. Constraint solver stable enough to add displacement domain
4. Clear use cases for displacement (not just "nice to have")
5. Error messages remain interpretable with displacement

**Defer Displacement if:**
1. <10% of code uses explicit level parameters (already low burden)
2. Large-by-default addresses most pain points
3. Displacement adds complexity without clear benefit
4. Implementation effort better spent elsewhere

### Measurement Strategy

**Quantitative:**
- Count: Lines with `Level` annotations / Total lines
- Count: Uses of `cast` operator / Total function calls
- Benchmark: Elaboration time with level constraints
- Track: Constraint solver failures (should be zero!)

**Qualitative:**
- User interviews: Understand universe pain points
- Code review: Identify common patterns
- Error analysis: Which universe errors occur most?
- Comparison: HWML code vs. Agda code (verbosity)

### Validation Checkpoints

**Month 3:**
- [ ] Phase 1 implementation complete
- [ ] Basic examples (signal processing) working
- [ ] Constraint solver handles simple cases
- [ ] Decision: Continue vs. pivot

**Month 6:**
- [ ] Standard library 50% complete
- [ ] Measure annotation burden quantitatively
- [ ] User testing with 5+ hardware engineers
- [ ] Decision: Start Phase 2 vs. iterate Phase 1

**Month 12:**
- [ ] Full system deployed
- [ ] Gather field data on universe usage
- [ ] Decide on Phase 2 adoption
- [ ] Document best practices

---

## Related Decisions

- **ADR-002:** Bidirectional typing - universe checking integrates with mode checking
- **ADR-001:** Kernel architecture - universe checking happens in elaborator, not kernel
- **Future ADR:** Module system - how do universe levels interact with module boundaries?
- **Future ADR:** Impredicativity - do we ever want Set₀ : Set₀ for specific types (e.g., Prop)?

---

## References

### Research (Foundation)

- [[research/crude-but-effective-stratification]] - McBride's displacement proposal + Favonia formalization
- [[research/disentangling-unification-coercion]] - Sterling's explicit cast approach
- Favonia, Angiuli, Mullanix: "An Order-Theoretic Analysis of Universe Polymorphism" (POPL 2023)
- McBride: "Crude but Effective Stratification" (Epilogue blog, 2011-2012)
- Kovács & Bocquet: "Nested Pattern Unification" (manuscript)
- Kovács: "Observational Type Theory for Postponed Unification" (recent)

### Jon Sterling's Pterodactyl Design

- **Fuss-free Universe Hierarchies** [01HX](https://www.jonmsterling.com/01HX/)
  - Work down from top (large by default)
  - Specialize to small when needed
  - Coherent universe hierarchy via smallness judgements

- **Disentangling Unification and Implicit Coercion** [01JQ](https://www.jonmsterling.com/01JQ/)
  - Explicit `cast` operator
  - Reliable unification first (Kovács)
  - User-controlled coercion
  - Avoids order-sensitivity problem

- **What About Universe Polymorphism?** [01HZ](https://www.jonmsterling.com/01HZ/)
  - Explicit polymorphism with Level type
  - Crude but Effective as future extension
  - Implementation in Pterodactyl kernel

### Existing Systems (Comparison)

**Agda:**
- Explicit levels with Level type
- Full expressiveness
- ❌ Verbose level management
- ❌ Universe polymorphism everywhere

**Coq/Rocq:**
- Algebraic universes + constraints
- Typical ambiguity (implicit)
- ❌ Unpredictable unification (Sterling's critique)
- ✅ Sakaguchi's coherent coercion preorder

**Lean 4:**
- Extensive level inference
- Type classes for structure coercion
- ❌ Order-sensitive elaboration (Sterling's critique)
- ❌ No dependent coercion chaining

**Idris 2:**
- Explicit levels with QTT
- ✅ Erasure via linearity
- ❌ Still requires level annotations

**Pterodactyl (Planned):**
- Sterling's approach (large-by-default + explicit cast)
- Future: McBride's displacement
- ✅ Predictable, reliable
- ✅ Minimal annotations in practice

### HWML-Specific Context

**Hardware Type Hierarchies:**
- Signal < Protocol < Module < System
- Clock domains: Synchronous < Asynchronous
- Resource types: Linear < Affine < Unrestricted
- **Advantage:** Natural fit for large-by-default

**Why Sterling's Approach Fits:**
1. Hardware specs naturally large (no size constraints)
2. Only synthesis tools care about finiteness
3. `cast` explicit at synthesis boundary
4. Most HDL code is universe-free

---

## Mugen Integration: What to Take from Favonia et al.

The **Mugen** library (Favonia, Angiuli, Mullanix, POPL 2023) provides a battle-tested OCaml implementation of displacement algebras. Here's what HWML should adopt:

### 1. Displacement Algebra Interface

**Key insight:** Displacements are strictly monotone operators closed under identity and composition.

```rust
// HWML implementation (from Mugen.Shift.S)
pub trait DisplacementAlgebra: PartialOrd + Eq {
    /// Identity displacement (no shift)
    fn id() -> Self;

    /// Check if this is the identity
    fn is_id(&self) -> bool;

    /// Compose displacements (s1 ∘ s2)
    /// Note: compose(s1, s2) means "apply s2 then s1"
    fn compose(s1: &Self, s2: &Self) -> Self;

    /// Partial order: s1 ≤ s2
    fn leq(&self, other: &Self) -> bool;
}
```

### 2. Choice of Displacement: `Mugen.Shift.Int`

**Mugen offers several choices:**
- `Mugen.Shift.Int` - Integers with addition (allows negative shifts)
- `Mugen.Shift.Nat` - Natural numbers only (classic McBride)
- `Mugen.ShiftWithJoin.Int` - Integers with join operation
- `Mugen.ShiftWithJoin.NearlyConstant` - Infinite products (advanced)

**HWML should use: `Int`** (integers with addition)

**Rationale:**
1. ✅ **Negative displacements** - Allows shunting downward (McBride's extension)
2. ✅ **Simplicity** - Just integer addition
3. ✅ **Proven** - Used in algaett proof assistant
4. ⚠️ **Caveat** - Does not handle overflow (acceptable for HWML)

```rust
// HWML: Simple integer displacement
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Displacement {
    shift: i64,
}

impl DisplacementAlgebra for Displacement {
    fn id() -> Self { Displacement { shift: 0 } }
    fn is_id(&self) -> bool { self.shift == 0 }
    fn compose(s1: &Self, s2: &Self) -> Self {
        Displacement { shift: s1.shift + s2.shift }
    }
    fn leq(&self, other: &Self) -> bool {
        self.shift <= other.shift
    }
}
```

### 3. Free vs. Embedded Level Expressions

**Mugen distinguishes:**
- `Mugen.Syntax.free` - Free level expressions (variable + shift)
- `Mugen.Syntax.endo` - Embedded in term syntax

**Structure:**
```rust
// Free level expression (for comparison)
pub enum FreeLevel<Var> {
    Var(Var),
    Shifted(Box<FreeLevel<Var>>, Displacement),
    Top,  // For convenience in type checking
}

// Embedded level expression (in HWML syntax)
pub enum Level<'db> {
    Var(LevelVar),
    Shifted(RcValue<'db>, Displacement),  // Arbitrary term + shift
    Top,
}
```

**HWML pattern (from Mugen quickstart):**
```rust
// Conversion from embedded to free (for comparison)
fn to_free_level(level: &Level<'db>) -> FreeLevel<LevelVar> {
    match level {
        Level::Var(v) => FreeLevel::Var(*v),
        Level::Shifted(l, s) => {
            FreeLevel::Shifted(Box::new(to_free_level(l)), *s)
        }
        Level::Top => FreeLevel::Top,
    }
}

// Comparison uses free levels
fn leq(l1: &Level<'db>, l2: &Level<'db>) -> bool {
    free_leq(&to_free_level(l1), &to_free_level(l2))
}
```

### 4. Smart Constructors (Consolidate Shifts)

**Key Mugen feature:** Smart constructors consolidate nested shifts

```rust
// Mugen.Builder.Endo.Make pattern
pub fn shifted(level: Level<'db>, s: Displacement) -> Level<'db> {
    if s.is_id() {
        return level;  // Optimize: x + 0 = x
    }

    match level {
        Level::Shifted(inner, s2) => {
            // Consolidate: (x + s2) + s1 = x + (s1 + s2)
            shifted(inner, Displacement::compose(&s, &s2))
        }
        Level::Top => Level::Top,  // Top cannot be shifted
        _ => Level::Shifted(level, s),
    }
}
```

**Why this matters:**
- ✅ Prevents exponential term size growth
- ✅ Makes comparison fast (fewer nested shifts)
- ✅ Canonical representation

### 5. Top Level for Type Checking

**Mugen includes a "top" level:**
```rust
pub enum FreeLevel<Var> {
    // ...
    Top,  // Greater than any other level
}
```

**Purpose:**
- Used internally by type checker
- Represents "large" types (Sterling's large-by-default)
- Cannot be shifted (shifting forbidden)
- NOT exposed to users in surface syntax

**HWML usage:**
```rust
// Internal: Type has level Top
let type_level = Level::Top;

// User cannot write:
// Signal : Type↑  // ERROR: cannot shift Top
```

### 6. Negative Displacements (McBride Extension)

**Mugen supports negative shifts:**
```rust
// Example from Mugen.Shift.Int
let shift_down = Displacement { shift: -2 };

// Example: (x + 5) + (-2) = x + 3
let l1 = shifted(var(x), Displacement { shift: 5 });
let l2 = shifted(l1, Displacement { shift: -2 });
// Result: x + 3
```

**Use case:**
- Allows more flexible displacement
- **Caveat:** Can fail if result would be negative
- Handle carefully in constraint solver

---

## Summary: The HWML Universe Strategy

### TL;DR

1. **Sterling's insight:** Unification + implicit coercion = unreliable (scheduling problem)
2. **Sterling's solution:** Explicit `cast` + reliable unification (Kovács)
3. **Sterling's bonus:** Large-by-default types (work down from top)
4. **McBride's enhancement:** Displacement syntax for convenience (crude but effective)
5. **HWML advantage:** Hardware naturally large, universes rarely needed

### What This Means in Practice

**Most user code looks like:**
```hwml
Signal clk A = ...  -- No universes!
Protocol sig = ...  -- No universes!
CPU proto = ...     -- No universes!
```

**When you need size constraints:**
```hwml
SmallSignal : {U : Universe} → ...
SmallSignal {U} = Signal / {result in U}
```

**When you need polymorphism:**
```hwml
Vec : {ℓ : Level} → Nat → Set ℓ → Set ℓ
```

**When you need convenience (Phase 2):**
```hwml
bigVec = Vec↑² 8 Bool  -- Displacement syntax
```

**When size changes (always explicit):**
```hwml
upcast x = cast x  -- User controls coercion
```

### Key Advantages for HWML

1. **Predictable elaboration** - No mystery errors, no order-sensitivity
2. **Natural hardware modeling** - Types naturally large (no bit-width constraints)
3. **Minimal annotations** - 80%+ of code universe-free
4. **User control** - `cast` makes size changes visible
5. **Proven approach** - Sterling implementing in Pterodactyl, McBride formalized

### Implementation Phases

- **Phase 1 (6 months):** Sterling's large-by-default + explicit casts
- **Phase 2 (6-12 months):** Add McBride's displacement syntax
- **Phase 3 (future):** Unified constraint solver

### Decision Rationale

We reject:
- ❌ Set : Set (unsound)
- ❌ Typical ambiguity (unpredictable)
- ❌ Fully implicit coercion (order-sensitive)

We adopt:
- ✅ Reliable unification (Kovács)
- ✅ Explicit casts (Sterling)
- ✅ Large-by-default (Sterling)
- ✅ Displacement syntax (McBride, optional)

**Why:** Combination addresses fundamental unification+coercion scheduling problem while keeping most code simple.

---

**Status:** Proposed - awaiting team review
**Date:** 2026-05-03 (Updated with Sterling/McBride integration)
**Next Review:** After Phase 1 implementation (6 months)
**Owner:** Type System Team
**Key Dependencies:**
- Kovács-style nested pattern unification (Phase 1)
- Displacement algebra implementation (Phase 2)
- Explicit cast operator in surface syntax (Phase 1)

