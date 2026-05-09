# Type Unification in Dependent Types: Structures, Records, and Efficient Implementation

**Type:** Research Survey & Synthesis  
**Created:** 2026-05-04  
**Confidence:** 0.9  
**Sources:** Abel & Pientka (2011), Agda, Coq, Lean 4, Epigram, ML modules, Academic papers  
**Relevance:** **CRITICAL** - Core unification algorithm for HWML's elaborator, especially for structures/records

---

## Executive Summary

This research surveys **type unification algorithms for dependent types** with specific focus on:
1. **Σ-types (dependent pairs/records)** - How to efficiently unify structures
2. **Implementation techniques** - Practical optimizations from production systems
3. **Module systems** - How different languages handle structured data
4. **Performance** - What makes unification fast in practice

**Key Finding:** Modern dependently-typed languages use **type isomorphisms** to flatten Σ-types into Π-types during unification, avoiding the complexity of dependent pairs while maintaining expressiveness.

---

## Core Problem: Unification with Σ-Types

### Miller's Pattern Fragment (1991)

**Classic higher-order pattern unification:**
- Meta-variables applied to **distinct bound variables**
- Example: `?f x y` where `x, y` are distinct
- **Decidable** with **most general unifiers** (MGUs)

**Limitation:** Doesn't handle projections or record fields well.

### The Σ-Type Challenge

**Problem:** These terms should be equivalent but don't match Miller's pattern:
```
(a) λy₁.λy₂. X (y₁, y₂)        -- Pair as argument
(b) λy. X (fst y) (snd y)       -- Projections of bound variable
(c) λy₁.λy₂. X y₁ y₂            -- Separate arguments (Miller pattern)
```

Only (c) is a Miller pattern, but all three are **morally the same**!

**Solution (Abel & Pientka 2011):** Use **type isomorphisms** to transform (a) and (b) into (c).

---

## Abel & Pientka's Algorithm (TLCA 2011)

### Key Innovation: Type Isomorphisms for Σ-Types

**Fundamental isomorphisms:**
```
Πz:(Σx:A.B).C  ≅  Πx:A.Πy:B.[(x,y)/z]C
f : Πx:A.Σy:B.C  ≅  (f₁ : Πx:A.B, f₂ : Πx:A.[f₁ x/y]C)
```

**Effect:** Eliminates Σ-types from unification problems by decomposing them into Π-types.

### Algorithm Structure

**Constraint-based rewrite system:**
```
∆ ⊢ K  →  ∆' ⊢ K'
```

Where:
- `∆` = meta-variable context
- `K` = set of constraints
- Transitions preserve solutions

### Key Operations

**1. Decomposition of Functions/Pairs**
```
Ψ ⊢ λx.M = λx.N : Πx:A.B  →  Ψ,x:A ⊢ M = N : B
Ψ ⊢ (M₁,M₂) = (N₁,N₂) : Σx:A.B  →  Ψ ⊢ M₁=N₁:A ∧ Ψ ⊢ M₂=N₂:[M₁/x]B
```

**2. η-Contraction**
```
u[σ{λx. R x}] = N  →  u[σ{R}] = N           (if x ∉ FV(R))
u[σ{(fst R, snd R)}] = N  →  u[σ{R}] = N
```

**3. Eliminating Projections**
```
Context: Ψ₁, x:Πy:A.Σz:B.C, Ψ₂
Problem: u[σ{π(x M)}] = N

Apply: τ = [λy.(x₁ y, x₂ y)/x]
Result: Ψ₁, x₁:Πy:A.B, x₂:Πy:A.[x₁ y/z]C, Ψ₂ ⊢ u[[τ]σ] = [τ]N
```

**4. Flattening Σ-types in Meta-Variable Contexts**
```
Active meta: u:A[Φ] where Φ contains Σ-types
Transform: Φ → Φ' (flatten all Σ-types)
New meta: v:([σ⁻¹]A)[Φ']
Solution: u := v[σ]
```

**5. Pruning (Higher-Dimensional)**
```
Problem: u[x] = suc(v[x,y])
Since u doesn't depend on y, v cannot either
Prune: v[x,y] := v'[x]
```

### Lowering Meta-Variables

**Transform higher-type metas to simpler ones:**
```
u:(Πx:A.B)[Φ]  →  v:B[Φ,x:A],  u := λx.v
u:(Σx:A.B)[Φ]  →  u₁:A[Φ], u₂:([u₁/x]B)[Φ],  u := (u₁,u₂)
```

**Benefit:** Simplifies the structure of meta-variables during solving.

---

## Implementation in Production Systems

### Agda

**Unification Approach:**
- Higher-order pattern unification with extensions
- Eta-expansion for records (controlled by `eta-equality` directive)
- Record types can be marked `pattern` or `no-eta-equality`

**Record Implementation:**
```haskell
-- Agda.TypeChecking.Records module
etaExpandRecord :: QName -> Args -> Term -> TCM Term
  -- Eta-expand record value at record type

tryEtaExpandRecord :: Type -> Term -> TCM (Maybe Term)
  -- Try eta-expansion if it's an eta-record
```

**Key Features:**
1. **Eta-equality control:** Users choose per-record
2. **Eta-contraction:** Automatic when beneficial
3. **Higher-dimensional unification:** Solve equality proofs recursively
4. **Postponement:** Delay non-patterns until more info available

**Performance Notes:**
- Eta-expansion can be expensive
- Memoization of eta-expanded forms
- Careful about when to trigger expansion

### Lean 4

**Structure Implementation:**
- Structures are special inductive types (single constructor)
- Projection functions auto-generated
- Integration with type class system

**Type Class Resolution:**
```lean
-- Implicit instance synthesis via unification
class Add (α : Type u) where
  add : α → α → α

-- Unification finds appropriate instance
def double {α : Type u} [Add α] (x : α) : α := Add.add x x
```

**Optimizations:**
1. **Tabled resolution:** Cache type class lookups
2. **Discrimination trees:** Fast instance matching
3. **Incremental:** Only re-resolve when dependencies change

### Coq (Rocq)

**Module System:**
- Structures as dependent records
- Module types as signatures
- Functors for parameterized modules

**Packed Classes (Mathematical Components):**
```coq
Record mixin_of (T : Type) := Mixin {
  op : T → T → T;
  axiom : ∀ x y, op x y = op y x
}.

Record class_of T := Class {
  base : Equality.mixin_of T;
  mixin : mixin_of T
}.

Structure type := Pack { sort; _ : class_of sort }.
```

**Key Technique: Telescopes**
- Chain of coercions: `T → sort₁ → sort₂ → ... → base_type`
- Type inference follows coercion chain
- Drives resolution of higher-order unification

### Epigram (Historical)

**Universe of Inductive Types:**
- First-order representation of datatypes
- Σ-types for dependent records
- W-types for well-founded trees

**Levitation Approach:**
```
data Desc (I : Set) : Set where
  var : I → Desc I
  sg  : (S : Set) → (T : S → Desc I) → Desc I  -- Sigma
  pi  : (S : Set) → (T : S → Desc I) → Desc I  -- Pi
```

**Benefit:** Generic programming over datatype structure.

---

## Performance: What Makes Unification Fast?

### 1. Hash Consing & Memoization

**Hash Consing (Tog⁺ prototype):**
- Share identical subterms in memory
- Structural equality becomes pointer equality
- **Performance:** 131s → 22s on setoid example (6x speedup!)

**Memoization:**
- Cache unification results
- Avoid re-solving identical sub-problems
- Critical for large hardware types with repeated patterns

### 2. Syntactic Equality Fast Path

**Type-agnostic syntactic check (Tog⁺):**
```haskell
syntacticEqual :: Term -> Term -> Bool
syntacticEqual t1 t2 = alphaEquivalent t1 t2  -- No type info needed!
```

**When applicable:**
```
Γ ⊢ t : A    Γ ⊢ t : B    t ≡ t (syntactically)
──────────────────────────────────────────────
Γ ⊢ (t : A) ≈ (t : B)
```

**Impact:** Avoids expensive type comparisons for obviously equal terms.

### 3. Eager vs. Lazy Strategies

**Kovács's Nested Pattern Unification:**
- **Lazy η-expansion:** Only expand when necessary
- **Pattern detection:** Check if problem is pattern before solving
- **Postponement:** Delay non-patterns until constraints simplify

**Abel & Pientka's Dynamic Patterns:**
- Solve pattern sub-problems **eagerly**
- Postpone non-pattern sub-problems
- Accumulate information to simplify postponed problems

### 4. Occurs Check Optimization (Pientka & Pfenning 2003)

**Problem:** Expensive to check if meta occurs in term.

**Solution: Linearization**
```
Traditional: Check every occurrence of ?X in M
Optimized: If ?X occurs linearly, skip check in many cases
```

**Performance:** Up to 445% improvement on proof-carrying code benchmarks!

### 5. Spine Representation

**Instead of nested applications:**
```
Traditional: App (App (App f a) b) c
Spine: f · [a, b, c]
```

**Benefits:**
- Direct access to head
- Faster pattern matching
- Better for η-expansion

---

## Module Systems & Structures

### ML Modules

**Core Concepts:**
- **Structures:** Collections of definitions
- **Signatures:** Module types
- **Functors:** Parameterized modules (dependent functions)

**Type Checking:**
```ocaml
module type MONOID = sig
  type t
  val unit : t
  val op : t -> t -> t
end

module IntAdd : MONOID = struct
  type t = int
  let unit = 0
  let op = (+)
end
```

**Elaboration to System Fω:**
- Structures → existential types
- Functors → polymorphic functions
- Signature matching → subtyping

### Hierarchy Builder (Mathematical Components)

**Packed Classes Architecture:**
```coq
(* Mixin: operations + axioms *)
mixin → mixin → ... → full_mixin

(* Class: inheritance relations *)
class = { carrier : Type; mixins : ... }

(* Structure: carrier + class *)
structure = { sort : Type; class : class_of sort }
```

**Type Inference:**
- Follow coercion telescope
- Unify with expected type
- Resolve canonical structures

### 1ML (Rossberg)

**Unifying Core and Modules:**
- No distinction between functions and functors
- No distinction between records and structures
- Everything is a module

**Type System:**
- Expressible in System Fω
- No dependent types needed (!)
- "F-ing modules" approach

**Implication:** Module systems can be understood as syntactic sugar over simpler calculi.

---

## Practical Recommendations for HWML

### Algorithm Choice

**Primary: Abel & Pientka's Constraint-Based Unification**

**Rationale:**
1. ✅ Handles Σ-types (essential for hardware structures)
2. ✅ Provably correct (termination + soundness)
3. ✅ Implemented in Agda (battle-tested)
4. ✅ Extensible with new constraints

**Extensions to Consider:**
- **Kovács's nested patterns:** Better interaction with projections
- **Tog⁺ twin types:** Handle heterogeneous cases (Phase 2)
- **Observational techniques:** For postponement (Phase 3)

### Performance Optimizations

**High Priority (Phase 1):**
1. **Hash consing:** Share structure in large hardware types
2. **Syntactic equality fast path:** Cheap early-out
3. **Spine representation:** Direct head access

**Medium Priority (Phase 2):**
1. **Memoization:** Cache unification results
2. **Linearization:** Optimize occurs checks
3. **Incremental solving:** Only re-solve changed constraints

**Low Priority (Phase 3):**
1. **Tabled resolution:** For type classes (if added)
2. **Discrimination trees:** Fast pattern matching
3. **Parallel solving:** Independent constraints

### Structure Representation

**Recommendation: Lean-style Structures**

```hwml
structure Signal (width : Nat) where
  data : BitVec width
  valid : Bool

-- Auto-generated projections
Signal.data : Signal w → BitVec w
Signal.valid : Signal w → Bool

-- Constructor
Signal.mk : BitVec w → Bool → Signal w
```

**With Eta-Equality:**
```
s ≡ Signal.mk (Signal.data s) (Signal.valid s)
```

**Why:**
- Clean user syntax
- Efficient representation (single constructor inductive)
- Good interaction with unification
- Proven in Lean 4

### Handling Hardware-Specific Features

**Clock Domains:**
```hwml
structure Clocked (α : Type) (clk : ClockDomain) where
  value : α

-- Unification must respect clock domain constraints
?X : Clocked Nat ?clk
-- When unified with (clocked_val : Clocked Nat SystemClock)
-- Produces: ?clk := SystemClock
```

**Bit Widths:**
```hwml
-- Unification of dependent pairs
?n : Nat
?sig : Signal ?n

-- Unified with: (wire8 : Signal 8)
-- Produces: ?n := 8, ?sig := wire8
```

**Key:** Use dependent types to encode hardware constraints, let unification enforce them!

---

## Implementation Sketch for HWML

### Data Structures

**Terms (following Abel & Pientka):**
```rust
enum Term {
    Var(Name),
    Meta(MetaVar, Subst),  // Meta-variable with suspended substitution
    Lam(Name, Box<Term>),
    App(Box<Term>, Box<Term>),
    Pair(Box<Term>, Box<Term>),
    Fst(Box<Term>),
    Snd(Box<Term>),
    // ... hardware-specific constructors
}

struct MetaVar {
    id: MetaId,
    ty: Type,
    ctx: Context,
}
```

**Constraints:**
```rust
enum Constraint {
    Unify { lhs: Term, rhs: Term, ty: Type, ctx: Context },
    TwinType { lhs: (Term, Type), rhs: (Term, Type), ctx: Context },  // Phase 2
    // ... other constraint types
}

struct ConstraintSet {
    constraints: Vec<Constraint>,
    meta_ctx: MetaContext,
    solutions: HashMap<MetaId, Term>,
}
```

### Core Algorithm

```rust
impl Unifier {
    fn solve(&mut self, mut constraints: ConstraintSet) -> Result<Subst, Error> {
        while !constraints.is_empty() {
            match constraints.pop_solvable() {
                Some(Constraint::Unify { lhs, rhs, ty, ctx }) => {
                    // 1. Try syntactic equality (fast path)
                    if syntactically_equal(&lhs, &rhs) {
                        continue;
                    }

                    // 2. Decompose by structure
                    if let Some(new_constraints) = self.decompose(&lhs, &rhs, &ty)? {
                        constraints.extend(new_constraints);
                        continue;
                    }

                    // 3. Check if it's a pattern
                    if let Some((meta, subst, term)) = as_pattern(&lhs, &rhs) {
                        // 4. Prune if necessary
                        let (meta, subst) = self.prune(meta, subst, &term)?;

                        // 5. Invert substitution
                        if let Some(solution) = invert_subst(&subst, &term) {
                            // 6. Occurs check
                            if !occurs(meta, &solution) {
                                self.instantiate(meta, solution)?;
                                continue;
                            }
                        }
                    }

                    // 7. Apply local simplifications (η-contraction, projection elimination)
                    if let Some(simplified) = self.simplify(&lhs, &rhs, &ty)? {
                        constraints.push(simplified);
                        continue;
                    }

                    // 8. Postpone if non-pattern
                    constraints.postpone(Constraint::Unify { lhs, rhs, ty, ctx });
                }

                None => {
                    // No more solvable constraints - check if any postponed
                    if constraints.has_postponed() {
                        return Err(Error::UnificationStuck);
                    }
                    break;
                }
            }
        }

        Ok(self.extract_solution())
    }
}
```

### Optimizations

**Hash Consing:**
```rust
struct HashCons<T> {
    arena: Arena<T>,
    cache: HashMap<T, ArenaId>,
}

impl HashCons<Term> {
    fn intern(&mut self, term: Term) -> TermRef {
        if let Some(&id) = self.cache.get(&term) {
            TermRef(id)  // Already exists - O(1)
        } else {
            let id = self.arena.alloc(term.clone());
            self.cache.insert(term, id);
            TermRef(id)
        }
    }
}
```

**Syntactic Equality:**
```rust
fn syntactically_equal(t1: &Term, t2: &Term) -> bool {
    // With hash consing:
    if let (TermRef(id1), TermRef(id2)) = (t1, t2) {
        return id1 == id2;  // Pointer equality!
    }

    // Without hash consing:
    alpha_equivalent(t1, t2)  // No type information needed
}
```

---

## Key Insights from the Research

### 1. Type Isomorphisms are Powerful

**Abel & Pientka's core idea:**
- Don't treat Σ-types as primitive in unification
- Transform them to Π-types using isomorphisms
- Simplifies the algorithm dramatically

**Lesson:** Choose the right representation for your algorithm, not for your surface syntax.

### 2. Postponement is Essential

**Dynamic pattern unification:**
- Not all problems are solvable immediately
- Postpone and retry with more information
- Requires careful orchestration to avoid infinite loops

**Lesson:** Build postponement into your constraint solver from day one.

### 3. Performance Comes from Multiple Sources

**No single silver bullet:**
- Hash consing: 6x speedup (Tog⁺)
- Occurs check optimization: 4.4x speedup (Pientka & Pfenning)
- Syntactic equality: Variable, but significant

**Lesson:** Profile and optimize multiple aspects.

### 4. Module Systems Can Be Simple

**1ML insight:**
- Module features can compile to simpler core
- Dependent types not required for modules
- Type-directed elaboration does the work

**Lesson:** Keep core calculus simple, elaborate rich features.

### 5. User Control Matters

**Sterling's explicit casts:**
- Predictability > Convenience
- User orchestrates unification/coercion interaction
- Clear semantics, reliable behavior

**Lesson:** Don't try to be too clever. Let users see what's happening.

---

## Open Questions & Future Directions

### For HWML Specifically

**Q1: How to handle clock domain unification?**
- Are clock domains types or terms?
- Should they participate in full unification?
- Or special-purpose constraint solver?

**Q2: Bit-width inference - how aggressive?**
- Fully infer widths? (`?n : Nat`)
- Or require annotations? (`Signal 8`)
- Hybrid approach? (infer in local scopes)

**Q3: When to flatten structures?**
- Eagerly flatten all structures during elaboration?
- Or lazy flattening on-demand during unification?
- Trade-off: compilation time vs. runtime complexity

### General Research Directions

**1. Parallel Unification**
- Can independent constraints solve in parallel?
- What's the synchronization overhead?
- Applicable to large hardware designs?

**2. Incremental Unification**
- When definition changes, what must re-unify?
- Can we cache partial results?
- Integration with incremental build systems?

**3. Better Postponement Strategies**
- Observational techniques (Kovács WITS 2026)
- Guaranteed progress conditions
- Avoiding infinite postponement

**4. Unification for Quantitative Types**
- Linear/affine/relevant type systems
- Resource tracking during unification
- Application to hardware resource constraints?

---

## Implementation Roadmap for HWML

### Phase 1: Basic Pattern Unification (Current)

**Goal:** Get simple cases working.

**Features:**
- Miller patterns only
- No Σ-types yet
- Basic postponement
- Simple occurs check

**Deliverable:** Can type-check simple dependent functions.

### Phase 2: Σ-Types and Structures

**Goal:** Handle hardware structures/records.

**Add:**
- Abel & Pientka's Σ-type transformations
- η-equality for structures
- Projection elimination
- Flattening transformation

**Test Cases:**
```hwml
structure Signal (w : Nat) where
  data : BitVec w
  valid : Bool

-- Should unify:
?s : Signal ?n
concrete_sig : Signal 8
-- Result: ?n := 8, ?s := concrete_sig
```

### Phase 3: Performance Optimizations

**Goal:** Make it fast enough for real designs.

**Add:**
- Hash consing
- Memoization
- Syntactic equality fast path
- Spine representation
- Optimized occurs check

**Benchmark:** Unify 10,000 hardware signal constraints in <100ms.

### Phase 4: Advanced Features

**Goal:** Research-grade features.

**Consider:**
- Twin types (Tog⁺) for heterogeneous unification
- Explicit casts (Sterling) for subtyping
- Observational postponement (Kovács)
- Type class resolution (Lean-style)

**Decision Point:** Only add if profiling shows need.

---

## References

### Primary Sources

**Abel & Pientka (2011):**
- "Higher-Order Dynamic Pattern Unification for Dependent Types and Records"
- TLCA 2011, LNCS 6690, pp. 10-26
- [Long version](https://www.cse.chalmers.se/~abela/unif-sigma-long.pdf)
- [Implementation in Beluga/Agda]

**Miller (1991):**
- "A logic programming language with lambda-abstraction, function variables, and simple unification"
- Foundation of pattern unification

**Kovács (2020-2026):**
- [Elaboration Zoo](https://github.com/AndrasKovacs/elaboration-zoo)
- Nested pattern unification (with Bocquet, WITS 2023)
- Observational postponement (WITS 2026)
- [Personal website](https://andraskovacs.github.io/)

**Pientka & Pfenning (2003):**
- "Optimizing higher-order pattern unification"
- CADE-19, pp. 473-487
- Linearization technique, 445% speedup

### Implementation References

**Agda:**
- Source: [github.com/agda/agda](https://github.com/agda/agda)
- Modules: `Agda.TypeChecking.Rules.LHS.Unify`, `Agda.TypeChecking.Records`
- Eta-expansion, higher-dimensional unification

**Lean 4:**
- Source: [github.com/leanprover/lean4](https://github.com/leanprover/lean4)
- `src/Lean/Meta/Structure.lean` - Structure elaboration
- Type class resolution, discrimination trees

**Coq (Rocq):**
- [Mathematical Components](https://math-comp.github.io/)
- Packed classes, canonical structures
- Telescopes and coercion chains

**Epigram:**
- [Original site](http://www.e-pig.org/)
- [Epilogue blog](http://mazzo.li/epilogue/)
- Levitation paper, universe of datatypes

### Related HWML Wiki Pages

- [[research/togt-heterogeneous-unification]] - Twin types for heterogeneous unification
- [[research/disentangling-unification-coercion]] - Explicit casts, Kovács's work
- [[research/extensible-elaborator]] - ExEl constraint-based architecture
- [[ADR-002-bidirectional-typing]] - HWML's bidirectional elaboration
- [[ADR-010-metavariable-scoping-constraint-solver]] - Current constraint solver design
- [[entities/nbe]] - Normalization by evaluation (separate from unification)

### Module System References

**ML Modules:**
- Dreyer et al. "A type system for higher-order modules"
- Rossberg "1ML - Core and modules united"
- [F-ing Modules](https://people.mpi-sws.org/~rossberg/f-ing/)

**Mathematical Components:**
- Garillot et al. "Packaging Mathematical Structures"
- [Hierarchy Builder](https://github.com/math-comp/hierarchy-builder)
- Telescopes, packed classes, canonical structures

---

## Conclusion

Unification in dependently-typed languages with structures is **well-understood** but **non-trivial**:

**Core Technique:** Use type isomorphisms to flatten Σ-types into Π-types during unification (Abel & Pientka).

**Performance:** Achievable through multiple optimizations:
- Hash consing (6x)
- Syntactic equality (variable)
- Occurs check optimization (4x+)
- Postponement strategies

**For HWML:**
1. ✅ Start with Abel & Pientka's algorithm
2. ✅ Add Kovács's nested patterns
3. ✅ Implement key optimizations (hash consing, syntactic equality)
4. ❓ Consider twin types if heterogeneous cases arise
5. ❓ Consider explicit casts for hardware coercions

**Key Insight:** Modern dependent type checkers don't treat structures/records as primitive during unification. They transform them into simpler representations, solve, and transform back.

**HWML Advantage:** Hardware structures often have regular patterns → prime candidates for hash consing and memoization!

---

**Last Updated:** 2026-05-04
**Status:** ✅ Comprehensive survey complete
**Confidence:** 0.9 (based on published papers + production implementations)
**Next Steps:**
1. Prototype Abel & Pientka's algorithm in Rust
2. Test on hardware structure examples
3. Profile and optimize hot paths
4. Integrate with HWML elaborator

**Cross-References:**
- [[research/togt-heterogeneous-unification]]
- [[research/disentangling-unification-coercion]]
- [[research/extensible-elaborator]]
- [[ADR-010-metavariable-scoping-constraint-solver]]

