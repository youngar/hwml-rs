# Mixfix Operators, Type-Directed Parsing, and Constraint-Based Elaboration

**Created:** 2026-05-06
**Type:** Research Survey (Deep Dive)
**Status:** In Progress
**Confidence:** 0.85

---

## Executive Summary

This research explores the intersection of three critical parsing/elaboration challenges:

1. **Mixfix operator parsing** (Agda's approach using precedence graphs)
2. **Type-based overloading** (how to pause elaboration until types are known)
3. **Universal dot notation** (Lean's type-directed field resolution)

The key insight is that all three require mechanisms to **pause** or **suspend** elaboration/parsing until type information becomes available, then **resume** when constraints are solved. This creates a new kind of constraint: **suspended elaboration constraints**.

---

## 1. Mixfix Operators: The Agda Approach

### 1.1 Core Paper: Danielsson & Norell (2008)

**Reference:** "Parsing Mixfix Operators" (IFL 2008)
**URL:** https://www.cse.chalmers.se/~nad/publications/danielsson-norell-mixfix.pdf

**Key Contributions:**
- Grammar scheme parameterized by a **precedence relation** (DAG, not total order)
- Modular precedence relations (can be composed incrementally)
- Precedence-correct expressions **by construction** (using dependent types)
- Two approaches: acyclic (left/right non-recursive) and cyclic (allows both)

**Agda's Two-Phase Parsing:**
1. **Pre-parse:** Treat everything as function application → rose trees
2. **Scope-directed parse:** For each symbol sequence, generate a dedicated parser based on:
   - Which operator parts are in scope
   - Relative precedences from fixity declarations
   - Associativity information

**Problem:** Current Agda implementation may not be efficient enough for complex fixity schemes (per the `notes/fixity-declarations` file).

### 1.2 Modern Developments (2023-2026)

**Recent Agda Issues:**
- **#7727** (2025): Exponential behavior in pattern parser when operator names used as variables
  - Fix: Only consider pattern-relevant operators during pattern parsing
- **#8228/#8232** (2025): Parse errors with DISPLAY pragma and mixfix operators
  - Fix: Stop pruning non-constructor operators from DISPLAY patterns

**Key Insight:** Mixfix parsing is **scope-sensitive** - you need to know which operators are in scope to build the right parser.

---

## 2. Type-Based Overloading and Suspended Constraints

### 2.1 The Fundamental Challenge

**Problem:** When encountering an overloaded symbol `f`:
- You need type information to resolve which `f` is meant
- But type information may not be available yet (unification in progress)
- And you can't wait forever (need to make progress)

**Traditional Approaches:**
- **Backtracking** (slow, exponential blowup)
- **HM(X)** (extend Hindley-Milner with constraint domain X)
- **Bidirectional** (push expected types down, pull inferred types up)

### 2.2 Modern Solutions: Suspended/Frozen Constraints

**Key Papers:**

1. **"Omnidirectional Type Inference"** (arXiv 2511.10343, 2024)
   - Constraints solved in **any order**
   - **Suspend** when progress requires known type info
   - **Resume** when other constraints supply it
   - **Suspended match constraints** as primitive
   - **Incremental instantiation** for let-polymorphism

2. **"The Simple Essence of Overloading"** (Benes et al., 2025)
   - Flow-based variational type-checking
   - Overloads represented as **choices** (variational types)
   - Cleanly separates: constraint collection → solving → overload resolution
   - No backtracking needed in type checker

3. **"Frozen Inference Constraints"** (Scherer, Pottier - Inferno library)
   - **Frozen constraints** for OCaml constructor disambiguation
   - Suspend constraint `x ≤ τ` when τ contains unresolved variable α
   - Generate fresh variable γ for the "frozen part" ⟨α⟩β
   - **Unfreeze** once α is unified




### 2.3 Type-Directed Overloading: The Chargueraud Approach (2025)

**Paper:** "Typechecking of Overloaded Symbols" (hal-04859446, 2025)
**First algorithm for:**
- Resolution guided by **both** arguments **and** result type
- Support for **polymorphic types**
- Type inference (except polymorphism inference)

**Two-Pass Algorithm:**
1. **First pass:** ML-style unification, introduce "not-yet-constrained" types for unresolved symbols
2. **Second pass:** Iteratively resolve overloaded symbols using accumulated type constraints

**Application:** Mathematical notation, ML with overloaded literals/functions/constructors/fields

---

## 3. Lean's Universal Dot Notation

### 3.1 Core Mechanism

**Resolution Rule (Post PR #6189, 2024):**
```
If x : S, then x.f resolves S.f relative to root namespace
(affected by export/open)
```

**Key Features:**
- Works for **any** function (not just structure projections)
- `TARGET.f ARG1 ARG2 ...` → find leftmost argument of type T in T.f
- Can **unfold definitions** during resolution
- Uses **C3 linearization** for method resolution order (like Python)

### 3.2 Type-Directed Resolution

**The Challenge (Issue #1629, 2024):**
```lean
def Function.swap {α β} {γ : α → β → Sort _}
  (f : (a : α) → (b : β) → γ a b) : (b : β) → (a : α) → γ a b :=
  f a b

-- Can't use f.swap because elaborator selects f for the implicit type family!
```

**Solutions Explored:**
- `selfParam` pragma to mark which argument to use
- Named `self` arguments (currently being explored)

**Structure Resolution Order (PR #5770, 2024):**
- Navigate to **all** parent structures (not just subobjects)
- C3 algorithm for resolution order
- Relaxed mode tolerates inconsistencies
- Strict mode warns on inconsistent parent orderings

### 3.3 Implementation Details

**Key Lean 4 Files:**
- `Lean/Structure.lean`: computeStructureResolutionOrder
- `Lean/Elab/StructInst.lean`: Structure instance elaboration
- `Lean/ProjFns.lean`: Projection function metadata
- `Lean/PrettyPrinter/Delaborator/FieldNotation.lean`: Pretty printing

**Dot Notation Resolution:**
1. Infer type of `x` in `x.f`
2. Unfold definitions if needed to find structure type S
3. Walk resolution order for S (C3 linearization of all parents)
4. For each candidate namespace, try to resolve S.f
5. Check if S appears in the type of some argument to S.f
6. Apply remaining arguments

---

## 4. Constraint-Based Elaboration Architecture

### 4.1 Lean's Elaborator (Avigad et al., 2016)

**Paper:** "The Lean Elaborator"
**URL:** https://www.andrew.cmu.edu/user/avigad/Papers/constr.pdf

**Components:**
- Higher-order unification
- Ad-hoc overloading (more flexible than type classes)
- Insertion of coercions
- Type class inference
- Tactic invocation
- Computational reduction

**Constraint Types:**
- **Unification constraints:** enforce typing
- **Choice constraints:** overload resolution (finite set of possibilities)
- **Type class constraints:** instance search

**Pre-processing Phase:**
- Elaborate partial terms with metavariables (holes)
- Generate constraints
- Mark "easy" vs "hard" constraints

**Solving Phase:**
- Constraint propagation
- Unification (pattern fragment + heuristics)
- Backtracking for choice constraints


### 4.2 Idris Elaborator Reflection (Christiansen, 2016)

**Key Idea:** Expose elaboration primitives as a type of computations

**TT (Core Language):**
- Holes: placeholders not yet filled in
- Guesses: like let bindings, but no reduction (elaborator controls shape)

**Elaboration Monad:**
- Captures proof state
- Collection of tactics for updating/refining
- Can be **invoked by users** (elaborator reflection)

**Benefits:**
- DSLs use same elaboration technology as language itself
- Code reuse across: elaboration → type checking → execution
- Programmable elaboration strategies

### 4.3 ExEl: Extensible Constraint-Based Elaboration (2024)

**Paper:** "ExEl: Building an Elaborator Using Extensible Constraints" (ECOOP 2024)
**Code:** https://research.tudelft.nl/en/datasets/code-underlying-the-publication-exel

**Architecture:**
- **Open datatype** of constraints
- **Plugin system** for solvers working on constraints
- Each feature = one module
- Modular elaboration architecture

**Key Innovation:** Constraints and solvers can be extended without modifying core

---

## 5. The Suspended Elaboration Constraint

### 5.1 Core Idea

**What we need:** A constraint that says "pause elaboration of this syntax tree until type variable α is resolved."

**Analogy to existing work:**

| Domain | Suspension Mechanism | Resume Trigger |
|--------|---------------------|----------------|
| **Overloading** | Frozen constraint `x ≤ τ` when τ has unresolved α | α gets unified |
| **Let-polymorphism** | Suspended generalization (Omnidirectional) | Unification resolves dependencies |
| **Dot notation** | Defer resolution until type of `x` known | Type inference provides structure type |
| **Mixfix parsing** | Defer operator parsing until scope known | Scope analysis completes |
| **Our goal** | Suspend elaboration until types resolve | Constraint solver unifies type variables |

### 5.2 Design Sketch

**Constraint Type:**
```rust
enum Constraint {
    Unify(Type, Type),
    Instance(TypeClass, Type),
    Choice(Symbol, Vec<Candidate>),
    // NEW:
    SuspendedElab {
        syntax: SyntaxTree,
        blocked_on: Vec<MetaVar>,
        resume: impl FnOnce(Solution) -> CoreExpr,
    }
}
```

**Elaboration Flow:**
1. Encounter ambiguous syntax (overloaded op, dot notation, etc.)
2. Create metavariables for unknown types
3. Emit `SuspendedElab` constraint
4. Continue elaborating other parts
5. Constraint solver unifies types
6. Resume suspended elaborations with solutions

### 5.3 Applications

**Type-Directed Mixfix Parsing:**
```
Expression: a + b * c
Could parse as: (a + b) * c  or  a + (b * c)
```
If `+` and `*` are overloaded, precedence might depend on types!

**Lean-Style Dot Notation:**
```
x.foo.bar
```
- Need type of `x` to resolve `foo`
- Need type of `x.foo` to resolve `bar`
- But type of `x` might not be known yet (unification in progress)

**Type-Directed Operator Sections:**
```
(+ 1) : Int -> Int   vs   (+ 1) : Float -> Float
```
Can't elaborate until return type is known.

---

## 6. Combining Mixfix + Type-Direction + Dot Notation

### 6.1 The Grand Challenge

**Imagine:**
```
(x.field1 +ᵢ y.field2) *ᶠ z.field3
```

Where:
- `+ᵢ` is integer addition (precedence depends on context)
- `*ᶠ` is float multiplication
- `.field1`, `.field2`, `.field3` require type-directed resolution
- Parentheses might not be needed if precedence is right
- But precedence might depend on types!

**Dependencies:**
- Can't parse operators without knowing their types (for type-directed precedence)
- Can't resolve dot notation without knowing structure types
- Can't know types without elaborating
- Can't elaborate without parsing!

**Solution:** Iterative refinement with suspended constraints.

### 6.2 Proposed Algorithm

**Phase 1: Conservative Parse**
- Parse with default precedences
- Insert metavariables for all ambiguous constructs
- Emit suspended constraints for:
  - Operator precedence decisions
  - Dot notation resolutions
  - Overload choices

**Phase 2: Type Inference**
- Run constraint solver
- Unify types as much as possible
- Incrementally resolve suspended constraints
- May trigger re-parsing if precedence changes!

**Phase 3: Re-elaboration**
- For any suspended constraints now solvable, resume elaboration
- May discover new type information → more unification
- Repeat until fixed point

**Termination:** Bounded by number of syntax nodes × type variables.


---

## 7. Key References

### 7.1 Mixfix Operators

1. **Danielsson & Norell (2008)** - "Parsing Mixfix Operators" (IFL 2008)
   - https://www.cse.chalmers.se/~nad/publications/danielsson-norell-mixfix.pdf
   - Formalized in Agda: https://www.cse.chalmers.se/~nad/publications/danielsson-norell-mixfix/

2. **Danielsson (2010)** - "Total Parser Combinators"
   - https://dl.acm.org/doi/10.1145/1932681.1863585

3. **Agda Issues** (2024-2025)
   - #7727: Pattern parser performance
   - #8228/#8232: DISPLAY pragma with mixfix

### 7.2 Type-Directed Overloading

4. **Benes et al. (2025)** - "The Simple Essence of Overloading"
   - https://se.cs.uni-tuebingen.de/publications/benes2025overloading.pdf
   - Flow-based variational type-checking

5. **Chargueraud (2025)** - "Typechecking of Overloaded Symbols"
   - https://chargueraud.org/research/2025/overloading/overloading.pdf
   - Bidirectional algorithm with two passes

6. **Frozen Constraints** (Scherer, Pottier)
   - https://gallium.inria.fr/~scherer/research/constraints/frozen-constraints/short-abstract.pdf

7. **Omnidirectional Type Inference** (2024)
   - https://arxiv.org/pdf/2511.10343
   - Suspended match constraints, incremental instantiation

### 7.3 Elaboration & Constraint Solving

8. **Avigad et al. (2016)** - "The Lean Elaborator"
   - https://www.andrew.cmu.edu/user/avigad/Papers/constr.pdf

9. **Christiansen (2016)** - "Elaborator Reflection" (PhD thesis)
   - https://davidchristiansen.dk/david-christiansen-phd.pdf

10. **Pottier (2014)** - "Inferno: A Constraint-Based Type Inference Library"
    - Constraint generation + solving separation

11. **Liesnikov & Cockx (2024)** - "ExEl: Extensible Elaboration"
    - https://research.tudelft.nl/en/datasets/code-underlying-the-publication-exel

### 7.4 Lean's Dot Notation

12. **Lean 4 PRs:**
    - #5770 (2024): C3 resolution order for all parents
    - #6189 (2024): Affected by export/open
    - #9634 (2025): Use name resolution for dot ident

13. **Lean 4 Issues:**
    - #1629 (2024): Dot notation with type families
    - #3467: Generalized field notation improvements

---

## 8. Research Gaps and Future Directions

### 8.1 Open Questions

1. **Performance:** How expensive is iterative re-elaboration?
   - Can we bound the number of re-parses?
   - Are there incremental parsing techniques that help?

2. **Type-Directed Precedence:** Should operator precedence depend on types?
   - Example: `Matrix +` might bind tighter than `Scalar +`
   - How to keep this comprehensible to programmers?

3. **Error Messages:** When suspended constraints fail to resolve:
   - How to explain which types are still ambiguous?
   - How to suggest where type annotations would help?

4. **Interaction with Type Classes:**
   - Can suspended elaboration help with type class resolution?
   - Example: `x.map f` where `map` requires a `Functor` instance

### 8.2 Connections to HWML

**Immediate Applications:**
- **Module projections:** `Module.Type.field` → need type to resolve path
- **Overloaded literals:** `0` could be `Nat`, `Int`, `Fin n`, etc.
- **Tactic elaboration:** Tactics that inspect types during elaboration

**Design Questions:**
- Should HWML support mixfix operators? (Agda-style vs Lean-style)
- Should dot notation be universal? (like Lean) or structure-only? (like Coq)
- How to balance flexibility vs simplicity?

**Implementation Strategy:**
1. Start with simple elaboration (no suspension)
2. Add basic constraint solver (unification + type classes)
3. Implement suspended constraints for dot notation
4. Extend to overloading if needed
5. Consider mixfix if there's demand

---

## 9. Related Work to Explore Further

### 9.1 Papers to Read

- **"Type Inference Logics"** (ACM SIGPLAN 2024)
  - Machine-checked verification of type inference with elaboration
  - https://dl.acm.org/doi/10.1145/3689786

- **"When Subtyping Constraints Liberate"** (POPL 2024)
  - SuperF: first-class polymorphism with subtyping
  - Novel approach to constraint solving

- **"InferType"** (ECOOP 2024)
  - DSL embedded in Java for type inference
  - Uses Z3 SMT solver for constraint solving

### 9.2 Systems to Study

- **Scala 3:** DOT calculus with intersection types
- **TypeScript:** Structural typing with conditional types
- **Haskell GHC:** OutsideIn(X) constraint solver
- **OCaml:** Modular implicits and type-directed disambiguation
- **Agda:** Full mixfix implementation (for comparison)
- **Idris 2:** Elaborator reflection in practice

### 9.3 Techniques to Investigate

- **Variational type-checking:** Represent choices as first-class values
- **Constraint HDL:** How hardware description languages handle elaboration
- **Algebraic subtyping:** MLsub's approach to constraint solving
- **Gradual typing:** Suspending type checks to runtime

---

## 10. Actionable Next Steps

1. **Read the Danielsson-Norell paper carefully** (it's been fetched)
   - Understand the precedence graph construction
   - Study the cyclic vs acyclic approaches
   - Look at the Agda formalization

2. **Implement prototype constraint solver** with:
   - Basic unification
   - Suspended constraints primitive
   - Simple resumption mechanism

3. **Design HWML's elaboration architecture:**
   - Decide on constraint language
   - Specify elaboration monad
   - Plan for extensibility (ExEl-style?)

4. **Prototype dot notation:**
   - Start with structure projections only
   - Add parent projection resolution
   - Extend to arbitrary functions (Lean-style)

5. **Write ADR:**
   - Document design decisions
   - Explain tradeoffs (flexibility vs simplicity)
   - Specify implementation strategy

---

**Next Research Session:** Focus on constraint solver architecture and incremental instantiation details.
