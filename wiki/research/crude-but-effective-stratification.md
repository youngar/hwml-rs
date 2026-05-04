# Crude but Effective Stratification [McBride 2011-2012]

**Source:** Multiple blog posts by Conor McBride (Epilogue blog, 2011-2012)  
**Type:** Research Proposal / Language Design Technique  
**Author:** Conor McBride  
**Date:** June 17, 2011 - 2012  
**Formalization:** "An Order-Theoretic Analysis of Universe Polymorphism" (Favonia, Angiuli, Mullanix, POPL 2023)  
**Created:** 2026-05-03  
**Relevance:** High - Lightweight solution to universe polymorphism in dependent type theory

---

## Overview

"Crude but Effective Stratification" is Conor McBride's proposal for handling **universe polymorphism** in dependently typed proof assistants. The core idea is remarkably simple: define everything at the lowest possible level where it can live, then subject the entire type theory to **functoriality in displacement operations**, allowing developments to be **shunted upward** in the hierarchy as needed.

**The Problem:** Predicative type theories need a stratified hierarchy of universes (Set₀, Set₁, Set₂, ...) to avoid Russell's paradox. But manually tracking universe levels is tedious and error-prone.

**McBride's Solution:** Every top-level definition is implicitly polymorphic in a "secret" universe level variable, which can be instantiated with a **displacement operation** that shifts all levels uniformly.

---

## The Problem: Universe Polymorphism

### Why We Need Universe Hierarchies

In predicative type theories (Luo's UTT, Agda, Coq without impredicativity):
- Types are organized in a cumulative hierarchy: **Set₀ : Set₁ : Set₂ : ...**
- Prevents **Set : Set** (which leads to Girard's paradox)
- Each type has a **level** in the hierarchy

### The Pragmatic Pain

**Example: Lists**
```agda
List : Set₀ → Set₀
List : Set₁ → Set₁
List : Set₂ → Set₂
-- Need infinitely many copies!
```

**Current approaches:**
1. **Set : Set hack** - Inconsistent but convenient (Epigram 1)
2. **Explicit level polymorphism** - Type-correct but verbose (Agda, modern Coq)
3. **Typical ambiguity** - Infer levels silently (Coq classic)

**Problems:**
- Explicit polymorphism is syntactically heavy
- Typical ambiguity hides what's going on
- Universe constraints leak into interfaces
- Nested polymorphism gets complicated

---

## Crude but Effective Stratification

### Core Idea

**Write definitions at the lowest level, then displace them upward:**

1. Define `List` at level 0:
   ```
   List : Set₀ → Set₀
   ```

2. Apply displacement operation **`(−)⇑`** to get higher levels:
   ```
   List⇑   : Set₁ → Set₁
   List⇑⇑  : Set₂ → Set₂
   List⇑ⁿ  : Setₙ → Setₙ
   ```

3. All top-level definitions have an implicit displacement parameter
4. Elaborator infers the right displacement for each use

### Displacement Operations

**Simplest version:** Just shift levels by n
```
t⇑ⁿ = t[Setᵢ ↦ Setᵢ₊ₙ for all i]
```

**More general (Favonia et al.):** Abstract displacement algebra
- Identity displacement: `id`
- Composition: `d₁ ∘ d₂`
- Can have displacements other than just `+n`

**Key property:** Functoriality
```
(t₁ t₂)⇑ = t₁⇑ t₂⇑
(λx. t)⇑ = λx. t⇑
...
```

---

## Example: The Benefit

### Without Crude but Effective

**Agda with explicit levels:**
```agda
List : {ℓ : Level} → Set ℓ → Set ℓ
map  : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {B : Set ℓ₂} 
     → (A → B) → List A → List B
```

**Problem:** Level parameters proliferate, clutter type signatures

### With Crude but Effective

**Write at level 0:**
```
List : Set₀ → Set₀
map  : {A B : Set₀} → (A → B) → List A → List B
```

**Use at higher levels:**
```
-- Elaborator inserts displacements
xs : List⇑² Nat⇑²   -- Works at level 2
```

**Benefit:** Clean definitions, no explicit level management

---

## Two Ways to Think About It

### 1. Secret Polymorphism

Every top-level definition `f : T` is implicitly:
```
f<ℓ> : T[Set₀ ↦ Setₗ]
```

At use sites, elaborator infers the right `ℓ`.

**Like:** Implicit universe parameters, but zero syntactic burden

### 2. Functorial Displacement

The entire signature (all top-level definitions) forms a **functor** from the displacement monoid to itself:
```
Σ⇑ : Signature → Signature
```

**Like:** Lifting a module to higher universe levels

---

## Jon Sterling's Explanation (2025)

From Sterling's blog post on Project Pterodactyl:

> **"Their idea is to define everything at the lowest possible level where it can live, but then subject the entire type theory to a functoriality in displacement operations, which allows developments to be shunted upward in the hierarchy as-needed."**

**Tightest instantiation principle:**
- When you need universes in linear relationship (U, U+, U++)
- Pick the tightest possible instantiation
- Later use displacement to create extra room between universes

**Sterling's take for Pterodactyl:**
- Starts with explicit polymorphism (simpler to implement first)
- Open to revisiting crude but effective later
- Wants to see usability limitations before adding general displacements

---

## Formalization: Displacement Algebras

### Favonia, Angiuli, Mullanix (POPL 2023)

**"An Order-Theoretic Analysis of Universe Polymorphism"**

Formalizes McBride's idea using **displacement algebras**:

**Definition:** A displacement algebra is a (strict partial) order (D, ≤) with:
- **Identity**: `id ∈ D` with `id ≤ d` for all `d`
- **Composition**: `d₁ ∘ d₂ ∈ D` for all `d₁, d₂`
- **Monoid laws**: Identity and associativity
- **Monotonicity**: `d₁ ≤ d₂ ⟹ d ∘ d₁ ≤ d ∘ d₂`

**Classic example (integers):**
```ocaml
module I = struct
  type t = int  (* displacements are integers *)
  let compare = Int.compare
  let zero = 0  (* identity displacement *)
  let plus = (+)  (* composition *)
end
```

**Key theorem:** Any universe hierarchy can be embedded in a displacement algebra and hence implemented via crude but effective stratification.

### Mugen Library

Favonia et al. provide **OCaml library** for universe levels based on displacement algebras:
- `Mugen.Shift`: Example displacement algebras
- `Mugen.Shift.Int`: Classic integer displacements
- `Mugen.Syntax`: Syntax of universe levels
- Used in proof assistant implementations

---

## Comparison to Other Approaches

### vs. Agda's Explicit Levels

**Agda:**
```agda
Level : Set
_⊔_   : Level → Level → Level  -- max
suc   : Level → Level           -- successor
```
Levels form a type, with explicit max/suc operations

**Crude but Effective:**
- Levels are NOT a type (no abstraction over them)
- Displacements are syntactic operations
- Zero user-facing level management

**Trade-off:**
- Agda: More expressive (can compute with levels)
- C.B.E.: Simpler (less to think about)

### vs. Coq's Typical Ambiguity

**Coq (classic):**
- Infer universe levels silently
- User rarely sees them
- Sometimes inference fails mysteriously

**Crude but Effective:**
- Also infers levels (via displacement)
- But displacement is a syntactic operation (more predictable)
- Explicit when needed (write `⇑` explicitly)

### vs. Set : Set Hack

**Set : Set (Epigram 1, early prototypes):**
- Inconsistent (leads to paradoxes)
- Very convenient for programming
- Can't be trusted for proofs

**Crude but Effective:**
- **Consistent** (predicative)
- **Almost as convenient** (write code once, use everywhere)
- Can be trusted

---

## Negative Displacements

**Extension by Favonia et al.:** Displacements can be **negative integers**!

**Idea:**
- Syntactically, can write `Set₋₁, Set₋₂, ...`
- Semantically, these don't exist
- But finite developments only use finite levels
- Negative indices are "placeholders" that get shifted positive

**Example:**
```
Define List at level -1:
  List : Set₋₁ → Set₋₁

Use at level 0:
  List⇑  : Set₀ → Set₀

Use at level 3:
  List⇑⁴ : Set₃ → Set₃
```

**Benefit:** Even more flexibility in arranging relative levels

---

## McBride's Original Motivation (2011)

From the Epilogue blog post "Crude but Effective Stratification":

### The Problem He Was Solving

**Epigram context:**
- Wanted predicative fragment of Luo's UTT
- Had been hacking with Set : Set as "holding pattern"
- Knew it was inconsistent
- But existing stratification approaches were **pragmatically unsatisfying**

**Quote:**
> "I always dodged implementing the stratified hierarchy of universes, hacking in the (fun but) inconsistent Set : Set as a holding pattern. It's not that I don't care about consistency. It's more that I'm unhappy with the pragmatics of many of the treatments I've seen and wanted to think a bit more about the problem."

### The Insight

**Start simple, lift as needed:**

1. Define at level 0:
   ```
   Vec : Nat → Set₀ → Set₀
   ```

2. Need higher level? Apply displacement:
   ```
   Vec⇑ⁿ : Nat → Setₙ → Setₙ
   ```

3. Elaborator does this automatically

**Quote:**
> "It's not fancy, It's not complicated. It's crude but effective, and we'll find out in time whether it's extra abstraction will buy you anything essential."

---

## Implementation Considerations

### For Language Designers

**Elaboration algorithm needs to:**
1. Track displacement constraints during type checking
2. Solve constraint system to find minimal displacements
3. Insert displacement operations explicitly in core language

**Constraint generation:**
```
If Γ ⊢ t : T  and we need  t : T⇑ᵈ
Generate constraint: d ≥ identity
```

**Constraint solving:**
- Find minimal displacement satisfying all constraints
- Similar to universe level inference in Agda
- But simpler: just monotone functions on levels

### Core Language

**Surface language:**
```
List : Set → Set
```

**Core language (after elaboration):**
```
List<d> : Set⇑ᵈ → Set⇑ᵈ
```

**All displacement operations made explicit in core**

---

## Applications to HWML

### Direct Relevance

HWML will need universe stratification for:
1. **Predicative type theory** (avoid paradoxes)
2. **Hardware type hierarchies** (signals, protocols, modules)
3. **Polymorphic hardware generators**

### HWML-Specific Benefits

**Bit-width polymorphism:**
```
Signal : Nat → Set₀ → Set₀
-- Use at different levels:
Signal⇑² : Nat → Set₂ → Set₂
```

**Clock domain abstraction:**
```
Protocol : ClockDomain → Set₀ → Set₀
-- Displace to work with higher-level types
```

**Hierarchical hardware:**
```
Module : Set₀ → Set₁  -- Modules contain types
-- Displacement lets you nest modules
```

### Integration Strategy

**Phase 1 (Current):**
- Start with explicit universe levels (like Agda)
- Get type system working
- Understand universe constraints in practice

**Phase 2:**
- Implement displacement algebra
- Add implicit displacement parameters
- Migrate to crude but effective

**Phase 3:**
- Optimize constraint solving
- Add syntactic sugar for common patterns
- Profile performance

**Decision Point:**
- Monitor Pterodactyl's development
- See if crude but effective proves valuable in practice
- Consider hybrid (explicit + displacement)

---

## Limitations and Trade-offs

### What You Give Up

**1. No Abstraction Over Displacements**
- Can't write functions that take displacements as arguments
- Can't compute displacements dynamically
- **Impact:** Less expressive than full level polymorphism

**2. All Definitions Displaced Together**
- Can't selectively displace individual definitions
- The "signature" moves as a unit
- **Impact:** Less fine-grained control

**3. Implementation Complexity**
- Elaborator must track displacement constraints
- Constraint solving can be non-trivial
- **Impact:** More complex than Set : Set hack

### What You Gain

**1. Simplicity for Users**
- Write definitions once, at lowest level
- Use anywhere, elaborator handles displacement
- **Impact:** Much less syntactic clutter

**2. Consistency**
- Predicative, avoids paradoxes
- Can be trusted for proofs
- **Impact:** Sound foundation

**3. Pragmatic Middle Ground**
- More convenient than explicit levels everywhere
- More predictable than typical ambiguity
- **Impact:** Good balance of safety + usability

---

## Relationship to Other Work

### Agda's Level System

Agda has a type `Level` with operations:
- `lzero : Level`
- `lsuc : Level → Level`
- `_⊔_ : Level → Level → Level` (max)

**Connection to crude but effective:**
- Crude but effective is SIMPLER (no Level type)
- But Agda's system is MORE EXPRESSIVE (can abstract over levels)
- Could implement crude but effective ON TOP of Agda's levels

### Universe Polymorphism in Rocq/Coq

Coq (now Rocq) has evolved sophisticated universe management:
- Algebraic universes (constraints)
- Cumulative inductive types
- Template polymorphism

**Connection:**
- Rocq is very expressive but complex
- Crude but effective is simpler, less powerful
- Trade-off: expressiveness vs. simplicity

### Idris 2 Universe Handling

Idris 2 uses:
- Explicit universe levels when needed
- Type-directed erasure
- QTT (Quantitative Type Theory) integration

**Connection:**
- Orthogonal concerns (linearity vs. universes)
- Could combine crude but effective with QTT

---

## Key Insights

### For Type Theory

**1. Functoriality is Key**
- Viewing signatures as functors enables displacement
- Category theory provides clean formalization
- Displacement algebras are the right abstraction

**2. Syntactic vs. Semantic**
- Displacement is syntactic (text transformation)
- But preserves semantics (types stay well-formed)
- Clean separation of concerns

**3. Predicativity Need Not Be Painful**
- Can have predicative + convenient
- Don't have to choose between sound and usable
- Language design matters

### For Language Implementers

**1. Start Simple**
- McBride's original proposal is remarkably simple
- Extensions (negative indices, algebra) add power later
- Don't over-engineer from the start

**2. Elaboration is the Key**
- Most complexity is in elaborator, not core language
- Good constraint solving makes or breaks usability
- Invest in good error messages

**3. Pragmatics Matter**
- Mathematical elegance is not enough
- How does it feel to use day-to-day?
- McBride's motivation was pragmatic frustration

### For HWML

**1. Hardware Has Natural Hierarchies**
- Signals ⊂ Protocols ⊂ Modules ⊂ Systems
- Clock domains, bit widths, resource types
- Crude but effective fits this naturally

**2. Don't Fight the Type System**
- If stratification is needed, embrace it
- Crude but effective makes it painless
- Users focus on hardware, not universe levels

**3. Iterate Based on Experience**
- Start explicit (Agda-style)
- Measure where universe management hurts
- Add crude but effective if it helps

---

## References and Links

### Primary Sources

- **Original Blog Post:** ["Crude but Effective Stratification"](https://mazzo.li/epilogue/index.html?p=857.html) (Epilogue blog, June 17, 2011)
- **Author:** Conor McBride
- **Context:** Epigram 2 language design

### Formalization

- **POPL 2023 Paper:** ["An Order-Theoretic Analysis of Universe Polymorphism"](https://favonia.org/files/mugen.pdf)
- **Authors:** Kuen-Bang Hou (Favonia), Carlo Angiuli, Reed Mullanix
- **Code:** [Mugen OCaml library](https://github.com/plurigrid/mugen)
- **Key Contribution:** Displacement algebras, proof of universality

### Jon Sterling's Discussion

- **Blog Post:** ["Fuss-free universe hierarchies › What about universe polymorphism?"](https://www.jonmsterling.com/01HZ/)
- **Subsection:** ["McBride's Crude but Effective Stratification"](https://www.jonmsterling.com/01I4/)
- **Date:** October 6, 2025
- **Context:** Project Pterodactyl design decisions

### Related Work

- **Luo's UTT:** "An Extended Calculus of Constructions" (Zhaohui Luo, 1990)
- **Epigram:** "The View from the Left" (McBride & McKinna, 2004)
- **Agda Levels:** "Practical Erasure in Dependently Typed Languages" (various)

### HWML Wiki Cross-References

- [[research/disentangling-unification-coercion]] - Sterling's Pterodactyl design (mentions crude but effective)
- [[research/extensible-elaborator]] - ExEl elaborator architecture (could use C.B.E. for universes)
- [[research/togt-heterogeneous-unification]] - Tog+ unification (orthogonal to universe management)

---

## Discussion Points for HWML

### Q: Should HWML Use Crude but Effective Stratification?

**Pros:**
- Simpler for users (write code once)
- Consistent (predicative type theory)
- Proven approach (Favonia et al. formalized it)
- Fits hardware hierarchies naturally

**Cons:**
- Implementation complexity (elaborator)
- Less expressive than full level polymorphism
- Relatively new (less battle-tested than Agda's approach)

**Recommendation:** Start with Agda-style explicit levels, migrate to crude but effective if pain points emerge.

### Q: How Does This Relate to Hardware-Specific Type Features?

**Natural fit:**
- Bit-width hierarchies (Bit, Word₈, Word₁₆, ...)
- Clock domain polymorphism (sync → async promotion)
- Resource type levels (Linear, Affine, Unrestricted)

**Could combine:**
- Crude but effective for universe stratification
- Separate mechanism for hardware-specific subtyping
- Orthogonal concerns, both valuable

### Q: Performance Implications?

**Elaboration time:**
- Displacement constraint solving adds overhead
- But likely small compared to other type checking
- Need to profile in practice

**Core language size:**
- Explicit displacements in core = larger terms
- Could impact compilation time
- Possible mitigation: erase displacements post-type-checking

**Developer experience:**
- Faster to write (less level management)
- Potentially slower to elaborate
- Net positive if elaboration is fast enough

---

## Conclusion

Crude but Effective Stratification is an elegant solution to a practical problem: how to have predicative type theory without drowning in universe level management. By treating signatures as functors over displacement algebras, McBride found a sweet spot between the unsafe convenience of Set : Set and the cumbersome explicitness of fully-general universe polymorphism.

**For HWML**, the approach is particularly attractive because:
1. **Hardware has natural hierarchies** that map well to universe stratification
2. **Users want to focus on circuits**, not type theory plumbing
3. **Formalization exists** (Favonia et al.) proving it's sound
4. **Implementation path is clear** (start explicit, add displacement later)

The key decision is **when** to adopt it, not **whether**. Starting with explicit levels (Phase 1) gives us experience with where universe management hurts. Adding crude but effective (Phase 2) addresses those pain points with minimal disruption to user code.

**Next Steps:**
1. Implement basic universe stratification (Agda-style)
2. Track where users struggle with level management
3. Prototype displacement algebra elaboration
4. Measure usability improvement
5. Decide on adoption based on empirical evidence

**"It's crude, but effective, and we'll find out in time whether its extra abstraction will buy you anything essential."** — Conor McBride, 2011

---

**Last Updated:** 2026-05-03
**Status:** ✅ Comprehensive research summary complete
**Length:** 400+ lines
**Coverage:**
- ✅ McBride's original proposal (2011-2012)
- ✅ Formalization by Favonia et al. (POPL 2023)
- ✅ Jon Sterling's perspective (Pterodactyl 2025)
- ✅ Comparison to Agda, Coq, other systems
- ✅ Implementation considerations
- ✅ HWML-specific analysis
- ✅ Complete bibliography

**Cross-References:** [[research/disentangling-unification-coercion]], [[research/extensible-elaborator]], [[research/togt-heterogeneous-unification]]
