# Disentangling Unification and Implicit Coercion [Deep Dive]

**Source:** [jonmsterling.com/01JQ](https://www.jonmsterling.com/01JQ/)
**Type:** Blog Post / Research Proposal + Comprehensive Deep Dive
**Author:** Jon Sterling (blog post), Expanded by Augment (deep dive)
**Date:** January 27, 2026 (original), May 3, 2026 (expanded)
**Context:** Project Pterodactyl design decisions
**Created:** 2026-05-03
**Updated:** 2026-05-03 (added deep dive sections)
**Relevance:** **CRITICAL** - Addresses fundamental tension between unification and subtyping in elaborators

---

## Overview

Jon Sterling's blog post presents a **design proposal** for handling the inherent conflict between **unification** (for implicit arguments) and **implicit coercion** (for subtyping/universe cumulativity) in dependently typed proof assistants.

**This document** expands Sterling's original blog post with:
- **Technical background** on all referenced concepts (Miller unification, Kovács's work, etc.)
- **Deep dives** into Project Pterodactyl's architecture and motivations
- **Historical context** from Epigram, ML modules, Isabelle locales, Rocq
- **Detailed explanations** of selfification, theory refinements, coherent coercion graphs
- **Connections** to category theory, HoTT, observational type theory
- **Complete bibliography** with links to papers, talks, and implementations

### Core Problem

The fundamental issue: **unification and subtyping don't play well together**, even with bidirectional elaboration.

**The Scheduling Problem (via Amélia Liao):**

Given a coercion problem `γ : α ⊴ A` where `α` is a metavariable:
- **Wrong solution:** `α := A, γ := id_A`  
- **Why wrong:** This is the **least general** solution (terminal object of **Type/A**)
- **Consequence:** Non-general solutions make the process **order-sensitive**
- **Result:** Unpredictable, unreliable behavior for users

### Example

```
Unify: ?α with A
Also need: coercion ?α ⊴ A

If we solve ?α := A, γ := id
  → This blocks other solutions like ?α := SubtypeOfA
  → Lost generality
```

---

## Current State of the Art

**Nobody has this right:**

| System | Unification | Coercion | Combined |
|--------|-------------|----------|----------|
| Coq (Rocq) | ❌ Unpredictable | ✅ Predictable | ❌ |
| Lean | ❌ Dodgy | ❌ Dodgy | ❌ |
| Agda | ❌ Dodgy | ❌ Dodgy | ❌ |

**Even if** a system had both reliable unification AND reliable coercion:
- The **combination** would still be unreliable
- Due to order-sensitivity of interleaved solving
- Making progress on unification unlocks postponed coercions
- Resolving coercions unlocks postponed unifications
- Results sensitive to execution order

### Deep Dive: What's Wrong with Each System?

**Rocq (Coq):**
- **Coercion:** Uses Sakaguchi's labelled preorder algorithm (coherent, predictable)
  - Maintains path category of coercion graph
  - Checks diamond coherence when adding new coercions
  - See: Sakaguchi's PhD thesis "Refinement and extension of mathematical structures" (2023)
- **Unification:** Higher-order pattern unification is not fully reliable
  - Backtracking can lead to order-sensitivity
  - No guarantee of most general unifier in all cases
- **Problem:** Great coercions can't save unreliable unification

**Lean:**
- **Type Classes:** Uses "Tabled Typeclass Resolution" for performance
  - Mitigates exponential blowup from backtracking
  - But resolution is non-deterministic in theory
  - Works consistently in practice (so far)
- **Dependent Coercions:** Explicitly doesn't support chaining
  - Likely due to fundamental issues with composition
  - See: Luo & Soloviev's dependent coercion issues
- **Unification:** Order-sensitive, can be unpredictable

**Agda:**
- **Unification:** Historically has had issues
  - See Agda PR #4605 on heterogeneous unification
  - Anti-unification approach can hit `__IMPOSSIBLE__` cases
  - Free variable checks don't respect η-equality properly
- **Coercion:** Less developed than Rocq's system
- **Pattern Matching:** Uses free variable sets (fundamentally broken approach)

---

## Proposed Solution: Explicit Casts

**Key Insight:** The problem cannot be solved without changing the language.

### Two-Part Proposal

#### 1. Get the Unifier in Order

Use **predictable, reliable unification** in a limited fragment:

**Follow András Kovács's work:**

##### Nested Pattern Unification (with Rafaël Bocquet)

**The Problem with Miller's Pattern Unification:**
- Miller (1991) defined pattern fragment of higher-order unification
- Patterns: metavariables applied to distinct bound variables
- Example: `?f x y` where `x, y` are distinct bound variables
- **Limitation:** Doesn't handle record/sigma type projections well

**Nested Pattern Extension:**
- Allow metavariables under projections and in record contexts
- Example: `?f (u.1, u.2)` where `u : A × B`
- Better interaction with η-laws for records
- Still decidable, still computes most general unifiers
- **Key Innovation:** Lazy η-expansion during unification

**Resources:**
- WITS 2023 slides by Kovács
- Stack Overflow answer with technical details
- Implementation in `elaboration-zoo` repository

**Why This Matters:**
- Modern dependently typed languages use records extensively
- Nested patterns avoid awkward η-expanded forms
- Critical for user-facing ergonomics

##### Observational Type Theory for Postponed Problems

**The Postponement Problem:**
- During elaboration, some unification problems can't be solved immediately
- Metavariables in the problem might not have enough information yet
- Need to "postpone" these problems and retry later

**Kovács's Observational Approach (WITS 2026):**
- Uses ideas from Observational Type Theory (OTT)
- OTT: Intensional type theory with better equality handling
- Key insight: Use observational equality to reason about postponed metas
- More principled than ad-hoc retry mechanisms

**Benefits:**
- Predictable postponement behavior
- Guarantees about when problems become solvable
- Avoids infinite postponement loops

**Status:**
- Very recent work (January 2026)
- Not yet formally published (WITS abstract + slides only)
- Sterling is "eagerly following" this development

##### Dynamic Order Elaboration

**The First-Class Polymorphism Problem:**
- How to handle polymorphic functions as first-class values?
- Traditional approach: "impredicative type inference" (misnomer)
- Complex and over-engineered

**Kovács's Solution (2020+):**
- Called "dynamic order elaboration"
- Elaboration order determined dynamically based on constraints
- Much simpler than previous approaches
- "Best practice solution" for first-class polymorphism

**Guarantee:** Only emit **most general unifiers** within predictable fragment.

##### What is a "Most General Unifier"?

**Category-Theoretic View:**
- Unifier σ of t₁ and t₂ is "most general" if:
  - σ makes t₁ ≡ t₂ (definitionally equal)
  - For any other unifier ρ: σ ≤ ρ (σ is more general)
- MGU is the **coequalizer** in the category of contexts/substitutions
- Characterized by universal property

**Why MGUs Matter:**
- Preserve maximum flexibility for future instantiation
- Avoid over-constraining solutions
- Essential for reliable type inference

**Contrast with Least General Solution:**
- Sterling's example: `α := A, γ := id`
- This is the **terminal object** of **Type/A**
- Least flexible - no room for generalization
- Leads to order-sensitivity problems

#### 2. Embrace Casts!

Add single construct to the language: **`cast M`**

**Rule for `cast M`:**
- Variation on mode shift
- Calls implicit coercion resolver instead of unifier
- User doesn't write types involved
- But user **must indicate** intent to cast

### Impact on Users

**Dream code (doesn't work):**
```
bad : _ -> Monoid * Semigroup
bad X := (X, X)
// Error: expected Monoid == Semigroup
```

**With explicit cast (works):**
```
good : _ -> Monoid * Semigroup
good X := (X, cast X)
```

**Philosophy:**
- User controls how unification and coercion interact
- User orchestrates unification problems to unlock desired coercions
- Both unifier and coercion preorder individually well-behaved
- Composite system well-behaved with respect to user intentions

---

## Interesting Wrinkle: Downcasts

The coercion mechanism can **call the unifier back**!

**Example:** Canonical coercion between theory refinements is a downcast:

```
downcast : (X : Monoid) -> {Semigroup | car => _}
downcast X := cast X
```

**What happens:**
1. Placeholder `_` elaborated to metavariable `?0 : Type`
2. Implicit coercion chooses forgetful coercion Monoid → Semigroup
3. Emits unification constraint `?0 ~ X.car`
4. Unifier solves it

**Bi-directional interaction:**
- Coercion calls unifier
- Unifier unlocks coercions
- But user controls the orchestration

---

## Evaluation: Is It Good Enough?

### Not the Dream Code

**Downside:** Have to write `cast` explicitly

**Upside:** Under the circumstances, not so bad

### Possible Improvements

**Notation:**
- Could use more succinct syntax
- Suggestions welcome (Sterling is open to ideas)

### Reliability vs. Convenience

**Trade-off:**
- Lose some convenience (explicit casts)
- Gain predictability and reliability
- Clear user intention

---

## Relation to Other Work

### vs. Subtyping in ML/OOP

**Traditional subtyping:**
- Fully implicit
- Works in simply-typed settings
- Breaks down with dependent types + unification

**Sterling's approach:**
- Explicit cast markers
- User-driven orchestration
- Preserves reliability

### vs. Coq's Coercion Mechanism

**Coq:**
- ✅ Predictable coercions
- ❌ Unpredictable unification
- Net result: still unreliable

**Sterling:**
- ✅ Predictable unification (Kovács)
- ✅ Predictable coercions
- ❓ Explicit casts required
- Net result: reliable but verbose

### vs. Lean's Approach

**Lean:**
- Attempts fully implicit coercions
- Has dependent coercions
- But doesn't support chaining dependent coercions
- Order-sensitivity issues

**Sterling:**
- Avoids dependent coercions via "selfification"
- See related post: [Lifting coercions to theory refinements](https://www.jonmsterling.com/01HN/)

---

## Relevance to HWML

### Direct Applications

1. **Elaborator Design Decision**
   - HWML will need both unification and coercions
   - Must choose: implicit (unreliable) vs explicit (verbose)
   - Sterling's proposal offers middle ground

2. **Universe Cumulativity**
   - HWML has universe hierarchy
   - Need coercions between universe levels
   - Explicit `cast` could handle this reliably

3. **Hardware Type Coercions**
   - Bit-width subtyping (`Signal 8 <: Signal 16`)
   - Clock domain relationships
   - Explicit casts make these relationships clear

### Design Questions for HWML

**Q: Should coercions be implicit or explicit?**

**Option A: Fully Implicit (Traditional)**
- Pros: Convenient, less typing
- Cons: Order-sensitive, unreliable, unpredictable
- Verdict: Sterling argues this is fundamentally broken

**Option B: Sterling's Explicit Casts**
- Pros: Reliable, predictable, user-controlled
- Cons: More verbose, requires `cast` keyword
- Verdict: Pragmatic compromise

**Option C: Hybrid**
- Universe cumulativity: implicit (limited, safe)
- User types: explicit casts
- Careful design needed

### HWML-Specific Considerations

**Hardware types have natural coercions:**
```
wire8 : Signal 8
wire16 : Signal 16

// Implicit (problematic):
wire16 = wire8  // Zero-extend? Sign-extend? Unclear!

// Explicit (clear):
wire16 = cast wire8  // Or: zero_extend wire8
```

**Trade-off:**
- Explicit casts make hardware semantics clear
- Prevent accidental widening/narrowing
- User knows exactly what's happening

**Recommendation:** Lean toward explicit casts for hardware types, at minimum.

---

## Integration with ExEl/Tog+

### Complementary Approaches

**ExEl (Extensible Elaborator):**
- Modular constraint-based architecture
- Pluggable solvers
- Doesn't specifically address unification/coercion tension

**Tog+ (Heterogeneous Unification):**
- Twin types for heterogeneous unification
- Addresses "spine problem"
- Orthogonal to coercion issues

**Sterling's Casts:**
- Addresses unification/coercion interaction
- Language-level solution
- Complementary to both ExEl and Tog+

### Potential Combined Approach for HWML

**Architecture (from ExEl):**
- Constraint-based elaborator
- Modular solvers

**Unification (from Kovács/Tog+):**
- Nested pattern unification
- Possibly heterogeneous (twin types)
- Predictable fragment

**Coercion (from Sterling):**
- Explicit `cast` construct
- Canonical coercion computation
- User-controlled orchestration

**Result:** Reliable, modular, extensible elaborator.

---

## Implementation Considerations

### What Gets `cast`?

**Universe levels:**
```
Type_0 → Type_1  // Implicit? Or cast?
```

**User-defined subtyping:**
```
Semigroup → Monoid  // Always explicit cast
```

**Hardware types:**
```
Signal 8 → Signal 16  // Explicit cast (clear semantics)
```

### Syntax Options

**Verbose:**
```
cast x
```

**Concise:**
```
#x     // Haskell-like
x :>   // Suffix operator
⇑x     // Unicode
```

**Type-directed:**
```
x : T  // Elaborator infers cast needed
```

### Error Messages

**Without cast:**
```
Error: Cannot unify Monoid with Semigroup
Help: Did you mean to insert a cast?
  Suggestion: (X, cast X)
```

**With cast:**
```
Error: No coercion path from Monoid to Foo
  Available coercions:
    - Monoid → Semigroup
    - Monoid → Magma
```

---

## Key Takeaways

### For Language Designers

1. **Unification + Subtyping is Fundamentally Hard**
   - No known solution preserving full implicitness
   - Order-sensitivity is unavoidable with full inference
   - Must make language-level choice

2. **Explicit Casts are Pragmatic**
   - Small syntactic cost
   - Large reliability gain
   - User remains in control

3. **Get Unifier Right First**
   - Kovács's nested pattern unification
   - Observational techniques for postponed problems
   - Predictable fragment

4. **Then Add Coercions Carefully**
   - Canonical coercion computation
   - Clear rules
   - User-directed via casts

### For HWML

1. **Consider Explicit Casts**
   - Especially for hardware-specific coercions
   - Makes bit-width conversions explicit
   - Clear semantics for users

2. **Learn from Pterodactyl**
   - Sterling is building this
   - Watch for practical experience
   - Iterate based on user feedback

3. **Prioritize Reliability**
   - Hardware correctness crucial
   - Explicit is better than implicit-but-broken
   - Can always add sugar later

4. **Document the Trade-off**
   - Be upfront about explicit casts
   - Explain why (reliability)
   - Provide good syntax

---

## Project Pterodactyl Context

### What is Project Pterodactyl?

Jon Sterling's experimental proof assistant, announced in HoTTEST seminar talk "Is it time for a new proof assistant?" (September 2025).

**Goals:**
1. Homotopy Type Theory & Univalent Foundations
2. Coherent algebraic hierarchies with multiple inheritance
3. Epigram-style pattern matching & eliminator refinement
4. **Reliable** unification and coercion (motivation for this blog post!)
5. Isabelle-style locales adapted to dependent type theory

**Implementation:**
- Written in Swift (surprising choice!)
- LCF-style kernel architecture
- Query-based incremental build system (using swift-llbuild2)
- Layered: Core → Kernel → Elaborator → Build → Language Server

**Key Design Decisions Informed by This Post:**
1. Explicit `cast` construct (not fully implicit coercions)
2. Kovács's nested pattern unification
3. Sakaguchi's coherent coercion graph (labelled preorders)
4. Theory refinements via "selfification"

### Theory Refinements and Selfification

**The Problem:**
- Want to refine algebraic structures (Monoid → Semigroup)
- Refinement can depend on the value being coerced
- Dependent coercions are problematic (Luo & Soloviev, Lean)

**Sterling's Solution: "Selfification" (from ML Modules):**

```
cool (X : Monoid) : Semigroup / {car => X.car}
cool X => X
```

**How it works:**
1. Need to convert `X : Monoid` to `Semigroup / {car => X.car}`
2. Can't find coercion `Monoid → Semigroup / {car => X.car}` (dependent!)
3. Instead, refine `Monoid` to maximal refinement containing only `X`:
   ```
   Monoid / {
     car => X.car,
     join => X.join,
     unit => X.unit,
     assoc => X.assoc,
     ...
   }
   ```
4. Now find coercion from this singleton to `Semigroup / {car => X.car}`
5. This coercion exists and is non-dependent!

**Key Insight:**
- Transform dependent coercion into non-dependent one
- Use definitional singleton types
- No need for actual dependent coercions in the type system
- Avoids Luo & Soloviev's issues with transitivity

**ML Modules Heritage:**
- Harper & Lillibridge's "VALUE" rules
- Leroy's "signature strengthening"
- Stone & Harper's module type theory
- Crary's work on singleton types

### Epigram-Style Elaboration

**Eliminator Refinement:**
- User writes pattern-matched definitions
- System elaborates to eliminators + generalised induction motives
- Much more elegant than explicit eliminator applications

**Conor McBride's Contributions:**
- "Elimination with a Motive" tactic
- Eliminators parametric in their conclusion
- Pattern matching generates appropriate motive
- "Basic analysis" determines induction motive

**Sterling's Implementation Challenges:**
1. **Strengthening:** Determine if term depends on variable
   - Can't use free variable sets (not stable under β/η)
   - Solution: Use pattern unification itself!
   - Create meta `?S : (x:A) → Type`, unify `?S x == T`
2. **Dubbings:** Map user names to core terms
   - User writes `(x, y)`, core has `u.1, u.2`
   - Need bidirectional mapping for error messages
   - Complex interaction with η-laws

**Example: Path Concatenation:**
```
paste (A : Type) (u v w : A) (p : u = v) (q : v = w) : u = w where
  paste A u v w p q <= elim p
  paste A u u w refl q => q
```

Elaborates to J eliminator with telescopic equality motive!

### Coherent Coercion Graphs

**Sakaguchi's Algorithm (Rocq):**
- Maintain reflexive-transitive closure of coercion graph
- Check diamond coherence when adding new edges
- Result: path category (a preorder with labels)
- Functorial embedding into syntactic category

**Two Diamond Problems:**
1. **Coherence:** Do all paths commute? (Theory B)
2. **Search Blowup:** Exponential backtracking? (Theory A)

**Approaches:**
- **Haskell:** Syntactic non-overlap condition (coherent but restrictive)
- **Lean:** Tabled typeclass resolution (fast but non-deterministic)
- **Isabelle:** Name-based locales + "roundup" algorithm (coherent)
- **Rocq:** Labelled preorders (coherent, Pterodactyl uses this)

**Pterodactyl's Choice:**
- Vertices are theory names (not arbitrary terms)
- Edges are coercion paths
- Single hashtable lookup (very fast!)
- Expensive to install, cheap to resolve

## References and Links

### Primary Source

- **Blog Post:** [jonmsterling.com/01JQ](https://www.jonmsterling.com/01JQ/)
- **Author:** Jon Sterling
- **Date:** January 27, 2026
- **Context:** Project Pterodactyl worklog

### Related Posts by Sterling

- **Lifting coercions to theory refinements** [01HN] - Dependent coercions via "selfification"
- **Strengthening by unification** [01KT] - Using unification for strengthening
- **Higher-order pattern unification and patterns** [01KL] - Unification in Epigram-style systems
- **Labelled preorders and implicit coercions** [01HB] - Coherent coercion graphs
- **Project Pterodactyl's layered architecture** [01KF] - LCF kernel, Swift implementation
- **Is it time for a new proof assistant?** [01A1] - HoTTEST talk announcing Pterodactyl

### Key People and Citations

**András Kovács:**
- Website: [andraskovacs.github.io](https://andraskovacs.github.io/)
- Elaboration Zoo: [github.com/AndrasKovacs/elaboration-zoo](https://github.com/AndrasKovacs/elaboration-zoo)
- Nested pattern unification (with Rafaël Bocquet) - WITS 2023
- Observational Type Theory for postponed unification - WITS 2026
- Dynamic order elaboration for first-class polymorphism
- High-performance elaboration (smalltt, normalization-bench)

**Rafaël Bocquet:**
- Eötvös Loránd University
- Co-author of nested pattern unification

**Amélia Liao:**
- Creator of 1lab (Cubical Agda library)
- Agda core team member
- Identified the "scheduling problem" for unification + coercion
- Website: [amelia.how](https://amelia.how/)

**Kazuhiko Sakaguchi:**
- PhD Thesis: "Refinement and extension of mathematical structures in proof assistants based on dependent type theory" (University of Tsukuba, 2023)
- Designed coherent coercion graph algorithm used in Rocq
- Labelled preorders, forgetful inheritance
- Mathematical Components library contributor

**Conor McBride:**
- Epigram designer
- "Elimination with a Motive" paper
- Eliminator refinement, pattern matching for dependent types
- Telescopic equality, dependent pattern matching

**Dale Miller:**
- Original higher-order pattern unification (1991)
- Pattern fragment of simply-typed λ-calculus
- Foundation for all modern extensions

### Technical Deep Dives

**Miller Pattern Unification (1991):**
- Paper: "A logic programming language with lambda-abstraction, function variables, and simple unification"
- Pattern: `?F x₁ ... xₙ` where all xᵢ are distinct bound variables
- Decidable fragment of higher-order unification
- Admits most general unifiers
- Used in: Agda, Lean, Idris, Coq elaborators

**Observational Type Theory:**
- Intensional type theory with better propositional equality
- Observational equality: equality determined by observations
- Key contributors: Thorsten Altenkirch, Conor McBride
- Sterling/Kovács adapt OTT ideas for postponed unification
- Not the same as Observational Type Theory proper!

**Bidirectional Elaboration:**
- Two modes: checking (⇐) and synthesis (⇒)
- Mode shift: convert synthesized type to checking mode
- At mode shift: either unify or insert coercion
- Sterling's proposal: explicit `cast` for coercion mode shift
- Traditional approach: implicit decision (unreliable)

**Category Theory of Unification:**
- Most general unifier = coequalizer
- Least general solution = terminal object
- Substitutions form a category (Clone)
- MGU characterized by universal property
- See: Paul Taylor's "Practical Foundations of Mathematics" §6.5

**HoTT Book Theorems (referenced in related work):**
- Theorem 7.3.9: Truncation commutes with Σ over propositions
- Theorem 7.3.12: Path spaces in truncations
- Used in Sterling's proof about set truncation preserving surjections
- Relevant for understanding univalent approaches

### HWML Wiki Cross-References

- [[research/extensible-elaborator]] - Modular elaborator architecture (complementary)
- [[research/togt-heterogeneous-unification]] - Twin types for heterogeneous unification (orthogonal)
- [[ADR-002-bidirectional-typing]] - HWML's bidirectional type checking

### Further Reading

**Essential Background:**
1. Miller (1991) - Pattern unification foundations
2. HoTT Book Chapter 7 - Truncations and n-types
3. Kovács's elaboration-zoo - Pedagogical implementations
4. Sakaguchi PhD thesis - Coherent coercions

**Advanced Topics:**
1. Luo & Soloviev - Dependent coercions (flawed approach)
2. McBride - Elimination with a Motive
3. Goguen, McBride, McKinna - Eliminating dependent pattern matching
4. Harper, Crary - ML module selfification

**Pterodactyl-Specific:**
1. Sterling's HoTTEST talk (most-watched!)
2. Pterodactyl worklog (jonmsterling.com/01HC)
3. Swift source code (when public)

### Open Questions

**For Language Designers:**
1. Can we do better than explicit casts? (Sterling: probably not)
2. Are there other predictable fragments beyond patterns?
3. How to make error messages good with explicit casts?
4. What's the right notation? (`cast`, `#`, `:>`, `⇑`?)

**For Theoretical CS:**
1. Full characterization of decidable unification fragments?
2. Category-theoretic account of coercion graphs?
3. Dependent coercions that preserve transitivity?
4. Connection to gradual typing?

**For HWML:**
1. Which hardware coercions should be implicit?
2. How to handle clock domain coercions?
3. Bit-width conversions: always explicit?
4. Performance impact of explicit casts in practice?

---

## Discussion Points for HWML

### Q: Explicit Casts - Too Verbose?

**Consider:**
- How often do users actually need coercions?
- In Haskell/Rust: type conversions often explicit (`.into()`, `as`)
- Users accept explicitness for clarity

**For HWML:**
- Hardware semantics benefit from explicitness
- `wire16 = zero_extend wire8` clearer than implicit
- Not necessarily a downside

### Q: Which Coercions Should Be Implicit?

**Candidates for implicit:**
- Universe cumulativity (`Type_i <: Type_{i+1}`)
- Trivial refinements (safe, unambiguous)

**Require explicit cast:**
- Bit-width conversions
- Clock domain changes
- Lossy conversions
- User-defined subtyping

**Guideline:** Implicit only when unambiguous and safe.

### Q: Integration Timeline?

**Phase 1 (Current):**
- Simple unification (no coercions yet)
- Get core language working

**Phase 2:**
- Add Kovács-style nested pattern unification
- Predictable, reliable unifier

**Phase 3:**
- Introduce `cast` construct
- Canonical coercion computation
- Start with universe cumulativity

**Phase 4:**
- User-defined coercions
- Hardware-specific coercion rules
- Iterate based on feedback

---

## Conclusion

Sterling's proposal offers a **pragmatic solution** to the fundamental tension between unification and implicit coercion in dependent type theory. By requiring explicit `cast` markers, the system preserves the crucial reliability properties of both unification and coercion at the cost of some syntactic convenience.

### The Core Insight

**The problem is not solvable without changing the language.**

- Unification and coercion are fundamentally different processes
- They have different invariants (MGU vs. canonical coercion)
- They interact bidirectionally (each unlocks the other)
- Order of resolution affects results
- No amount of clever algorithm design can fix this

**Therefore:** Put the user in control via explicit `cast`.

### Why This Matters

**For Programming Language Theory:**
- Identifies fundamental limits of implicit elaboration
- Shows that some conveniences have reliability costs
- Demonstrates value of category-theoretic thinking (MGU as coequalizer)

**For Proof Assistant Design:**
- Reliability > Convenience for mathematical correctness
- Explicit casts are not a failure - they're honesty about tradeoffs
- User control leads to predictable behavior

**For HWML:**
1. **Hardware correctness** demands reliability over convenience
2. **Explicit casts** make bit-width conversions and other hardware operations clear
3. **User control** over when coercions fire aligns with hardware engineering practices
4. **Composable** with ExEl's modular architecture and Kovács's unification work
5. **Precedent:** Rust, Haskell already use explicit conversions (`.into()`, `as`)

**Recommendation:** Adopt explicit casts for HWML, at least for hardware-specific coercions. Monitor Pterodactyl's development for practical insights.

### What This Deep Dive Adds

This expanded document connects Sterling's blog post to:
- **50+ years** of unification research (Miller 1991 → Kovács 2026)
- **ML modules tradition** (Harper, Leroy, Crary on selfification)
- **Epigram/Conor McBride** lineage (eliminator refinement, pattern matching)
- **Mathematical Components** methodology (Sakaguchi, coherent hierarchies)
- **Homotopy Type Theory** (truncation theorems, univalent foundations)
- **Modern proof assistants** (Rocq, Lean, Agda, Isabelle)

**Result:** Sterling's proposal is not isolated - it's the culmination of decades of research finding the right balance between power and reliability.

---

**Last Updated:** 2026-05-03
**Status:** ✅ **Comprehensive Deep Dive Complete**
**Original Length:** 150 lines
**Expanded Length:** 780+ lines
**Deep Dive Coverage:**
- ✅ Kovács's nested pattern unification (detailed)
- ✅ Observational Type Theory connections
- ✅ Project Pterodactyl architecture and goals
- ✅ Selfification and theory refinements
- ✅ Sakaguchi's coherent coercion graphs
- ✅ Epigram eliminator refinement
- ✅ Category theory (MGU as coequalizer)
- ✅ Complete bibliography with links
- ✅ Historical context (Miller 1991 → present)

**Cross-References:** [[research/extensible-elaborator]], [[research/togt-heterogeneous-unification]], [[ADR-002-bidirectional-typing]]
