# Tog⁺: Practical Heterogeneous Unification for Dependent Type Checking

**Source:** `external/togt/` (prototype implementation)  
**Type:** Research Prototype + PhD Thesis  
**Author:** Víctor López Juan (Chalmers/Gothenburg)  
**Year:** 2021  
**Thesis:** [research.chalmers.se/publication/527051](https://research.chalmers.se/publication/527051)  
**Paper:** "Practical Dependent Type Checking using Twin Types" (TyDe 2020)  
**Created:** 2026-05-03  
**Relevance:** High - Addresses heterogeneous unification and "spine problem" in dependent type checking

---

## Overview

Tog⁺ (pronounced "tog-tee") is a **prototype implementation** demonstrating **heterogeneous unification using twin types** for dependently typed languages. It addresses the problem of unifying terms whose types are not yet known to be equal - the so-called **"spine problem"**.

### Core Problem

Traditional dependently typed language unifiers (Agda, Idris, Lean, Coq) require that **types are equal before unifying terms**:

```
Unify: t1 ≈ t2   requires   type(t1) = type(t2)
```

But during elaboration, we often need to **unify terms before proving their types equal**:
- Function application with implicit arguments
- Solving for metavariables in extended contexts
- Type-directed elaboration

**Problem:** This creates a chicken-and-egg situation that can lead to:
- Internal errors (`__IMPOSSIBLE__` cases in Agda)
- Overly conservative type checkers
- Rejection of valid programs

---

## Solution: Twin Types

### Gundry and McBride's Approach

Gundry and McBride (2012) proposed using **twin types** for constraints:

- **Twin types**: `(A₁ ‡ A₂)` - a constraint that can have *two* types simultaneously
- **Twin variables**: Variables with two types
- **Heterogeneous unification**: Unify `t1 : A1` with `t2 : A2` even when `A1 ≠ A2`

### Tog⁺ Simplification

López Juan's key contribution was **simplifying** twin types:

1. **Remove twin variables** - Only use twin types for constraints
2. **Type-agnostic syntactic equality** - Fast check that works without type info
3. **Practical implementation** - Tested in full type checker

**Benefit:** Easier to implement in existing type checkers (especially Agda).

---

## Key Technical Innovations

### 1. Heterogeneous Spine Unification

The "spine problem" occurs when unifying:
```
f : (x : A) → B x
y : C

Unify:  f a  ≈  f b
```

where `type(a)` might not be known equal to `type(b)` yet.

**Tog⁺ solution:** Allow constraints with twin types, delay type equality check.

### 2. Type-Agnostic Syntactic Equality

Fast syntactic check that doesn't require type information:
```haskell
syntacticEqual :: Term -> Term -> Bool
syntacticEqual t1 t2 = 
  alphaEquivalent t1 t2  -- No type information needed
```

**Impact:** Significant performance improvement - avoids expensive type comparisons.

### 3. Hash Consing + Memoization

To handle large terms efficiently:
- **Hash consing (HC)**: Share identical subterms in memory
- **Memoization**: Cache unification results

**Performance:** 131s → 22s on setoid example with HC&M enabled.

---

## Implementation: Tog⁺ Prototype

### Based on Tog

Extends the **Tog** type checker (a minimal Agda-like language) with:
- Heterogeneous unification
- Twin type constraints
- Optimizations (hash consing, memoization)

### Language Features

Supports:
- Dependent types (Pi, Sigma)
- Indexed inductive types  
- Type-in-type (for simplicity)
- No termination checking (prototype)

### Architecture

```
Surface Syntax
     ↓
Elaborator (raises heterogeneous constraints)
     ↓
Twin Type Constraints: (t1 : A1) ≈ (t2 : A2)
     ↓
Heterogeneous Unifier
     ↓
Core Terms
```

---

## Performance & Results

### Benchmark: Setoid Example

Problem that Coq, Idris, Lean, and Matita **cannot type-check**:
- Large sigma types
- Complex equality proofs
- Deep unification problems

**Results:**

| System | HC&M | Time | Result |
|--------|------|------|--------|
| Tog⁺ (hetero) | No  | 131s | ✅ Success |
| Tog⁺ (hetero) | Yes | 22s  | ✅ Success |
| Tog (homo)    | No  | timeout | ❌ Fail |
| Tog (homo)    | Yes | timeout | ❌ Fail |
| Agda 2.6.1    | -   | ~25s | ✅ Success |
| Coq/Idris/Lean/Matita | - | - | ❌ Cannot handle |

**Conclusion:** Heterogeneous unification **enables** type-checking this example, with performance comparable to Agda.

### Test Suite

Includes examples demonstrating:
- `Goal1_WellTypedness` - Basic well-typedness
- `Goal2_OutOfOrder` - Out-of-order unification
- `Language_test0_Type` through `test6_Setoid` - Increasing complexity
- Setoid reasoning (the challenging case)

---

## Comparison to Other Approaches

### vs. Agda's Approach

**Agda (pre-4605):**
- Homogeneous unification (types must be equal first)
- Uses anti-unification to handle spine problem
- Can hit `__IMPOSSIBLE__` cases (#3027, #1467, #2709)

**Tog⁺:**
- Heterogeneous unification
- No anti-unification needed
- Handles more cases gracefully

**Impact:** Agda PR #4605 (2020) proposed integrating heterogeneous unification inspired by this work.

### vs. ExEl Anti-Unification

**ExEl (Extensible Elaborator):**
- Uses anti-unification variables as communication channels
- Unification + anti-unification unified
- "Well-typed modulo constraints"

**Tog⁺:**
- Uses twin types for heterogeneous constraints
- Separates type equality from term unification
- More focused on the unification problem itself

**ExEl critique of Tog⁺:**
- Claims Agda's separate anti-unification was bug-prone
- Argues unifying anti-unification with unification is cleaner
- But acknowledges heterogeneous unification handles "sufficiently broad class of problems"

**Trade-offs:**
- Tog⁺: More focused, specifically targets spine problem
- ExEl: More general, modular elaborator architecture

---

## Usage (Running Tog⁺)

### Compilation

```bash
cd external/togt
stack build
```

### Running Examples

**Recommended configuration (Tog⁺ with all features):**
```bash
stack exec tog -- \
  --synEquality 2 \
  --physicalEquality \
  --solver W \
  --noCheckElaborated \
  --fastElaborate \
  --termType HC4 \
  examples/Language_test6_Setoid.agda
```

**Without syntactic equality rule:**
```bash
stack exec tog -- \
  --solver W \
  --noCheckElaborated \
  --fastElaborate \
  --termType HC4 \
  --synEquality 0 \
  examples/Language_test6_Setoid.agda
```

**Helper scripts (Unix-like systems):**
```bash
./togt.sh examples/Language_test6_Setoid.agda
./togt-nosyneq.sh examples/Language_test6_Setoid.agda
```

### Comparing with Agda

```bash
agda -iexamples -iagda-prelude \
  --type-in-type \
  --without-K \
  --no-termination-check \
  --ignore-interfaces \
  --no-positivity-check \
  examples/Language_test6_Setoid.agda
```

---

## Theoretical Foundations

### Twin Type Constraints

A constraint in Tog⁺ has the form:
```
Γ ⊢ (t₁ : A₁) ≈ (t₂ : A₂)
```

Where:
- `t₁`, `t₂` are terms to unify
- `A₁`, `A₂` are their **potentially different** types
- Validity requires eventually showing `A₁ ≡ A₂`

### Unification Rules (Simplified)

**Syntactic equality (fast path):**
```
Γ ⊢ t : A    Γ ⊢ t : B
─────────────────────── (if t syntactically equal)
Γ ⊢ (t : A) ≈ (t : B)
```

**Heterogeneous decomposition:**
```
Γ ⊢ (A₁ : Type) ≈ (A₂ : Type)
Γ, x : A₁ ⊢ (B₁ : Type) ≈ (B₂ : Type)
────────────────────────────────────────
Γ ⊢ ((x:A₁)→B₁ : Type) ≈ ((x:A₂)→B₂ : Type)
```

**Metavariable instantiation (heterogeneous):**
```
Γ ⊢ ?α : A₁    Γ ⊢ t : A₂
────────────────────────── (if occurs-check passes)
?α := t
Γ ⊢ (?α : A₁) ≈ (t : A₂)
```

### Correctness

**Thesis proves:**
1. **Soundness**: If unification succeeds, the constraint is valid
2. **Completeness**: Can solve all solvable constraints (within decidable fragment)
3. **Termination**: Unification algorithm terminates

**Key insight:** Delaying type equality check doesn't compromise soundness.

---

## Relation to HWML

### Direct Applications

1. **Heterogeneous Unification**
   - HWML's elaborator could use twin types for constraints
   - Handle cases where types not yet proven equal
   - Fewer internal errors, more programs accepted

2. **Spine Problem**
   - Relevant for HWML's dependent types
   - Function application with implicit arguments
   - Metavariable solving in extended contexts

3. **Performance Optimizations**
   - Hash consing for large hardware types
   - Memoization for repeated unification
   - Syntactic equality for fast path

### Integration with ExEl

Could **combine** approaches:
- **ExEl architecture**: Modular constraint-based elaborator
- **Tog⁺ technique**: Heterogeneous twin-type unification as one solver

Example:
```haskell
-- Twin type constraint (from Tog⁺)
data TwinTypeConstraint e =
  TwinTypeConstraint Term Type Term Type

-- Handler checks if heterogeneous unification applicable
twinTypeHandler :: HandlerType
twinTypeHandler constr = ...

-- Solver uses Tog⁺ algorithm
twinTypeSolver :: SolverType
twinTypeSolver constr = do
  let (TwinTypeConstraint t1 ty1 t2 ty2) = constr
  -- Apply heterogeneous unification
  heteroUnify t1 ty1 t2 ty2
```

### HWML-Specific Considerations

**Hardware types complicate unification:**
- Clock domain annotations
- Bit widths in types
- Resource constraints

**Twin types could help:**
```
Unify:  Signal 8  ≈  Signal ?n
```
where bit width `?n` not yet determined but unification can proceed.

---

## Limitations

### 1. Prototype Only

- Not production-ready
- Limited language features
- Type-in-type (unsound)
- No termination/positivity checking

### 2. Performance Issues

- Some test cases become **slower** with heterogeneous unification (#4044)
- Size types sometimes fail
- Requires careful engineering for production use

### 3. Standard Library Impact

When integrated into Agda (PR #4605):
- Some implicit arguments needed explicit annotation
- Two cases in stdlib required changes
- Indicates potential breaking changes

### 4. Complexity

- More complex than homogeneous unification
- Requires twin type infrastructure
- Harder to reason about for users

---

## Key Takeaways

### For Language Implementers

1. **Heterogeneous Unification is Viable**
   - Can be implemented efficiently
   - Handles cases homogeneous unifiers cannot
   - Performance comparable to or better than alternatives

2. **Twin Types Work in Practice**
   - Simpler than twin variables
   - Can integrate into existing type checkers
   - Proven correct

3. **Optimizations Matter**
   - Hash consing + memoization crucial
   - Syntactic equality rule gives big speedup
   - Engineering as important as theory

4. **Trade-offs Exist**
   - Some cases get slower
   - May require user-visible changes
   - Not a silver bullet

### For HWML

1. **Consider for Elaborator**
   - Could adopt twin type constraints
   - Especially useful for hardware-specific types
   - Combine with ExEl architecture

2. **Performance Techniques**
   - Hash consing for hardware types (often large/repetitive)
   - Memoization for repeated checks
   - Fast syntactic equality path

3. **Integration Strategy**
   - Start with homogeneous unification
   - Add heterogeneous as extension
   - Measure performance impact

4. **Research Opportunity**
   - Apply twin types to hardware domain
   - Novel constraints (clock domains, bit widths)
   - Potential publication

---

## References and Links

### Primary Sources

- **PhD Thesis (2021):** "Practical Heterogeneous Unification for Dependent Type Checking"
  [research.chalmers.se/publication/527051](https://research.chalmers.se/publication/527051)

- **TyDe Paper (2020):** "Practical Dependent Type Checking using Twin Types"
  [cse.chalmers.se/~nad/publications/lopez-juan-danielsson-tyde2020.html](http://www.cse.chalmers.se/~nad/publications/lopez-juan-danielsson-tyde2020.html)

- **Code:** `external/togt/` in HWML repository
  Original: [github.com/bitonic/tog](https://github.com/bitonic/tog) (base)

### Related Work

- **Gundry & McBride (2012):** "A Framework for Elaborating Dependently Typed Programs" - Original twin types
- **Agda PR #4605:** Proposal to integrate heterogeneous unification
- **ExEl Paper:** Mentions Tog⁺ anti-unification critique

### HWML Wiki Cross-References

- [[research/extensible-elaborator]] - Complementary elaborator architecture
- [[ADR-002-bidirectional-typing]] - HWML's type checking approach
- [[entities/nbe]] - Normalization technique (separate from unification)

---

## Discussion Points for HWML

### Q: Should HWML Use Twin Types?

**Pros:**
- More flexible unification
- Handle more valid programs
- Performance benefits (with optimizations)
- Proven correct in thesis

**Cons:**
- Added complexity
- Some cases slower
- Prototype not production-ready
- Requires significant engineering

**Recommendation:** Monitor Agda's integration (PR #4605). If successful in Agda, consider for HWML Phase 3+.

### Q: Heterogeneous vs. ExEl Anti-Unification?

**Twin Types (Tog⁺):**
- Focused on unification problem
- Delays type equality
- Proven correct

**Anti-Unification (ExEl):**
- Part of larger architecture
- Communication channels
- Unification + anti-unification unified

**HWML Could:**
- Use ExEl architecture (modular solvers)
- Implement heterogeneous unification as one solver
- Get best of both approaches

### Q: Performance in Practice?

**Evidence:**
- Tog⁺: 22s with optimizations (comparable to Agda)
- Handles cases other systems cannot
- But some regressions on other cases

**For HWML:**
- Hardware types often large → hash consing helps
- Many repeated checks → memoization helps
- Need careful profiling

### Q: Integration Timeline?

**Phase 1 (Current):**
- Simple homogeneous unification
- Get basic language working

**Phase 2:**
- Profile unification bottlenecks
- Identify cases needing heterogeneous unification

**Phase 3:**
- Prototype twin type constraints
- Measure performance impact
- Decide on adoption

---

## Conclusion

Tog⁺ demonstrates that **heterogeneous unification using twin types** is both theoretically sound and practically viable for dependently typed languages. By allowing terms to be unified before their types are proven equal, it handles the "spine problem" that causes issues in traditional type checkers.

For HWML, twin types offer an intriguing approach to handling complex unification scenarios, especially with hardware-specific type features. Combined with ExEl's modular architecture, it could provide a robust foundation for the elaborator.

**Next Steps:**
1. Review full thesis for technical details
2. Experiment with Tog⁺ prototype on hardware-like examples
3. Consider hybrid approach (ExEl + twin types)
4. Monitor Agda's heterogeneous unification integration

---

**Last Updated:** 2026-05-03
**Status:** Complete summary of Tog⁺ research
**Cross-References:** [[research/extensible-elaborator]], [[ADR-002-bidirectional-typing]], [[entities/nbe]]
