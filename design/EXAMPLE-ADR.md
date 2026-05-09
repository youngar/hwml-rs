# Example ADR: What Wiki Pages Would Look Like

**Created:** 2026-05-02  
**Purpose:** Show concrete examples of wiki pages that would be generated

---

## Example 1: Architecture Decision Record

This would be generated from `design/ARCHITECTURE.md`:

```markdown
# ADR-001: LCF-Style Trusted Kernel

**Status:** Approved  
**Date:** 2026-03-12  
**Phase:** Phase 1 (Complete)  
**Confidence:** 0.95

## Context

HWML is a dependently-typed hardware description language. Type safety is critical 
because incorrect types can lead to synthesis errors or hardware bugs. We need a 
way to ensure that every term in the core language is well-typed.

**Constraints:**
- Must support bidirectional type checking
- Must integrate with async elaboration (metavariable solving)
- Must be verifiable/auditable for correctness
- Performance: type checking happens frequently

## Alternatives Considered

### Option 1: Unchecked Construction (Unsafe)
- **Pros:** 
  - Maximum flexibility
  - Best performance
  - Simple implementation
- **Cons:** 
  - No safety guarantees
  - Bugs can create ill-typed terms
  - Hard to debug type errors
- **Verdict:** Rejected - safety is paramount for hardware

### Option 2: Runtime Type Checking
- **Pros:**
  - Catch errors at term construction
  - Flexible construction
- **Cons:**
  - Runtime overhead on every construction
  - Error messages far from source
  - Can still construct invalid terms if checks have bugs
- **Verdict:** Better but not sufficient

### Option 3: LCF-Style Kernel (Chosen)
- **Pros:**
  - Type safety enforced at compile time by Rust
  - Only valid terms can be constructed
  - Single trusted module (easy to audit)
  - Zero runtime overhead
- **Cons:**
  - More complex API
  - Less flexibility (intentional)
  - Requires disciplined design
- **Verdict:** Best fit for HWML's safety requirements

### Option 4: Proof-Carrying Terms (Over-engineered)
- **Pros:**
  - Mathematical proof of correctness
  - Ultimate verification
- **Cons:**
  - Massive implementation complexity
  - Performance overhead
  - Overkill for our needs
- **Verdict:** Interesting but unnecessary

## Decision

Use an **LCF-style trusted kernel** where:
1. All `Syntax<'db>` constructors are `pub(crate)` within `hwml-core`
2. Only the `kernel` module can construct terms
3. Kernel enforces bidirectional typing rules
4. Kernel returns typed evidence tokens: `CheckedTerm`, `SynthesizedTerm`, `WellFormedType`

## Rationale

The LCF approach gives us type safety for free via Rust's type system. A term of 
type `CheckedTerm<'db>` is **proof** that the term was type-checked against a 
known type. This proof is checked at compile time, not runtime.

By restricting term construction to the kernel module, we create a small trusted 
computing base (TCB). If the kernel is correct, the entire type system is sound.

This pattern comes from the ML family of theorem provers (LCF, HOL, Isabelle, Coq) 
where the kernel is the only module that can construct theorems. We apply the same 
principle to dependently-typed term construction.

## Implementation

**Module structure:**
```rust
// hwml-core/src/syn.rs
pub struct Syntax<'db> { ... }

impl Syntax<'db> {
    // Constructors are pub(crate) - only kernel can call
    pub(crate) fn lambda(...) -> Self { ... }
    pub(crate) fn app(...) -> Self { ... }
}

// hwml-core/src/kernel/mod.rs
pub struct CheckedTerm<'db>(RcSyntax<'db>);
pub struct SynthesizedTerm<'db>(RcSyntax<'db>, RcValue<'db>);

pub fn check_lambda<'db>(
    ctx: &mut KernelContext<'db>,
    param_ty: WellFormedType<'db>,
    body: impl FnOnce(&mut KernelContext<'db>) -> Result<CheckedTerm<'db>>,
) -> Result<CheckedTerm<'db>> {
    // Enforce lambda typing rule
    // Construct Syntax::lambda only if rule satisfied
}
```

**Crate:** `hwml-core`  
**Key files:**
- `src/kernel/mod.rs` - Kernel module
- `src/kernel/judgements.rs` - Typing rules
- `src/kernel/tokens.rs` - Evidence tokens
- `src/syn.rs` - Syntax (constructors pub(crate))

## Consequences

### Positive
- **Type safety:** Impossible to construct ill-typed terms
- **Auditability:** Only kernel needs deep review
- **Zero cost:** Safety enforced at compile time
- **Clear API:** Evidence tokens make type checking explicit
- **Rust synergy:** Uses Rust's type system for proof

### Negative
- **API complexity:** Elaborator must use kernel API, can't construct terms directly
- **Learning curve:** Contributors need to understand the pattern
- **Rigidity:** Can't "hack around" kernel for experiments (intentional)

### Trade-offs
- Chose **safety over flexibility**
- Chose **compile-time checking over runtime checking**
- Chose **small TCB over distributed checking**

## Challenges Encountered

1. **Async elaboration:** Kernel functions need to be async to wait on metavariables
   - Solution: `async fn` in kernel, cooperative scheduling
   
2. **Error reporting:** Type errors deep in kernel need good source locations
   - Solution: `SourceRange` tracking, metavariable creation locations

3. **Performance:** Concerned about overhead of evidence tokens
   - Result: Zero-cost abstractions, tokens are compile-time only

## Sources

- **Primary:** `design/ARCHITECTURE.md`
- **Research:**
  - LCF: "Edinburgh LCF" (Gordon, Milner, Wadsworth, 1979)
  - HOL kernel design
  - Coq kernel architecture
- **Discussion:** Internal design review, 2026-03-10

## Related

- [[ADR-002: Bidirectional Typing]] - Uses kernel's typed tokens
- [[ADR-003: Async Elaboration]] - How kernel integrates with metavariables
- [[wiki/entities/lcf-pattern.md]] - Detailed explanation of LCF
- [[wiki/components/kernel.md]] - Kernel component details
- **Implemented in:** Phase 1 (Complete)
- **Used by:** `hwml-elab` (elaborator uses kernel API)

## Status History

- 2026-03-12: Proposed
- 2026-03-15: Approved after design review
- 2026-03-28: Implemented
- 2026-04-10: Phase 1 complete, kernel in production use
```

---

## Example 2: Entity Page (Concept)

This would be generated from `design/2ltt-nbe.md` and other sources:

```markdown
# Normalization by Evaluation (NbE)

**Type:** Concept  
**Status:** In-Use  
**Confidence:** 0.95  
**Phase:** Phase 1 (Implemented)

## Definition

**Normalization by Evaluation** is a technique for normalizing terms in typed lambda 
calculi. The key insight: evaluate terms to semantic values, then quote back to 
syntax in normal form.

**The NbE pipeline:**
```
Syntax (raw term)
  → eval → 
Value (semantic domain)
  → quote →
Syntax (normalized term)
```

## How HWML Uses It

HWML uses NbE for:
1. **Type checking:** Normalize types to compare for equality
2. **Unification:** Normalize terms before pattern matching
3. **WHNF (Weak Head Normal Form):** Reduce terms just enough to expose head constructor
4. **Elaboration:** Normalize meta-level computation during hardware generation

**Example:**
```hwml
# Surface
def foo := (λx. x) 42

# After elaboration
const @foo : $Nat = ($App ($Lambda ...) ($NatLit 42))

# After NbE normalization
const @foo : $Nat = ($NatLit 42)
```

The lambda application evaluates away, producing the normalized result.

## Key Properties

- **Soundness:** If `eval(t) = v`, then `quote(v)` is a normal form of `t`
- **Completeness:** All convertible terms normalize to the same result
- **Efficiency:** Often faster than term rewriting
- **Typed:** Evaluation preserves types (semantic values are typed)

## Why NbE Instead of Alternatives?

### vs. Term Rewriting
- NbE: Evaluate to semantic domain, quote back
- Term rewriting: Pattern match and rewrite syntax directly
- **Winner:** NbE - cleaner for dependent types, handles binding correctly

### vs. Abstract Machines (CEK, SECD)
- NbE: High-level, compositional
- Abstract machines: Low-level, imperative
- **Winner:** NbE - easier to prove correct, integrates with type checking

## HWML Implementation

**Crate:** `hwml-core`  
**Module:** `src/eval.rs`, `src/quote.rs`

**Key types:**
```rust
// Semantic domain
pub enum Value<'db> {
    Lambda(Closure<'db>),
    Stuck(Head, Spine<'db>),
    Universe(UniverseLevel),
    // ...
}

// Evaluation
pub fn eval<'db>(env: &Env<'db>, term: RcSyntax<'db>) -> RcValue<'db>

// Quotation
pub fn quote<'db>(level: Level, value: RcValue<'db>) -> RcSyntax<'db>
```

**Special features:**
- **Stuck values:** Handle metavariables and free variables
- **Closures:** Capture environment for lambda bodies
- **Lazy evaluation:** Don't evaluate under binders unless needed

## Related Concepts

- [[bidirectional-typing]] - NbE used for type normalization
- [[pattern-unification]] - Normalizes before unifying
- [[universes]] - Universe levels tracked through evaluation
- [[elaboration]] - Meta-level uses NbE for computation

## References

**Papers:**
- "Normalization by Evaluation" (Berger, Schwichtenberg, 1991)
- "Type Theory in Color" (Bernardy, Guilhem, 2013) - Staged NbE
- "Elaborating Dependent (Co)pattern Matching" (Cockx, Abel, 2018)

**Implementations:**
- Agda: Uses NbE for type checking
- Lean 4: Staged NbE for kernel
- Idris 2: NbE with totality checking

**HWML sources:**
- `design/2ltt-nbe.md` - NbE design for 2-level type theory
- `design/nbe-architecture.md` - Implementation architecture
- `design/NbE-IMPLEMENTATION-PLAN.md` - Phase 1 plan

## Implementation Status

- [x] Basic eval/quote (Phase 1)
- [x] WHNF for type checking (Phase 1)
- [x] Stuck values (metavariables) (Phase 1)
- [x] Closures and environments (Phase 1)
- [ ] Optimizations (lazy reduction) (Phase 2)
- [ ] Profiling and performance tuning (Phase 2)

## Common Questions

**Q: Why semantic domain instead of syntax-directed reduction?**  
A: Semantic domain handles binding (de Bruijn levels) cleanly and composes well 
with type checking.

**Q: How do metavariables work with NbE?**  
A: Unsolved metavariables evaluate to stuck values. When solved, evaluation continues.

**Q: Performance concerns?**  
A: NbE can be slower for simple reductions but faster overall due to sharing. We 
profile and optimize hot paths.
```

---

These examples show:
- **ADRs** capture decisions with full context and rationale
- **Entity pages** explain concepts with HWML-specific details
- Both cite sources and cross-reference related pages
- Status and implementation tracking integrated
- Useful for both understanding (onboarding) and reference (development)
