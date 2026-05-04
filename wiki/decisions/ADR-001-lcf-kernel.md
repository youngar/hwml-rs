# ADR-001: LCF-Style Trusted Kernel

**Status:** Approved and Implemented  
**Date:** 2026-03-12  
**Phase:** Phase 1 (Complete)  
**Confidence:** 0.95

---

## Context

HWML is a dependently-typed hardware description language where type safety is critical. Incorrect types can lead to synthesis errors or hardware bugs that are expensive to fix. We need a mechanism to ensure that every term in the core language is provably well-typed.

**Constraints:**
- Must support bidirectional type checking
- Must integrate with async elaboration (metavariable solving)
- Must be verifiable and auditable for correctness
- Performance matters (type checking is frequent)

**Problem:** How do we enforce type safety in the core IR?

---

## Alternatives Considered

### Option 1: Unchecked Construction (Unsafe)
Allow direct construction of `Syntax<'db>` nodes without type checking.

**Pros:**
- Maximum flexibility for implementers
- Best raw performance
- Simplest implementation

**Cons:**
- No safety guarantees
- Bugs can create ill-typed terms
- Type errors discovered late, far from source
- Hard to debug when things go wrong

**Verdict:** **Rejected** - Safety is paramount for hardware compilation

### Option 2: Runtime Type Checking
Add runtime checks at every term construction point.

**Pros:**
- Catches errors at construction time
- More flexible than kernel approach
- Errors closer to source

**Cons:**
- Runtime overhead on every construction
- Error messages still distant from original source
- Can still construct invalid terms if checks have bugs
- No compile-time guarantees

**Verdict:** **Better but insufficient**

### Option 3: LCF-Style Kernel (Chosen)
Create a trusted kernel module that is the only code that can construct `Syntax<'db>` nodes. Kernel enforces bidirectional typing rules and returns typed evidence tokens.

**Pros:**
- Type safety enforced at Rust compile time
- Only valid terms can be constructed
- Small trusted computing base (easy to audit)
- Zero runtime overhead
- Evidence tokens (`CheckedTerm`, `SynthesizedTerm`) prove correctness

**Cons:**
- More complex API for elaborator
- Less flexibility (intentional - forces correctness)
- Requires disciplined design

**Verdict:** **Best fit for HWML's safety and correctness requirements**

### Option 4: Proof-Carrying Terms
Embed full proof objects that terms are well-typed.

**Pros:**
- Mathematical proof of correctness
- Ultimate verification

**Cons:**
- Massive implementation complexity
- Significant performance overhead
- Way more than needed for our use case

**Verdict:** **Overkill** - Interesting but unnecessary

---

## Decision

Implement an **LCF-style trusted kernel** where:

1. All `Syntax<'db>` constructors are `pub(crate)` within `hwml-core`
2. Only the `kernel` module (within `hwml-core`) can construct terms
3. Kernel enforces bidirectional typing rules (check mode ⇐, synth mode ⇒)
4. Kernel returns typed evidence tokens that prove well-typedness:
   - `CheckedTerm<'db>` - proves `Γ ⊢ term ⇐ ty`
   - `SynthesizedTerm<'db>` - proves `Γ ⊢ term ⇒ ty`
   - `WellFormedType<'db>` - proves `Γ ⊢ ty : U_level`

---

## Rationale

The LCF approach gives us **type safety for free via Rust's type system**. A value of type `CheckedTerm<'db>` is compile-time proof that the term was type-checked against a known type. This proof is verified at Rust compile time, not at runtime.

By restricting term construction to the kernel module, we create a **small trusted computing base (TCB)**. If the kernel is correct, the entire type system is sound. The rest of the compiler (elaborator, parser, etc.) is untrusted - bugs in those modules can cause compilation failures but cannot violate type safety.

This pattern comes from the ML family of theorem provers:
- **LCF** (Edinburgh, 1970s) - Original idea
- **HOL** - Refined the kernel approach
- **Isabelle**, **Coq** - Modern implementations

We apply the same principle to dependently-typed term construction.

**Key Insight:** Use Rust's type system to enforce HWML's type system. The kernel's API makes illegal states unrepresentable.

---

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
pub struct WellFormedType<'db>(RcValue<'db>, UniverseLevel);

pub async fn check_lambda<'db>(
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
- `src/kernel/mod.rs` - Kernel public API
- `src/kernel/judgements.rs` - Typing rules implementation
- `src/kernel/tokens.rs` - Evidence token definitions
- `src/kernel/context.rs` - KernelContext with async support
- `src/syn.rs` - Syntax (constructors pub(crate))

---

## Consequences

### Positive
✅ **Type safety:** Impossible to construct ill-typed terms outside kernel  
✅ **Auditability:** Only ~2000 lines of kernel code needs deep review  
✅ **Zero cost:** Safety enforced at compile time, no runtime overhead  
✅ **Clear API:** Evidence tokens make type checking explicit  
✅ **Rust synergy:** Leverages Rust's type system for proof  
✅ **Maintainability:** Elaborator can be refactored without breaking soundness

### Negative
❌ **API complexity:** Elaborator must use kernel API, can't construct terms directly  
❌ **Learning curve:** Contributors need to understand the pattern  
❌ **Rigidity:** Can't "hack around" kernel for experiments (intentional)

### Trade-offs
We chose:
- **Safety over flexibility**
- **Compile-time checking over runtime checking**
- **Small TCB over distributed verification**

---

## Challenges Encountered

1. **Async elaboration integration**
   - Problem: Kernel needs to await on unsolved metavariables
   - Solution: Make kernel functions `async`, use cooperative scheduling
   - See: [[ADR-003-async-elaboration]]

2. **Error reporting with good source locations**
   - Problem: Type errors deep in kernel need accurate source info
   - Solution: `SourceRange` tracking, metavariable creation locations
   - Status: Implemented in Phase 1

3. **Performance concerns**
   - Worry: Evidence tokens might add overhead
   - Result: Zero-cost abstractions - tokens are compile-time only
   - Status: No measurable performance impact

---

## Sources

**Primary Design Document:**
- `design/ARCHITECTURE.md` (Last Updated: 2026-03-12)

**Research & Inspiration:**
- Gordon, Milner, Wadsworth: "Edinburgh LCF" (1979)
- HOL Light kernel design
- Coq kernel architecture documentation
- Lean 4 kernel (though different approach)

**Discussions:**
- Internal design review: 2026-03-10
- Consensus: Safety-first approach for hardware domain

---

## Related

**Decisions:**
- [[ADR-002-bidirectional-typing]] - Uses kernel's typed tokens
- [[ADR-003-async-elaboration]] - How kernel integrates with metavariables

**Entities:**
- [[entities/lcf-pattern]] - Detailed explanation of LCF approach
- [[entities/bidirectional-typing]] - The typing discipline kernel enforces

**Components:**
- [[components/kernel]] - Implementation details
- [[components/elaborator]] - Uses the kernel API

**Implementation:**
- **Phase:** 1 (Complete)
- **Status:** Implemented and in production use
- **Crate:** `hwml-core/src/kernel/`

---

## Status History

- **2026-03-10:** Initial proposal discussed
- **2026-03-12:** Design approved (this ADR written)
- **2026-03-15:** Kernel foundation implemented (~1200 lines)
- **2026-03-20:** Universe inference added (~150 lines)
- **2026-03-28:** Elaborator refactored to use kernel API (~1500 lines)
- **2026-04-10:** Phase 1 complete, kernel in production use
