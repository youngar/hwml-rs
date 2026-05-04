# Normalization by Evaluation (NbE)

**Type:** Concept  
**Status:** In-Use (Implemented Phase 1)  
**Confidence:** 0.95  
**Last Updated:** 2026-05-02

---

## Definition

**Normalization by Evaluation (NbE)** is a technique for normalizing terms in typed lambda calculi by evaluating them to semantic values and then quoting back to syntax.

**The NbE Pipeline:**
```
Syntax (term)
    ↓ eval
Value (semantic)
    ↓ quote
Syntax (normalized)
```

Instead of rewriting syntax directly (term rewriting), NbE uses a semantic domain that naturally represents normal forms.

---

## How HWML Uses It

HWML uses NbE for multiple purposes:

1. **Type Checking** - Normalize types to compare for equality
2. **Unification** - Reduce terms before pattern matching
3. **WHNF** (Weak Head Normal Form) - Reduce just enough to expose head constructor
4. **Meta-level Computation** - Normalize during hardware generation

### Example

```hwml
# Surface syntax
def foo := (λx. x) 42

# After elaboration (core)
const @foo : $Nat = ($App ($Lambda ...) ($NatLit 42))

# After NbE normalization
const @foo : $Nat = ($NatLit 42)
```

The beta-reduction `(λx. x) 42 → 42` happens via evaluation and quotation.

---

## Key Properties

- **Soundness:** If `eval(t) = v` then `quote(v)` is a normal form of `t`
- **Completeness:** Convertible terms normalize to identical results
- **Efficiency:** Often faster than term rewriting (sharing, no pattern matching)
- **Typed:** Semantic values carry type information
- **Handles binding correctly:** De Bruijn levels in semantic domain

---

## Why NbE Instead of Alternatives?

### vs. Term Rewriting (Pattern Match & Replace)
**Term Rewriting:**
- Match patterns on syntax
- Apply rewrite rules
- Repeat until no rules match

**NbE:**
- Evaluate to semantic domain
- Quote back to syntax

**Winner:** NbE for dependent types
- Cleaner handling of substitution and binding
- Natural representation of normal forms
- Composes better with type checking

### vs. Abstract Machines (CEK, SECD, etc.)
**Abstract Machines:**
- Low-level, imperative
- Explicit control/environment/kontinuation

**NbE:**
- High-level, compositional
- Closures capture environment naturally

**Winner:** NbE for maintainability
- Easier to prove correct
- Better integration with type checking
- Simpler implementation

---

## HWML Implementation

**Crate:** `hwml-core`  
**Modules:** `src/eval.rs`, `src/quote.rs`, `src/val.rs`

### Key Types

```rust
// Semantic domain
pub enum Value<'db> {
    Lambda(Closure<'db>),
    Stuck(Head, Spine<'db>),  // Neutral values
    Universe(UniverseLevel),
    Pi(Pi<'db>),
    // ... hardware-specific values
}

// Closures capture environment
pub struct Closure<'db> {
    env: Env<'db>,
    body: RcSyntax<'db>,
}

// Stuck values (can't reduce further)
pub enum Head {
    Var(Level),              // Free variable
    Meta(MetaId),            // Unsolved metavariable
}

pub struct Spine<'db>(Vec<RcValue<'db>>);  // Arguments to stuck head
```

### Core Functions

```rust
// Evaluation: Syntax → Value
pub fn eval<'db>(
    env: &Env<'db>, 
    term: RcSyntax<'db>
) -> RcValue<'db>

// Quotation: Value → Syntax
pub fn quote<'db>(
    level: Level,      // Current de Bruijn level
    value: RcValue<'db>
) -> RcSyntax<'db>

// Weak Head Normal Form (for type checking)
pub async fn whnf<'db>(
    ctx: &mut Context<'db>,
    value: RcValue<'db>
) -> RcValue<'db>
```

### Special Features

**Stuck Values:**  
When evaluation encounters a free variable or unsolved metavariable, it produces a "stuck" value with a spine of arguments.

```rust
Value::Stuck(Head::Meta(m), spine)
// Represents: ?m arg1 arg2 arg3
// Can't reduce further until ?m is solved
```

**Closures:**  
Lambda bodies are stored as closures that capture their environment. This avoids explicit substitution.

```rust
Value::Lambda(Closure { env, body })
// When applied: eval body in extended env
```

**Lazy Evaluation:**  
Don't evaluate under binders unless needed. Quote can handle unevaluated closures.

---

## Type Checking with NbE

Bidirectional type checking uses NbE for type comparison:

```rust
// Check if two types are equal
pub async fn types_equal<'db>(
    ctx: &mut Context<'db>,
    ty1: RcValue<'db>,
    ty2: RcValue<'db>,
) -> bool {
    let ty1_whnf = whnf(ctx, ty1).await;
    let ty2_whnf = whnf(ctx, ty2).await;
    
    // Compare normalized types
    values_equal(ctx.level(), ty1_whnf, ty2_whnf)
}
```

WHNF is sufficient for most comparisons. Only reduce to head normal form.

---

## Hardware-Specific Aspects

HWML extends standard NbE for hardware:

**Signal values:**
```rust
Value::Signal(SignalValue)
// Hardware signals have special evaluation rules
```

**Module values:**
```rust
Value::Module(ModuleValue)
// Modules are first-class, can be normalized
```

**Staging (Meta vs Object level):**
- Meta-level: Evaluated at compile time (NbE runs)
- Object-level: Represents hardware (not evaluated, but normalized)

---

## Performance Considerations

**Sharing:**  
Values are reference-counted (`RcValue<'db>`). Sharing is preserved during evaluation.

**Memoization:**  
Combined with Salsa, NbE results are cached:
```rust
#[salsa::tracked]
fn normalize_term<'db>(
    db: &'db dyn Database,
    term: RcSyntax<'db>
) -> RcSyntax<'db>
```

**Profiling showed:**
- NbE is NOT the bottleneck (unification is)
- Sharing makes it faster than term rewriting for large terms
- WHNF (lazy) is much faster than full normalization

---

## Related Concepts

- [[bidirectional-typing]] - NbE used for type normalization and comparison
- [[pattern-unification]] - Normalizes before unifying
- [[universes]] - Universe levels tracked through evaluation
- [[elaboration]] - Meta-level uses NbE for compile-time computation

---

## References

### Papers
- Berger, Schwichtenberg: "An inverse of the evaluation functional for typed λ-calculus" (1991) - Original NbE paper
- Bernardy, Guilhem: "Type Theory in Color" (2013) - Staged NbE for two-level type theory
- Cockx, Abel: "Elaborating Dependent (Co)pattern Matching" (2018) - NbE in elaboration

### Implementations
- **Agda** - Uses NbE extensively for type checking
- **Lean 4** - Staged NbE in kernel
- **Idris 2** - NbE with totality checking
- **Mini-TT** - Simple educational implementation

### HWML Sources
- `design/2ltt-nbe.md` - NbE design for 2-level type theory
- `design/nbe-architecture.md` - Implementation architecture
- `design/NbE-IMPLEMENTATION-PLAN.md` - Phase 1 implementation plan
- `design/Staged-nbe.md` - Staging considerations

---

## Implementation Status

Phase 1 (Complete):
- [x] Basic `eval` and `quote`
- [x] WHNF for type checking
- [x] Stuck values (metavariables and free vars)
- [x] Closures and environments
- [x] Integration with bidirectional typing

Phase 2 (Future):
- [ ] Optimizations (lazy reduction, better sharing)
- [ ] Profiling and performance tuning
- [ ] Universe polymorphism support

---

## Common Questions

**Q: Why semantic domain instead of syntax-directed reduction?**  
A: Semantic domain naturally handles binding (de Bruijn levels), composes better with type checking, and represents normal forms directly.

**Q: How do unsolved metavariables work with NbE?**  
A: They become stuck values (`Value::Stuck(Head::Meta(m), spine)`). When the metavariable is solved, evaluation can continue.

**Q: Performance vs term rewriting?**  
A: NbE can be slower for simple reductions but faster overall due to sharing and avoiding repeated pattern matching. For HWML, it's fast enough (not the bottleneck).

**Q: Why WHNF instead of full normalization?**  
A: For type checking, we only need to see the head constructor. Full normalization is expensive and usually unnecessary.

---

**See Also:**
- [[components/kernel]] - Uses NbE for type checking
- [[decisions/ADR-001-lcf-kernel]] - Kernel architecture
- [[decisions/ADR-002-bidirectional-typing]] - How NbE fits into type checking
