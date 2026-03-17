# HWML Architecture: LCF-Style Trusted Kernel

**Last Updated:** 2026-03-12  
**Status:** Design Approved

---

## Core Architectural Principles

### 1. **Trusted Kernel with Bidirectional Judgements**

The kernel is the **only** module that can construct `Syntax<'db>` nodes. All constructors are `pub(crate)` within `hwml-core`, accessible only to the kernel module.

**Key Invariant:** Every term construction enforces bidirectional typing rules.

```
┌─────────────────────────────────────────────────────────┐
│                    Trusted Kernel                        │
│  ┌───────────────────────────────────────────────────┐  │
│  │  CheckedTerm<'db>    : Γ ⊢ term ⇐ ty             │  │
│  │  SynthesizedTerm<'db>: Γ ⊢ term ⇒ ty             │  │
│  │  WellFormedType<'db> : Γ ⊢ ty : U_level          │  │
│  └───────────────────────────────────────────────────┘  │
│                                                          │
│  Private: Syntax<'db> constructors                      │
│  Public:  Judgement API (check_lambda, synth_app, ...)  │
└─────────────────────────────────────────────────────────┘
                          ▲
                          │ Uses judgement API
                          │
┌─────────────────────────────────────────────────────────┐
│                    Elaborator                            │
│  - Parses surface syntax                                 │
│  - Resolves names to de Bruijn indices                   │
│  - Inserts implicit arguments                            │
│  - Compiles pattern matching                             │
│  - Calls kernel API to construct well-typed terms        │
└─────────────────────────────────────────────────────────┘
```

### 2. **Async Constraint Solving**

The kernel is **async** and integrates with the existing `SolverState` for metavariable resolution.

- Kernel functions can `.await` on unsolved metavariables
- Unification is part of the kernel context
- Cooperative scheduling via `SingleThreadedExecutor`

### 3. **Separation of Surface and Core**

```
Surface AST (hwml-surface)
    ↓ (elaboration)
Core AST (hwml-core::Syntax)
    ↓ (evaluation)
Semantic Domain (hwml-core::Value)
    ↓ (quotation)
Core AST (hwml-core::Syntax)
```

**Surface AST:** User-facing syntax with syntactic sugar, no type information  
**Core AST:** Fully elaborated, type-directed, de Bruijn indexed  
**Semantic Domain:** NbE representation for type checking and unification

---

## Module Structure

```
hwml-rust/
├── crates/
│   ├── hwml-core/           # Trusted kernel and core IR
│   │   ├── src/
│   │   │   ├── kernel/      # ← NEW: Trusted kernel module
│   │   │   │   ├── mod.rs
│   │   │   │   ├── tokens.rs      (CheckedTerm, SynthesizedTerm, WellFormedType)
│   │   │   │   ├── context.rs     (KernelContext)
│   │   │   │   ├── judgements.rs  (check_lambda, synth_app, ...)
│   │   │   │   ├── errors.rs      (KernelError)
│   │   │   │   └── universe.rs    (Universe level inference)
│   │   │   ├── syn/         # Syntax (constructors now pub(crate))
│   │   │   ├── val.rs       # Semantic domain
│   │   │   ├── eval.rs      # Evaluation
│   │   │   ├── quote.rs     # Quotation
│   │   │   └── ...
│   │   └── ...
│   ├── hwml-elab/           # Elaborator (untrusted)
│   │   ├── src/
│   │   │   ├── elaborator.rs  (Uses kernel API, no direct Syntax construction)
│   │   │   ├── engine.rs      (SolverState, SingleThreadedExecutor)
│   │   │   ├── unify.rs       (Async unification)
│   │   │   └── force.rs       (Metavariable forcing)
│   │   └── ...
│   ├── hwml-surface/        # Surface syntax parser
│   │   └── src/
│   │       ├── syntax.rs      (Surface AST)
│   │       └── grammar.lalrpop
│   └── ...
```

---

## Type Safety Guarantees

### Invariants Enforced by the Kernel

1. **Well-Typedness:** Every `CheckedTerm<'db>` has the claimed type
2. **Type Synthesis:** Every `SynthesizedTerm<'db>` has exactly the synthesized type
3. **Universe Consistency:** Every `WellFormedType<'db>` lives in the claimed universe
4. **Scope Safety:** Variables are always bound in the context
5. **Substitution Correctness:** Closures capture the correct environment

### What the Kernel Does NOT Guarantee

- **Termination:** The kernel does not check for infinite loops
- **Positivity:** Inductive types are not checked for strict positivity (yet)
- **Coverage:** Pattern matching exhaustiveness is checked but not proven complete

---

## Bidirectional Typing Rules (Encoded in Kernel)

### Check Mode (⇐)

```
Γ ⊢ A : U_i    Γ, x : A ⊢ B : U_j
─────────────────────────────────── (Pi-Form)
Γ ⊢ (x : A) → B ⇐ U_max(i,j)

Γ, x : A ⊢ body ⇐ B
──────────────────────────── (Lambda-Intro)
Γ ⊢ λx. body ⇐ (x : A) → B

Γ ⊢ term ⇒ T'    T' ≡ T
────────────────────────── (Check-Synth)
Γ ⊢ term ⇐ T
```

### Synth Mode (⇒)

```
x : T ∈ Γ
───────── (Var)
Γ ⊢ x ⇒ T

Γ ⊢ f ⇒ (x : A) → B    Γ ⊢ a ⇐ A
─────────────────────────────────── (App)
Γ ⊢ f a ⇒ B[a/x]

────────────────── (Universe)
Γ ⊢ U_i ⇒ U_{i+1}
```

---

## Async Integration

### Metavariable Resolution

```rust
// Kernel can await on metavariable solutions
pub async fn synth_app<'db, 'g>(
    ctx: &mut KernelContext<'db, 'g>,
    func: SynthesizedTerm<'db>,
    arg: CheckedTerm<'db>,
) -> Result<SynthesizedTerm<'db>, KernelError> {
    // Force function type to WHNF (may await on metas)
    let func_ty = ctx.whnf(func.ty.clone()).await?;
    
    // Extract Pi type
    let (source_ty, target_closure) = match &*func_ty {
        Value::Pi(pi) => (pi.source.clone(), pi.target.clone()),
        _ => return Err(KernelError::ExpectedPi { got: func_ty }),
    };
    
    // Unify argument type (may await on metas)
    ctx.unify(arg.ty.clone(), source_ty, func_ty.clone()).await?;
    
    // ... construct application
}
```

### Cooperative Scheduling

1. Kernel function calls `.await` on `ctx.whnf()` or `ctx.unify()`
2. If metavariable is unsolved, returns `Poll::Pending`
3. Executor suspends task and registers waker
4. When another task solves the meta, waker is called
5. Task resumes and completes the judgement

---

## Error Reporting

### SourceRange Tracking

Every metavariable stores its creation location:

```rust
struct MetaSlot<'db> {
    ty: RcValue<'db>,
    solution: Option<RcSyntax<'db>>,
    waiters: Vec<WaitingTask>,
    poisoned: bool,
    location: SourceRange,  // ← Source location
}
```

When the solver deadlocks, we can report:
```
Error: Unsolved metavariable ?0
  Created at: examples/test.hwml:5:10
  Expected type: (x : Nat) → Vec x
  Blocked on: Expected Pi type, got ?1
```

### Kernel Errors

```rust
pub enum KernelError {
    UnboundVariable { index: Index },
    ExpectedPi { got: RcValue<'db> },
    TypeMismatch { expected, got, location },
    UnificationFailed(String),
    // ...
}
```

---

## Migration Path

### Phase 1: SourceRange Tracking (~50 lines)
Add location to `MetaSlot`, thread through elaborator.

### Phase 2: Kernel Foundation (~1200 lines)
- Define tokens (`CheckedTerm`, `SynthesizedTerm`, `WellFormedType`)
- Implement `KernelContext`
- Implement core judgements (lambda, pi, app, var)
- Make `Syntax` constructors `pub(crate)`

### Phase 3: Universe Inference (~150 lines)
Replace hardcoded `UniverseLevel::new(0)` with proper inference.

### Phase 4: Elaborator Refactor (~1500 lines)
Update elaborator to use kernel API instead of direct `Syntax` construction.

**Total:** ~2900 lines

---

## Benefits

### Type Safety
- **Impossible to construct ill-typed terms** outside the kernel
- **Proof-carrying terms**: Every term carries its type

### Maintainability
- **Clear trust boundary**: Only kernel needs careful review
- **Modular**: Elaborator can be refactored without breaking soundness

### Debugging
- **Better error messages**: SourceRange tracking on metavariables
- **Easier to reason about**: Bidirectional rules are explicit

### Future-Proofing
- **Easy to add features**: New constructs just need kernel judgements
- **Incremental verification**: Can add proof obligations to kernel later

---

**End of Architecture Document**
