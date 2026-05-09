# Implementation Plan: LCF-Style Kernel with Bidirectional Judgements

**Date:** 2026-03-12  
**Status:** Implementation Plan  
**Architecture:** LCF-style trusted kernel with bidirectional typing judgements

---

## Overview

This plan implements a **trusted kernel** that encodes bidirectional typing rules as Rust functions, guaranteeing that every constructed term is well-typed by construction. Inspired by LCF-style systems like Project Pterodactyl, the kernel exposes judgement APIs rather than raw AST constructors.

---

## Current State (What We Have)

✅ **Async bidirectional elaborator** (`check` and `synth` in `elaborator.rs`)  
✅ **Async unification** with cooperative scheduling  
✅ **SingleThreadedExecutor** with deadlock detection  
✅ **Metavariable system** (`SolverState`, `MetaSlot`)  
✅ **NbE** (`eval` and `quote`)  
✅ **Separate surface AST** (only elaborator constructs `Syntax`)

---

## Implementation Phases

### **Phase 1: SourceRange Tracking** (Foundation)
**Priority:** HIGH  
**Estimated:** ~50 lines  
**Dependencies:** None

Add location tracking to metavariables for better error reporting.

#### Changes:

**File: `crates/hwml-elab/src/engine.rs`**
```rust
// Line 117: Add location field to MetaSlot
struct MetaSlot<'db> {
    ty: RcValue<'db>,
    solution: Option<RcSyntax<'db>>,
    waiters: Vec<WaitingTask>,
    poisoned: bool,
    location: SourceRange,  // ← NEW
}

// Line 130: Update constructor
fn new(ty: RcValue<'db>, location: SourceRange) -> Self {
    Self {
        ty,
        solution: None,
        waiters: Vec::new(),
        poisoned: false,
        location,  // ← NEW
    }
}

// Line 185: Update fresh_meta signature
pub fn fresh_meta(&mut self, ty: RcValue<'db>, loc: SourceRange) -> MetaVariableId {
    let local_index = self.next_meta_index;
    let id = MetaVariableId::new(local_index);
    self.next_meta_index += 1;
    self.metas.insert(id, MetaSlot::new(ty, loc));  // ← UPDATED
    id
}
```

**File: `crates/hwml-elab/src/elaborator.rs`**
- Thread `SourceRange` through all `ctx.fresh_meta()` calls (~15 call sites)
- Use `ctx.expr_location(expr)` to get location from surface AST

**Testing:**
- Verify error messages include source locations
- Test with deliberately unsolvable constraints

---

### **Phase 2a: Kernel Foundation** (Tokens and Context)
**Priority:** HIGH  
**Estimated:** ~300 lines  
**Dependencies:** Phase 1

Create the trusted kernel module with typing tokens and context.

#### New Files:

**File: `crates/hwml-core/src/kernel/mod.rs`**
```rust
//! The trusted kernel: all well-typed term construction goes through here.
//!
//! This module is the ONLY place where `Syntax` nodes are constructed.
//! All constructors enforce bidirectional typing rules.

mod tokens;
mod context;
mod judgements;
mod errors;

pub use tokens::{CheckedTerm, SynthesizedTerm, WellFormedType};
pub use context::KernelContext;
pub use errors::KernelError;

// Re-export judgement functions
pub use judgements::*;
```

**File: `crates/hwml-core/src/kernel/tokens.rs`**
```rust
use crate::{Syntax, Value, UniverseLevel};
use std::rc::Rc;

/// A term that has been **checked** against a known type.
/// Invariant: Γ ⊢ term ⇐ ty
#[derive(Clone, Debug)]
pub struct CheckedTerm<'db> {
    pub(super) term: RcSyntax<'db>,
    pub(super) ty: RcValue<'db>,
}

impl<'db> CheckedTerm<'db> {
    /// SAFETY: Only callable within the kernel module.
    /// Caller must ensure the typing invariant holds.
    pub(super) fn new_unchecked(term: RcSyntax<'db>, ty: RcValue<'db>) -> Self {
        Self { term, ty }
    }
    
    pub fn syntax(&self) -> &RcSyntax<'db> {
        &self.term
    }
    
    pub fn ty(&self) -> &RcValue<'db> {
        &self.ty
    }
    
    pub fn into_parts(self) -> (RcSyntax<'db>, RcValue<'db>) {
        (self.term, self.ty)
    }
}

/// A term whose type has been **synthesized**.
/// Invariant: Γ ⊢ term ⇒ ty
#[derive(Clone, Debug)]
pub struct SynthesizedTerm<'db> {
    pub(super) term: RcSyntax<'db>,
    pub(super) ty: RcValue<'db>,
}

impl<'db> SynthesizedTerm<'db> {
    pub(super) fn new_unchecked(term: RcSyntax<'db>, ty: RcValue<'db>) -> Self {
        Self { term, ty }
    }
    
    pub fn syntax(&self) -> &RcSyntax<'db> {
        &self.term
    }
    
    pub fn ty(&self) -> &RcValue<'db> {
        &self.ty
    }
    
    pub fn into_parts(self) -> (RcSyntax<'db>, RcValue<'db>) {
        (self.term, self.ty)
    }
    
    /// Convert a synthesized term to a checked term (trivial coercion).
    pub fn into_checked(self) -> CheckedTerm<'db> {
        CheckedTerm::new_unchecked(self.term, self.ty)
    }
}

/// A type that has been verified to be well-formed in a universe.
/// Invariant: Γ ⊢ ty : U_level
#[derive(Clone, Debug)]
pub struct WellFormedType<'db> {
    pub(super) ty: RcValue<'db>,
    pub(super) universe: UniverseLevel,
}

impl<'db> WellFormedType<'db> {
    pub(super) fn new_unchecked(ty: RcValue<'db>, universe: UniverseLevel) -> Self {
        Self { ty, universe }
    }
    
    pub fn ty(&self) -> &RcValue<'db> {
        &self.ty
    }
    
    pub fn universe(&self) -> UniverseLevel {
        self.universe
    }
}
```

**File: `crates/hwml-core/src/kernel/errors.rs`**
```rust
use crate::{Value, QualifiedName, UniverseLevel, SourceRange, Index};
use crate::eval;
use crate::unify;
use std::rc::Rc;

#[derive(Debug, Clone)]
pub enum KernelError {
    UnboundVariable { index: Index },
    ExpectedPi { got: RcValue<'db> },
    ExpectedTypeConstructor { expected: QualifiedName<'db>, got: RcValue<'db> },
    TypeMismatch {
        expected: RcValue<'db>,
        got: RcValue<'db>,
        location: SourceRange,
    },
    UnificationFailed(String),  // Simplified for now
    EvaluationFailed(String),
    UniverseLevelMismatch {
        expected: UniverseLevel,
        got: UniverseLevel,
    },
}

impl From<eval::Error> for KernelError {
    fn from(e: eval::Error) -> Self {
        KernelError::EvaluationFailed(format!("{:?}", e))
    }
}
```

**File: `crates/hwml-core/src/kernel/context.rs`**
```rust
use crate::kernel::{KernelError, CheckedTerm, SynthesizedTerm};
use crate::{Syntax, Value, Index, Level, SourceRange, eval, TransparentEnv};
use crate::val::{Environment, LocalEnv};
use hwml_elab::engine::SolverEnvironment;
use hwml_elab::force::force;
use hwml_elab::unify::unify;
use std::rc::Rc;

pub struct KernelContext<'db, 'g> {
    /// The solver environment (for metavariables and async operations)
    pub(super) solver: SolverEnvironment<'db, 'g>,

    /// The typing context: maps de Bruijn levels to their types
    pub(super) types: Vec<RcValue<'db>>,

    /// The value environment (for evaluation)
    pub(super) values: LocalEnv<'db>,

    /// Current location for error reporting
    pub(super) location: SourceRange,
}

impl<'db, 'g> KernelContext<'db, 'g> {
    pub fn new(solver: SolverEnvironment<'db, 'g>, location: SourceRange) -> Self {
        Self {
            solver,
            types: Vec::new(),
            values: LocalEnv::new(),
            location,
        }
    }

    /// Get the current depth (number of bindings)
    pub fn depth(&self) -> usize {
        self.types.len()
    }

    /// Convert de Bruijn index to level
    pub fn index_to_level(&self, index: Index) -> Result<usize, KernelError> {
        let depth = self.depth();
        if index.to_usize() < depth {
            Ok(depth - 1 - index.to_usize())
        } else {
            Err(KernelError::UnboundVariable { index })
        }
    }

    /// Push a new binding into the context
    pub fn push_binding(&mut self, ty: RcValue<'db>) -> Level {
        let level = self.types.len();
        self.types.push(ty);
        self.values = self.values.extend(Rc::new(Value::variable(level)));
        level
    }

    /// Pop a binding from the context
    pub fn pop_binding(&mut self) {
        self.types.pop();
        self.values = self.values.drop_last();
    }

    /// Look up the type of a variable by index
    pub fn lookup_type(&self, index: Index) -> Result<RcValue<'db>, KernelError> {
        let level = self.index_to_level(index)?;
        self.types.get(level).cloned()
            .ok_or(KernelError::UnboundVariable { index })
    }

    /// Evaluate a syntax term in the current context
    pub fn eval(&self, term: &Syntax<'db>) -> Result<RcValue<'db>, KernelError> {
        let mut env = Environment {
            global: self.solver.tc_env.values.global,
            local: self.values.clone(),
            transparent: TransparentEnv::new(),
        };
        eval::eval(&mut env, term).map_err(KernelError::from)
    }

    /// Force a value to WHNF (async, may block on metavariables)
    pub async fn whnf(&self, value: RcValue<'db>) -> Result<RcValue<'db>, KernelError> {
        force(&self.solver, value).map_err(KernelError::from)
    }

    /// Unify two values at a given type (async)
    pub async fn unify(
        &self,
        lhs: RcValue<'db>,
        rhs: RcValue<'db>,
        ty: RcValue<'db>,
    ) -> Result<(), KernelError> {
        unify(self.solver.tc_env.db, self.solver.clone(), lhs, rhs, ty)
            .await
            .map_err(|e| KernelError::UnificationFailed(format!("{:?}", e)))
    }
}
```

#### Changes to Existing Files:

**File: `crates/hwml-core/src/lib.rs`**
```rust
// Add kernel module
pub mod kernel;
```

**File: `crates/hwml-core/src/syn/basic.rs`**
```rust
// Change ALL Syntax constructors from `pub` to `pub(crate)`
impl<'db> Syntax<'db> {
    pub(crate) fn lambda_rc(body: RcSyntax<'db>) -> RcSyntax<'db> {
        // ...
    }

    pub(crate) fn application_rc(/* ... */) -> RcSyntax<'db> {
        // ...
    }

    // ... all other constructors become pub(crate)
}
```

**Testing:**
- Verify that code outside `hwml-core` cannot construct `Syntax` directly
- Verify that `CheckedTerm` and `SynthesizedTerm` can be created within kernel module

---

### **Phase 2b: Core Judgements** (Lambda, Pi, App, Var)
**Priority:** HIGH
**Estimated:** ~500 lines
**Dependencies:** Phase 2a

Implement the fundamental bidirectional typing judgements.

#### New File:

**File: `crates/hwml-core/src/kernel/judgements.rs`**

```rust
use super::{CheckedTerm, SynthesizedTerm, WellFormedType, KernelContext, KernelError};
use crate::{Syntax, Value, Index, UniverseLevel, QualifiedName};
use std::rc::Rc;
use std::pin::Pin;
use std::future::Future;

// ============================================================================
// Check Mode (Introduction Forms)
// ============================================================================

/// Γ ⊢ λx. body ⇐ (x : A) → B
pub async fn check_lambda<'db, 'g, F, Fut>(
    ctx: &mut KernelContext<'db, 'g>,
    expected_ty: &RcValue<'db>,
    body_checker: F,
) -> Result<CheckedTerm<'db>, KernelError>
where
    F: FnOnce(&mut KernelContext<'db, 'g>) -> Fut,
    Fut: Future<Output = Result<CheckedTerm<'db>, KernelError>>,
{
    // Force expected_ty to WHNF
    let expected_ty = ctx.whnf(expected_ty.clone()).await?;

    // Extract Pi type
    let (source_ty, target_closure) = match &*expected_ty {
        Value::Pi(pi) => (pi.source.clone(), pi.target.clone()),
        _ => return Err(KernelError::ExpectedPi { got: expected_ty }),
    };

    // Push binding for lambda parameter
    ctx.push_binding(source_ty.clone());

    // Check the body in extended context
    let body_checked = body_checker(ctx).await?;

    // Pop binding
    ctx.pop_binding();

    // Construct lambda term
    let lambda_term = Syntax::lambda_rc(body_checked.term.clone());

    Ok(CheckedTerm::new_unchecked(lambda_term, expected_ty))
}

/// Γ ⊢ (x : A) → B ⇐ U_i
pub async fn check_pi<'db, 'g, F, Fut>(
    ctx: &mut KernelContext<'db, 'g>,
    source: CheckedTerm<'db>,
    target_checker: F,
    expected_universe: UniverseLevel,
) -> Result<CheckedTerm<'db>, KernelError>
where
    F: FnOnce(&mut KernelContext<'db, 'g>) -> Fut,
    Fut: Future<Output = Result<CheckedTerm<'db>, KernelError>>,
{
    // Verify source is a type in some universe
    let source_val = ctx.eval(source.syntax())?;

    // Push binding for Pi parameter
    ctx.push_binding(source_val.clone());

    // Check target in extended context
    let target_checked = target_checker(ctx).await?;

    // Pop binding
    ctx.pop_binding();

    // Construct Pi term
    let pi_term = Syntax::pi_rc(source.term.clone(), target_checked.term.clone());

    // The type of the Pi is the expected universe
    let pi_ty = Rc::new(Value::universe(expected_universe));

    Ok(CheckedTerm::new_unchecked(pi_term, pi_ty))
}

/// Γ ⊢ term ⇐ expected_ty (via synthesis + conversion)
pub async fn check_by_synth<'db, 'g>(
    ctx: &mut KernelContext<'db, 'g>,
    term: SynthesizedTerm<'db>,
    expected_ty: &RcValue<'db>,
) -> Result<CheckedTerm<'db>, KernelError> {
    // Unify synthesized type with expected type
    let universe_ty = Rc::new(Value::universe(UniverseLevel::new(0))); // TODO: proper universe
    ctx.unify(term.ty.clone(), expected_ty.clone(), universe_ty).await?;

    // If unification succeeds, we can safely coerce
    Ok(CheckedTerm::new_unchecked(term.term, expected_ty.clone()))
}

// ============================================================================
// Synth Mode (Elimination Forms)
// ============================================================================

/// Γ ⊢ f a ⇒ B[a/x]  (given Γ ⊢ f ⇒ (x : A) → B)
pub async fn synth_app<'db, 'g>(
    ctx: &mut KernelContext<'db, 'g>,
    func: SynthesizedTerm<'db>,
    arg: CheckedTerm<'db>,
) -> Result<SynthesizedTerm<'db>, KernelError> {
    // Force function type to WHNF
    let func_ty = ctx.whnf(func.ty.clone()).await?;

    // Extract Pi type
    let (source_ty, target_closure) = match &*func_ty {
        Value::Pi(pi) => (pi.source.clone(), pi.target.clone()),
        _ => return Err(KernelError::ExpectedPi { got: func_ty }),
    };

    // Verify argument type matches source
    ctx.unify(arg.ty.clone(), source_ty, func_ty.clone()).await?;

    // Evaluate argument to apply closure
    let arg_val = ctx.eval(arg.syntax())?;

    // Apply closure to get result type
    let result_ty = eval::run_closure(
        ctx.solver.tc_env.values.global,
        &target_closure,
        std::iter::once(arg_val),
    )?;

    // Construct application term
    let app_term = Syntax::application_rc(func.term, arg.term);

    Ok(SynthesizedTerm::new_unchecked(app_term, result_ty))
}

/// Γ ⊢ x ⇒ Γ(x)
pub async fn synth_var<'db, 'g>(
    ctx: &KernelContext<'db, 'g>,
    index: Index,
) -> Result<SynthesizedTerm<'db>, KernelError> {
    let ty = ctx.lookup_type(index)?;
    let var_term = Syntax::variable_rc(index);
    Ok(SynthesizedTerm::new_unchecked(var_term, ty))
}

/// Γ ⊢ c ⇒ type(c)  (for constants)
pub async fn synth_constant<'db, 'g>(
    ctx: &KernelContext<'db, 'g>,
    constant: QualifiedName<'db>,
) -> Result<SynthesizedTerm<'db>, KernelError> {
    // Look up constant type from global environment
    let ty = ctx.solver.tc_env.values.global.lookup_constant_type(constant)?;
    let const_term = Syntax::constant_rc(constant);
    Ok(SynthesizedTerm::new_unchecked(const_term, ty))
}

/// Γ ⊢ U_i ⇒ U_{i+1}
pub async fn synth_universe<'db, 'g>(
    _ctx: &KernelContext<'db, 'g>,
    level: UniverseLevel,
) -> Result<SynthesizedTerm<'db>, KernelError> {
    let universe_term = Syntax::universe_rc(level);
    let universe_ty = Rc::new(Value::universe(level.successor()));
    Ok(SynthesizedTerm::new_unchecked(universe_term, universe_ty))
}
```

**Testing:**
- Unit tests for each judgement function
- Test lambda checking with various Pi types
- Test application synthesis with dependent types
- Test variable synthesis with multi-level contexts

---

### **Phase 2c: Advanced Judgements** (Case, Lift, Hardware)
**Priority:** MEDIUM
**Estimated:** ~400 lines
**Dependencies:** Phase 2b

Implement pattern matching, universe lifting, and hardware-specific judgements.

**File: `crates/hwml-core/src/kernel/judgements.rs` (continued)**

```rust
// ============================================================================
// Pattern Matching
// ============================================================================

/// Γ ⊢ case scrut of { branches } ⇐ motive(scrut)
pub async fn check_case<'db, 'g>(
    ctx: &mut KernelContext<'db, 'g>,
    scrut: SynthesizedTerm<'db>,
    motive: Closure<'db>,
    branches: Vec<CaseBranch<'db>>,
    expected_ty: &RcValue<'db>,
) -> Result<CheckedTerm<'db>, KernelError> {
    // TODO: Implement case checking
    // 1. Verify scrutinee type is a type constructor
    // 2. Check each branch against motive applied to constructor
    // 3. Verify exhaustiveness
    // 4. Construct case term
    unimplemented!("check_case")
}

// ============================================================================
// Universe Lifting
// ============================================================================

/// Γ ⊢ Lift A ⇐ U_{i+1}  (given A : U_i)
pub async fn check_lift<'db, 'g>(
    ctx: &KernelContext<'db, 'g>,
    inner: CheckedTerm<'db>,
) -> Result<CheckedTerm<'db>, KernelError> {
    // Extract universe level from inner type
    let inner_val = ctx.eval(inner.syntax())?;
    let inner_universe = match &*inner.ty {
        Value::Universe(u) => u.level,
        _ => return Err(KernelError::ExpectedUniverse { got: inner.ty.clone() }),
    };

    // Construct Lift type
    let lift_term = Syntax::lift_rc(inner.term);
    let lift_ty = Rc::new(Value::universe(inner_universe.successor()));

    Ok(CheckedTerm::new_unchecked(lift_term, lift_ty))
}

/// Γ ⊢ lift a ⇐ Lift A  (given a : A)
pub async fn check_lift_intro<'db, 'g>(
    ctx: &KernelContext<'db, 'g>,
    inner: CheckedTerm<'db>,
    expected_ty: &RcValue<'db>,
) -> Result<CheckedTerm<'db>, KernelError> {
    // Force expected type to WHNF
    let expected_ty = ctx.whnf(expected_ty.clone()).await?;

    // Extract Lift type
    let inner_ty = match &*expected_ty {
        Value::Lift(lift) => lift.ty.clone(),
        _ => return Err(KernelError::ExpectedLift { got: expected_ty }),
    };

    // Verify inner term has the lifted type
    ctx.unify(inner.ty.clone(), inner_ty, expected_ty.clone()).await?;

    // Construct lift term (same as Lift type constructor)
    let lift_term = Syntax::lift_rc(inner.term);

    Ok(CheckedTerm::new_unchecked(lift_term, expected_ty))
}

// Similar functions for SLift, MLift, HArrow, etc.
```

---

### **Phase 3: Universe Level Inference**
**Priority:** HIGH (Type Safety Issue)
**Estimated:** ~150 lines
**Dependencies:** Phase 2b

Replace hardcoded `UniverseLevel::new(0)` with proper inference.

**File: `crates/hwml-core/src/kernel/universe.rs`**
```rust
/// Infer the universe level of a Pi type: max(level(A), level(B))
pub fn infer_pi_universe<'db>(
    source_level: UniverseLevel,
    target_level: UniverseLevel,
) -> UniverseLevel {
    source_level.max(target_level)
}

/// Infer the universe level of an arrow type: max(level(A), level(B))
pub fn infer_arrow_universe<'db>(
    source_level: UniverseLevel,
    target_level: UniverseLevel,
) -> UniverseLevel {
    source_level.max(target_level)
}
```

Update `check_pi` and `check_arrow` to use these functions.

---

### **Phase 4: Elaborator Refactor**
**Priority:** HIGH
**Estimated:** ~1500 lines
**Dependencies:** Phases 2a, 2b, 2c

Refactor the elaborator to use the kernel API instead of constructing `Syntax` directly.

#### Changes:

**File: `crates/hwml-elab/src/elaborator.rs`**

1. **Update context to hold kernel context:**
```rust
pub struct ElaborationContext<'db, 'g> {
    db: &'db dyn salsa::Database,
    source_file: Option<SourceFile>,
    kernel: KernelContext<'db, 'g>,  // ← NEW: replaces solver
    scope: Vec<String>,
    primitives: HashMap<String, PrimitiveInfo<'db>>,
    diagnostics: Vec<Diagnostic>,
}
```

2. **Update `check` signature to return `CheckedTerm`:**
```rust
#[async_recursion::async_recursion(?Send)]
pub async fn check<'db, 'g>(
    ctx: &mut ElaborationContext<'db, 'g>,
    expr: &surface::Expression,
    expected_ty: RcValue<'db>,
) -> Result<CheckedTerm<'db>, String>  // ← Returns CheckedTerm
```

3. **Update `synth` signature to return `SynthesizedTerm`:**
```rust
#[async_recursion::async_recursion(?Send)]
pub async fn synth<'db, 'g>(
    ctx: &mut ElaborationContext<'db, 'g>,
    expr: &surface::Expression,
) -> Result<SynthesizedTerm<'db>, String>  // ← Returns SynthesizedTerm
```

4. **Refactor all elaboration functions:**

**Before:**
```rust
async fn check_fun<'db, 'g>(
    ctx: &mut ElaborationContext<'db, 'g>,
    fun: &surface::Fun,
    expected_ty: RcValue<'db>,
) -> RcSyntax<'db> {
    // ... extract Pi type ...
    let body_term = check(ctx, &fun.body, target_ty).await;
    Syntax::lambda_rc(body_term)  // ❌ Direct construction
}
```

**After:**
```rust
async fn check_fun<'db, 'g>(
    ctx: &mut ElaborationContext<'db, 'g>,
    fun: &surface::Fun,
    expected_ty: RcValue<'db>,
) -> Result<CheckedTerm<'db>, String> {
    // Use kernel API
    kernel::check_lambda(&mut ctx.kernel, &expected_ty, |kernel_ctx| {
        Box::pin(async move {
            check(ctx, &fun.body, /* target_ty */).await
        })
    }).await.map_err(|e| format!("{:?}", e))
}
```

5. **Update all call sites** (~50 locations):
   - `check_pi` → `kernel::check_pi`
   - `synth_app` → `kernel::synth_app`
   - `synth_var` → `kernel::synth_var`
   - etc.

**Testing:**
- Run full elaborator test suite
- Verify no direct `Syntax::*_rc()` calls remain in elaborator
- Test with complex surface programs

---

## Summary: Total Effort Estimate

| Phase | Lines | Priority | Dependencies |
|-------|-------|----------|--------------|
| Phase 1: SourceRange Tracking | ~50 | HIGH | None |
| Phase 2a: Kernel Foundation | ~300 | HIGH | Phase 1 |
| Phase 2b: Core Judgements | ~500 | HIGH | Phase 2a |
| Phase 2c: Advanced Judgements | ~400 | MEDIUM | Phase 2b |
| Phase 3: Universe Inference | ~150 | HIGH | Phase 2b |
| Phase 4: Elaborator Refactor | ~1500 | HIGH | 2a, 2b, 2c |
| **Total** | **~2900** | | |

---

## Testing Strategy

### Unit Tests (Per Phase)
- Phase 2a: Token creation and context management
- Phase 2b: Each judgement function in isolation
- Phase 2c: Pattern matching and lifting
- Phase 4: Full elaboration with kernel API

### Integration Tests
- Elaborate complex surface programs
- Verify type preservation: `eval(check(e, T)) : T`
- Verify substitution lemma
- Verify universe consistency

### Property-Based Tests
- Roundtrip: `quote(eval(term)) ≡ term`
- Type preservation under substitution
- Confluence of reduction

---

**End of Implementation Plan**


