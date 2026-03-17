# Architectural Update: Bidirectional Judgements in the Kernel

**Date:** 2026-03-12  
**Status:** Design Proposal  
**Inspired by:** LCF-style systems (Project Pterodactyl)

---

## Core Principle

The Kernel must not just be a collection of AST constructors; it must **encode the bidirectional typing rules natively** to guarantee that synthesized types perfectly match their terms.

Every term construction in the kernel returns **both** the term **and** its type, bundled together as a proof that the term is well-typed.

---

## Phase 2: The Trusted Kernel (Judgement API)

### 1. The Tokens

```rust
// crates/hwml-core/src/kernel/mod.rs

/// A term that has been **checked** against a known type.
/// Invariant: The wrapped term has the specified type.
#[derive(Clone, Debug)]
pub struct CheckedTerm<'db> {
    term: RcSyntax<'db>,
    ty: RcValue<'db>,
}

/// A term whose type has been **synthesized**.
/// Invariant: The wrapped term has exactly the synthesized type.
#[derive(Clone, Debug)]
pub struct SynthesizedTerm<'db> {
    term: RcSyntax<'db>,
    ty: RcValue<'db>,
}

/// A type that has been verified to be well-formed in a universe.
#[derive(Clone, Debug)]
pub struct WellFormedType<'db> {
    ty: RcValue<'db>,
    universe: UniverseLevel,
}
```

**Key invariants:**
- `CheckedTerm<'db>` guarantees `Γ ⊢ term ⇐ ty`
- `SynthesizedTerm<'db>` guarantees `Γ ⊢ term ⇒ ty`
- `WellFormedType<'db>` guarantees `Γ ⊢ ty : U_level`

### 2. Extraction (Read-Only)

```rust
impl<'db> CheckedTerm<'db> {
    /// Extract the underlying syntax (read-only).
    pub fn syntax(&self) -> &RcSyntax<'db> {
        &self.term
    }
    
    /// Extract the type (read-only).
    pub fn ty(&self) -> &RcValue<'db> {
        &self.ty
    }
    
    /// Consume and extract both (for final elaboration result).
    pub fn into_parts(self) -> (RcSyntax<'db>, RcValue<'db>) {
        (self.term, self.ty)
    }
}

impl<'db> SynthesizedTerm<'db> {
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
```

### 3. Bidirectional Judgement API

#### **Check Mode** (Introduction Forms)

```rust
/// Γ ⊢ λx. body ⇐ (x : A) → B
pub async fn check_lambda<'db, 'g>(
    ctx: &KernelContext<'db, 'g>,
    expected_ty: &WellFormedType<'db>,  // Must be a Pi type
    body_checker: impl FnOnce(&KernelContext<'db, 'g>) -> Pin<Box<dyn Future<Output = CheckedTerm<'db>> + 'g>>,
) -> Result<CheckedTerm<'db>, KernelError>

/// Γ ⊢ (x : A) → B ⇐ U_i
pub async fn check_pi<'db, 'g>(
    ctx: &KernelContext<'db, 'g>,
    source: CheckedTerm<'db>,           // A : U_j
    target_checker: impl FnOnce(&KernelContext<'db, 'g>) -> Pin<Box<dyn Future<Output = CheckedTerm<'db>> + 'g>>,
) -> Result<CheckedTerm<'db>, KernelError>

/// Γ ⊢ term ⇐ expected_ty (via synthesis + conversion)
pub async fn check_by_synth<'db, 'g>(
    ctx: &KernelContext<'db, 'g>,
    term: SynthesizedTerm<'db>,
    expected_ty: &WellFormedType<'db>,
) -> Result<CheckedTerm<'db>, KernelError>
```

#### **Synth Mode** (Elimination Forms)

```rust
/// Γ ⊢ f a ⇒ B[a/x]  (given Γ ⊢ f ⇒ (x : A) → B)
pub async fn synth_app<'db, 'g>(
    ctx: &KernelContext<'db, 'g>,
    func: SynthesizedTerm<'db>,         // f : (x : A) → B
    arg: CheckedTerm<'db>,              // a : A
) -> Result<SynthesizedTerm<'db>, KernelError>

/// Γ ⊢ x ⇒ Γ(x)
pub async fn synth_var<'db, 'g>(
    ctx: &KernelContext<'db, 'g>,
    index: Index,
) -> Result<SynthesizedTerm<'db>, KernelError>

/// Γ ⊢ c ⇒ type(c)  (for constants)
pub async fn synth_constant<'db, 'g>(
    ctx: &KernelContext<'db, 'g>,
    constant: QualifiedName<'db>,
) -> Result<SynthesizedTerm<'db>, KernelError>

/// Γ ⊢ ?M ⇒ type(?M)  (for metavariables)
pub async fn synth_meta<'db, 'g>(
    ctx: &KernelContext<'db, 'g>,
    meta_id: MetaVariableId,
) -> Result<SynthesizedTerm<'db>, KernelError>
```

#### **Pattern Matching**

```rust
/// Γ ⊢ case scrut of { branches } ⇐ motive(scrut)
pub async fn check_case<'db, 'g>(
    ctx: &KernelContext<'db, 'g>,
    scrut: SynthesizedTerm<'db>,        // scrutinee : DataType args
    motive: Closure<'db>,                // motive : DataType args → U_i
    branches: Vec<CaseBranch<'db>>,
    expected_ty: &WellFormedType<'db>,
) -> Result<CheckedTerm<'db>, KernelError>
```

#### **Universe and Lifting**

```rust
/// Γ ⊢ U_i ⇒ U_{i+1}
pub async fn synth_universe<'db, 'g>(
    ctx: &KernelContext<'db, 'g>,
    level: UniverseLevel,
) -> Result<SynthesizedTerm<'db>, KernelError>

/// Γ ⊢ Lift A ⇐ U_{i+1}  (given A : U_i)
pub async fn check_lift<'db, 'g>(
    ctx: &KernelContext<'db, 'g>,
    inner: CheckedTerm<'db>,            // A : U_i
) -> Result<CheckedTerm<'db>, KernelError>

/// Γ ⊢ lift a ⇐ Lift A  (given a : A)
pub async fn check_lift_intro<'db, 'g>(
    ctx: &KernelContext<'db, 'g>,
    inner: CheckedTerm<'db>,            // a : A
    expected_ty: &WellFormedType<'db>,  // Lift A
) -> Result<CheckedTerm<'db>, KernelError>
```

---

## 4. The Kernel Context

The kernel maintains its own context that tracks the typing environment:

```rust
pub struct KernelContext<'db, 'g> {
    /// The solver environment (for metavariables and async operations)
    solver: SolverEnvironment<'db, 'g>,

    /// The typing context (parallel to the elaborator's scope)
    /// Maps de Bruijn levels to their types
    types: Vec<RcValue<'db>>,

    /// The value environment (for evaluation)
    values: LocalEnv<'db>,

    /// SourceRange tracking for error reporting
    location: SourceRange,
}

impl<'db, 'g> KernelContext<'db, 'g> {
    /// Push a new binding into the context
    pub fn push_binding(&mut self, ty: RcValue<'db>) -> Level {
        let level = self.types.len();
        self.types.push(ty);
        // Also extend the value environment with a fresh variable
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
        // Force metavariable solutions
        let forced = force(&self.solver, value)?;
        // TODO: Add async WHNF reduction if needed
        Ok(forced)
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
            .map_err(KernelError::from)
    }
}
```

---

## 5. Error Handling

```rust
#[derive(Debug, Clone)]
pub enum KernelError {
    /// Variable is not bound in the context
    UnboundVariable { index: Index },

    /// Expected a Pi type but got something else
    ExpectedPi { got: RcValue<'db> },

    /// Expected a specific type constructor
    ExpectedTypeConstructor { expected: QualifiedName<'db>, got: RcValue<'db> },

    /// Type mismatch during conversion check
    TypeMismatch {
        expected: RcValue<'db>,
        got: RcValue<'db>,
        location: SourceRange,
    },

    /// Unification failed
    UnificationFailed(unify::Error),

    /// Evaluation error
    EvaluationFailed(eval::Error),

    /// Universe level mismatch
    UniverseLevelMismatch {
        expected: UniverseLevel,
        got: UniverseLevel,
    },
}
```

---

## 6. Private Syntax Constructors

All `Syntax` constructors become `pub(crate)` within `hwml-core`, visible only to the `kernel` module:

```rust
// crates/hwml-core/src/syn/basic.rs

impl<'db> Syntax<'db> {
    // All constructors become pub(crate)
    pub(crate) fn lambda_rc(body: RcSyntax<'db>) -> RcSyntax<'db> {
        Rc::new(Syntax::Lambda(Lambda::new(body)))
    }

    pub(crate) fn application_rc(
        func: RcSyntax<'db>,
        arg: RcSyntax<'db>,
    ) -> RcSyntax<'db> {
        Rc::new(Syntax::Application(Application::new(func, arg)))
    }

    // ... all other constructors
}
```

**Only the kernel module can construct `Syntax` nodes.**

---

## Phase 4: Refactor Elaborator to Use Kernel API

The elaborator becomes a **client** of the kernel, calling judgement functions instead of constructing syntax directly.

### Before (Current):

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

### After (With Kernel):

```rust
async fn check_fun<'db, 'g>(
    ctx: &mut ElaborationContext<'db, 'g>,
    fun: &surface::Fun,
    expected_ty: RcValue<'db>,
) -> CheckedTerm<'db> {
    // Verify expected_ty is a Pi type
    let pi_type = ctx.kernel.verify_pi_type(expected_ty)?;

    // Check the body in extended context
    let body_checked = ctx.kernel.check_lambda(
        &pi_type,
        |kernel_ctx| Box::pin(async move {
            // Recursively elaborate the body
            check(ctx, &fun.body, pi_type.target_type()).await
        })
    ).await?;

    body_checked  // ✅ Returns CheckedTerm with proof
}
```

---

## 7. Benefits of This Approach

### Type Safety by Construction
- **Impossible to construct ill-typed terms**: Every `CheckedTerm` and `SynthesizedTerm` carries a proof of well-typedness
- **No post-hoc validation needed**: The kernel API enforces typing rules at construction time

### Clear Separation of Concerns
- **Kernel**: Trusted core, implements typing rules, constructs syntax
- **Elaborator**: Untrusted client, handles name resolution, implicit insertion, pattern compilation

### Async-Friendly
- All kernel functions are `async`, allowing them to block on metavariable resolution
- Unification is integrated into the kernel context

### Error Localization
- Kernel errors are precise and localized to specific judgement failures
- SourceRange tracking flows through the kernel context

---

## 8. Implementation Phases (Revised)

### Phase 2a: Kernel Foundation (~300 lines)
1. Define `CheckedTerm`, `SynthesizedTerm`, `WellFormedType` tokens
2. Implement `KernelContext` with binding management
3. Define `KernelError` enum
4. Make `Syntax` constructors `pub(crate)`

### Phase 2b: Core Judgements (~500 lines)
1. Implement `check_lambda`, `check_pi`
2. Implement `synth_app`, `synth_var`, `synth_constant`
3. Implement `check_by_synth` (synthesis + conversion)
4. Implement universe and lifting judgements

### Phase 2c: Advanced Judgements (~400 lines)
1. Implement `check_case` for pattern matching
2. Implement hardware-specific judgements (SLift, MLift, HArrow)
3. Implement equality type judgements

### Phase 4: Elaborator Refactor (~1500 lines)
1. Update `ElaborationContext` to hold a `KernelContext`
2. Refactor `check` to return `CheckedTerm`
3. Refactor `synth` to return `SynthesizedTerm`
4. Update all elaboration functions to use kernel API
5. Remove all direct `Syntax::*_rc()` calls from elaborator

---

## 9. Testing Strategy

### Kernel Unit Tests
```rust
#[cfg(test)]
mod tests {
    #[tokio::test]
    async fn test_check_lambda_well_typed() {
        // Γ ⊢ λx. x ⇐ A → A
        let ctx = setup_kernel_context();
        let a_type = /* ... */;
        let pi_type = WellFormedType::pi(a_type.clone(), a_type.clone());

        let lambda = ctx.check_lambda(&pi_type, |ctx| {
            Box::pin(async move {
                ctx.synth_var(Index::new(0)).await
            })
        }).await;

        assert!(lambda.is_ok());
    }

    #[tokio::test]
    async fn test_synth_app_type_correct() {
        // Γ ⊢ (λx. x) a ⇒ A  (given a : A)
        // ...
    }
}
```

### Property-Based Tests
- **Roundtrip**: `quote(eval(term)) ≡ term` for all kernel-constructed terms
- **Type preservation**: If `check_lambda` succeeds, the result evaluates to a lambda value
- **Substitution lemma**: Kernel respects substitution in Pi types

---

**End of Design Document**


