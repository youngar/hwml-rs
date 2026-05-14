# Implicit Arguments Implementation Plan

**Created:** 2026-05-13
**Target:** 5 weeks (25 working days)
**Approach:** Dynamic Order Elaboration (DOE)
**Complexity:** ~150 LOC overhead for DOE, ~500 LOC total

---

## Overview

This plan implements implicit function arguments (`{A : Type} → A → A`) using Dynamic Order Elaboration (DOE), the simplest and most practical solution for first-class polymorphism.

**References:**
- Research: `wiki/research/implicit-arguments-first-class-polymorphism.md`
- Source: [elaboration-zoo/06-first-class-poly](https://github.com/AndrasKovacs/elaboration-zoo/tree/master/06-first-class-poly)

---

## Phase 1: Icit Infrastructure (Week 1)

**Goal:** Add visibility tracking to core types, no elaboration changes yet.

### Task 1.1: Core Icit Enum (Day 1)

**File:** `crates/hwml-core/src/common.rs`

**Add:**
```rust
/// Implicitness/Explicitness of function arguments
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Icit {
    /// Explicit argument: `(x : A) → B`
    Explicit,
    /// Implicit argument: `{x : A} → B`
    Implicit,
}

impl Icit {
    pub fn is_implicit(&self) -> bool {
        matches!(self, Icit::Implicit)
    }

    pub fn is_explicit(&self) -> bool {
        matches!(self, Icit::Explicit)
    }
}

impl Default for Icit {
    fn default() -> Self {
        Icit::Explicit
    }
}
```

**Tests:**
```rust
#[test]
fn test_icit_basic() {
    assert!(Icit::Implicit.is_implicit());
    assert!(Icit::Explicit.is_explicit());
    assert_eq!(Icit::default(), Icit::Explicit);
}
```

### Task 1.2: Update Syntax Types (Day 1-2)

**File:** `crates/hwml-core/src/syn/syntax.rs`

**Changes:**

1. **Update PiCode:**
```rust
// OLD
PiCode(RcSyntax<'db>, BindingSyntax<'db>)

// NEW
PiCode(RcSyntax<'db>, Icit, BindingSyntax<'db>)
```

2. **Update Application:**
```rust
// OLD
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct Application<'db> {
    pub function: RcSyntax<'db>,
    pub argument: RcSyntax<'db>,
}

// NEW
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct Application<'db> {
    pub function: RcSyntax<'db>,
    pub argument: RcSyntax<'db>,
    pub icit: Icit,
}

impl<'db> Application<'db> {
    pub fn new(function: RcSyntax<'db>, argument: RcSyntax<'db>, icit: Icit) -> Self {
        Application { function, argument, icit }
    }

    pub fn explicit(function: RcSyntax<'db>, argument: RcSyntax<'db>) -> Self {
        Self::new(function, argument, Icit::Explicit)
    }

    pub fn implicit(function: RcSyntax<'db>, argument: RcSyntax<'db>) -> Self {
        Self::new(function, argument, Icit::Implicit)
    }
}
```

3. **Update Lambda** (CRITICAL - Lambda MUST track Icit):
```rust
// OLD
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct Lambda<'db> {
    pub body: BindingSyntax<'db>,
}

// NEW - Lambda MUST know if it's implicit or explicit!
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct Lambda<'db> {
    pub icit: Icit,  // ← CRITICAL: Needed for quotation & sanity checks
    pub body: BindingSyntax<'db>,
}

impl<'db> Lambda<'db> {
    pub fn new(icit: Icit, body: BindingSyntax<'db>) -> Lambda<'db> {
        Lambda { icit, body }
    }

    pub fn explicit(body: BindingSyntax<'db>) -> Lambda<'db> {
        Lambda::new(Icit::Explicit, body)
    }

    pub fn implicit(body: BindingSyntax<'db>) -> Lambda<'db> {
        Lambda::new(Icit::Implicit, body)
    }
}
```

**Why Lambda needs Icit:**
1. **Quotation**: When quoting `Value::Lambda` back to `Syntax`, we need to know if it's `λ {A}` or `λ A`
2. **Sanity checking**: During β-reduction, verify that application Icit matches lambda Icit
3. **Pretty printing**: Display implicit vs explicit lambdas correctly

4. **Update constructors in `Syntax` impl:**
```rust
impl<'db> Syntax<'db> {
    pub fn pi(dom: RcSyntax<'db>, icit: Icit, cod: BindingSyntax<'db>) -> Syntax<'db> {
        Syntax::PiCode(dom, icit, cod)
    }

    pub fn pi_rc(dom: RcSyntax<'db>, icit: Icit, cod: BindingSyntax<'db>) -> RcSyntax<'db> {
        Rc::new(Syntax::pi(dom, icit, cod))
    }

    pub fn lambda(icit: Icit, body: BindingSyntax<'db>) -> Syntax<'db> {
        Syntax::Lambda(Lambda::new(icit, body))
    }

    pub fn lambda_rc(icit: Icit, body: BindingSyntax<'db>) -> RcSyntax<'db> {
        Rc::new(Syntax::lambda(icit, body))
    }

    pub fn app(fun: RcSyntax<'db>, arg: RcSyntax<'db>, icit: Icit) -> Syntax<'db> {
        Syntax::Application(Application::new(fun, arg, icit))
    }

    pub fn app_rc(fun: RcSyntax<'db>, arg: RcSyntax<'db>, icit: Icit) -> RcSyntax<'db> {
        Rc::new(Syntax::app(fun, arg, icit))
    }
}
```

**Compilation fixes:** Update all PiCode/Application construction sites to include Icit::Explicit (default).

### Task 1.3: Update Value Types (Day 2)

**File:** `crates/hwml-core/src/val.rs`

**Changes:**

1. **Update Value::PiCode:**
```rust
// OLD
PiCode(RcValue<'db>, Closure<'db>)

// NEW
PiCode(RcValue<'db>, Icit, Closure<'db>)
```

2. **Update val::Lambda** (the Value domain lambda):
```rust
// OLD
#[derive(Clone, Debug)]
pub struct Lambda<'db> {
    pub body: Closure<'db>,
}

// NEW - Lambda in Value domain also tracks Icit
#[derive(Clone, Debug)]
pub struct Lambda<'db> {
    pub icit: Icit,  // ← CRITICAL: Preserved from Syntax lambda
    pub body: Closure<'db>,
}

impl<'db> Lambda<'db> {
    pub fn new(icit: Icit, body: Closure<'db>) -> Lambda<'db> {
        Lambda { icit, body }
    }
}
```

3. **Update Eliminator::Application:**
```rust
// OLD
#[derive(Clone, Debug)]
pub struct Application<'db> {
    pub argument: Normal<'db>,
}

// NEW
#[derive(Clone, Debug)]
pub struct Application<'db> {
    pub argument: Normal<'db>,
    pub icit: Icit,
}

impl<'db> Application<'db> {
    pub fn new(argument: Normal<'db>, icit: Icit) -> Self {
        Application { argument, icit }
    }

    pub fn explicit(argument: Normal<'db>) -> Self {
        Self::new(argument, Icit::Explicit)
    }

    pub fn implicit(argument: Normal<'db>) -> Self {
        Self::new(argument, Icit::Implicit)
    }
}
```

4. **Update Eliminator constructors:**
```rust
impl<'db> Eliminator<'db> {
    pub fn application(argument: Normal<'db>, icit: Icit) -> Eliminator<'db> {
        Eliminator::Application(Application::new(argument, icit))
    }
}
```

5. **Update Value constructors:**
```rust
impl<'db> Value<'db> {
    pub fn pi(dom: RcValue<'db>, icit: Icit, cod: Closure<'db>) -> Value<'db> {
        Value::PiCode(dom, icit, cod)
    }

    pub fn pi_rc(dom: RcValue<'db>, icit: Icit, cod: Closure<'db>) -> RcValue<'db> {
        Rc::new(Value::pi(dom, icit, cod))
    }

    pub fn lambda(icit: Icit, body: Closure<'db>) -> Value<'db> {
        Value::Lambda(Lambda::new(icit, body))
    }

    pub fn lambda_rc(icit: Icit, body: Closure<'db>) -> RcValue<'db> {
        Rc::new(Value::lambda(icit, body))
    }
}
```

**Compilation fixes:** Update all PiCode/Application construction sites.

### Task 1.4: Update Evaluation (Day 3) - CORRECTED

**File:** `crates/hwml-core/src/eval.rs`

**CRITICAL: Current architecture is correct - don't add type inference to eval!**

**Changes:**

```rust
// 1. Evaluate Lambda - PRESERVE Icit
fn eval_lambda<'db, 'g>(
    env: &mut Environment<'db, 'g>,
    lambda: &syn::Lambda<'db>,
) -> Result<RcValue<'db>, Error<'db>> {
    Ok(Value::lambda_rc(
        lambda.icit,  // ← PRESERVE Icit from syntax
        Closure::new(env.local.clone(), lambda.body.term().clone())
    ))
}

// 2. Evaluate PiCode with Icit
Syntax::PiCode(dom, icit, cod) => {
    let dom_val = eval(env, dom)?;
    Ok(Value::pi_rc(dom_val, *icit, Closure::new(env.local.clone(), cod.term.clone())))
}

// 3. Evaluate Application - PASS Icit through
fn eval_application<'db, 'g>(
    env: &mut Environment<'db, 'g>,
    application: &syn::Application<'db>,
) -> Result<RcValue<'db>, Error<'db>> {
    let fun = eval(env, &application.function)?;
    let arg = eval(env, &application.argument)?;
    // PASS Icit to run_application
    run_application(&env.global, &*fun, arg, application.icit)
}
```

**Update run_application signature:**
```rust
pub fn run_application<'db>(
    global: &GlobalEnv<'db>,
    fun: &Value<'db>,
    arg: RcValue<'db>,
    arg_icit: Icit,  // ← ADD THIS
) -> Result<RcValue<'db>, Error<'db>> {
    match fun {
        Value::Lambda(lambda) => {
            apply_lambda(global, lambda, arg, arg_icit)
        }
        Value::Rigid(rigid) => {
            apply_rigid(global, rigid, arg, arg_icit)
        }
        Value::Flex(flex) => {
            apply_flex(global, flex, arg, arg_icit)
        }
        Value::Constant(constant) => {
            apply_constant(global, constant, arg, arg_icit)
        }
        _ => Err(Error::BadApplication { loc: None }),
    }
}
```

**Update apply_lambda - ADD SANITY CHECK:**
```rust
pub fn apply_lambda<'db>(
    global: &GlobalEnv<'db>,
    lambda: &val::Lambda<'db>,
    arg: RcValue<'db>,
    arg_icit: Icit,  // ← ADD THIS
) -> Result<RcValue<'db>, Error<'db>> {
    // CRITICAL SANITY CHECK
    debug_assert_eq!(
        lambda.icit, arg_icit,
        "Compiler bug: Applied {:?} argument to {:?} lambda",
        arg_icit, lambda.icit
    );

    // β-reduction (Icit doesn't affect computation, just checked for correctness)
    run_closure(global, &lambda.body, [arg])
}
```

**Update apply_rigid - Extract Icit from Pi type:**
```rust
fn apply_rigid<'db>(
    global: &GlobalEnv<'db>,
    rigid: &Rigid<'db>,
    arg: RcValue<'db>,
    arg_icit: Icit,  // ← ADD THIS
) -> Result<RcValue<'db>, Error<'db>> {
    // Extract type info from rigid's Pi type (CURRENT ARCHITECTURE - KEEP IT!)
    let Value::PiCode(source_ty, pi_icit, target) = rigid.ty.as_ref() else {
        return Err(Error::BadApplication { loc: None });
    };

    // SANITY CHECK: Icit matches
    debug_assert_eq!(*pi_icit, arg_icit, "Icit mismatch in rigid application");

    // Build Normal with type from Pi (NO TYPE INFERENCE - just extract from Pi!)
    let arg_normal = Normal::new(source_ty.clone(), arg.clone());
    let target_ty = run_closure(global, target, [arg])?;

    // Extend spine
    let mut spine = rigid.spine.clone();
    spine.push(Eliminator::application(arg_normal, arg_icit));

    Ok(Value::rigid_rc(rigid.head.clone(), spine, target_ty))
}
```

**Similar for apply_flex:**
```rust
fn apply_flex<'db>(
    global: &GlobalEnv<'db>,
    flex: &Flex<'db>,
    arg: RcValue<'db>,
    arg_icit: Icit,  // ← ADD THIS
) -> Result<RcValue<'db>, Error<'db>> {
    // Extract type from flex's Pi type (CURRENT ARCHITECTURE)
    let Value::PiCode(source_ty, pi_icit, target) = flex.ty.as_ref() else {
        return Err(Error::BadApplication { loc: None });
    };

    // SANITY CHECK
    debug_assert_eq!(*pi_icit, arg_icit, "Icit mismatch in flex application");

    // Rest is same as current code
    let arg_normal = Normal::new(source_ty.clone(), arg.clone());
    let target_ty = run_closure(global, target, [arg])?;

    let mut spine = flex.spine.clone();
    spine.push(Eliminator::application(arg_normal, arg_icit));

    Ok(Value::flex_rc(flex.head.clone(), spine, target_ty))
}
```

**Key points:**
1. ✅ NO type inference in eval - types come from Pi for neutrals
2. ✅ Lambda stores Icit, checked during β-reduction
3. ✅ Icit passed through entire application chain
4. ✅ Sanity checks with debug_assert (zero runtime cost in release)

### Task 1.5: Update Quotation (Day 3) - CORRECTED

**File:** `crates/hwml-core/src/quote.rs`

**Changes:**

```rust
// 1. Quote PiCode with Icit
Value::PiCode(dom, icit, cod) => {
    let dom_syn = quote(global, depth, dom, /* dom type */)?;

    // Create fresh variable
    let var = Value::variable_rc(Level::new(depth), dom.clone());

    // Apply closure and quote body
    let cod_val = cod.apply(global, &var)?;
    let cod_syn = quote(global, depth + 1, &cod_val, /* cod type */)?;

    // Build Pi with Icit
    Ok(Syntax::pi_rc(dom_syn, *icit, Binding::new(None, cod_syn)))
}

// 2. Quote Lambda - PRESERVE Icit
Value::Lambda(lam) => {
    // Create fresh variable
    // Apply closure to get body
    // Quote body

    let var = Value::variable_rc(Level::new(depth), /* dom type from context */);
    let body_val = lam.body.apply(global, &var)?;
    let body_syn = quote(global, depth + 1, &body_val, /* body type */)?;

    // BUILD LAMBDA WITH Icit - CRITICAL!
    Ok(Syntax::lambda_rc(lam.icit, Binding::new(None, body_syn)))
}

// 3. Quote Rigid with Icit in spine
Value::Rigid(rigid) => {
    // Quote head
    let head_syn = quote_variable(rigid.head.level, depth);

    // Quote spine - this rebuilds applications with Icit preserved
    let result = quote_spine(global, depth, head_syn, &rigid.spine)?;
    Ok(result)
}

fn quote_spine<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    head: RcSyntax<'db>,
    spine: &Spine<'db>,
) -> Result<RcSyntax<'db>, QuoteError> {
    let mut result = head;

    for elim in spine.iter() {
        match elim {
            Eliminator::Application(app) => {
                // Quote argument value
                let arg_syn = quote(global, depth, &app.argument.value, &app.argument.ty)?;

                // Build application with PRESERVED Icit
                result = Syntax::app_rc(result, arg_syn, app.icit);
            }
            Eliminator::Case(case) => {
                // Handle case eliminator
                // ...
            }
        }
    }

    Ok(result)
}

// Similar for Flex
Value::Flex(flex) => {
    let head_syn = quote_metavariable(global, depth, &flex.head)?;
    quote_spine(global, depth, head_syn, &flex.spine)
}
```

**Key points:**
1. ✅ Lambda quotation preserves Icit
2. ✅ Spine quotation preserves Icit in applications
3. ✅ `λ {A}. ...` quotes back as implicit lambda
4. ✅ Pretty printer will show correct syntax

### Task 1.6: Update Equality Checking (Day 4)

**File:** `crates/hwml-core/src/equal.rs`

**Changes:**

```rust
// In convertibility checking:
pub fn is_convertible<'db>(
    global: &GlobalEnv<'db>,
    val1: &Value<'db>,
    val2: &Value<'db>,
) -> Result<bool, Error> {
    match (val1, val2) {
        (Value::PiCode(dom1, icit1, cod1), Value::PiCode(dom2, icit2, cod2)) => {
            // STRICT ICIT MATCHING - {A} ≠ (A)
            if icit1 != icit2 {
                return Ok(false);
            }

            // Check domain and codomain convertibility
            // ... (existing logic with fresh variables)
        }

        (Value::Lambda(lam1), lam2), Value::Lambda(lam2)) => {
            // STRICT ICIT MATCHING - λ {A} ≠ λ A
            if lam1.icit != lam2.icit {
                return Ok(false);
            }

            // Check body convertibility with fresh variable
            // ...
        }

        // For neutrals: compare spines element-wise
        (Value::Rigid(r1), Value::Rigid(r2)) => {
            if r1.head != r2.head {
                return Ok(false);
            }
            compare_spines(global, &r1.spine, &r2.spine)
        }

        (Value::Flex(f1), Value::Flex(f2)) => {
            if f1.head.id != f2.head.id {
                return Ok(false);
            }
            compare_spines(global, &f1.spine, &f2.spine)
        }
        // ...
    }
}

fn compare_spines<'db>(
    global: &GlobalEnv<'db>,
    spine1: &Spine<'db>,
    spine2: &Spine<'db>,
) -> Result<bool, Error> {
    if spine1.len() != spine2.len() {
        return Ok(false);
    }

    for (elim1, elim2) in spine1.iter().zip(spine2.iter()) {
        match (elim1, elim2) {
            (Eliminator::Application(app1), Eliminator::Application(app2)) => {
                // STRICT ICIT MATCHING - f {x} ≠ f x
                if app1.icit != app2.icit {
                    return Ok(false);
                }

                // Compare argument values
                if !is_convertible(global, &app1.argument.value, &app2.argument.value)? {
                    return Ok(false);
                }
            }
            _ => // Handle other eliminators
        }
    }

    Ok(true)
}
```

**Key points:**
1. ✅ Strict Icit matching in Pi types
2. ✅ Strict Icit matching in Lambda values
3. ✅ Strict Icit matching in spine applications
4. ✅ `{A} → B` is NOT convertible with `(A) → B`
5. ✅ `f {x}` is NOT convertible with `f x`

### Task 1.7: Update Pattern Unification (Day 4)

**File:** `crates/hwml-core/src/pattern_unify.rs`

**Changes:**

```rust
// Pattern unification already works on Value domain
// Just need to ensure Icit is checked during spine comparison

pub fn unify<'db>(
    global: &GlobalEnv<'db>,
    val1: &Value<'db>,
    val2: &Value<'db>,
) -> Result<(), UnifyError> {
    match (val1, val2) {
        (Value::PiCode(dom1, icit1, cod1), Value::PiCode(dom2, icit2, cod2)) => {
            // Icit must match
            if icit1 != icit2 {
                return Err(UnifyError::NotConvertible);
            }

            // Unify domain
            unify(global, dom1, dom2)?;

            // Unify codomain with fresh variable
            // ...
        }

        // Spine unification already uses is_convertible,
        // which now checks Icit, so no changes needed!

        // Pattern unification case:
        (Value::Flex(flex), rhs) | (rhs, Value::Flex(flex)) => {
            pattern_unify(global, flex, rhs)?;
        }

        _ => {
            // Fall back to convertibility check (which now handles Icit)
            if !is_convertible(global, val1, val2)? {
                return Err(UnifyError::NotConvertible);
            }
        }
    }
    Ok(())
}
```

**No major changes needed** - equality checking already handles Icit!

### Task 1.8: Update Printer (Day 5)

**File:** `crates/hwml-core/src/syn/print.rs`

**Changes:**

```rust
// Print PiCode with Icit
Syntax::PiCode(dom, icit, cod) => {
    print_syntax(buf, dom);
    match icit {
        Icit::Explicit => buf.push_str(" → "),
        Icit::Implicit => buf.push_str(" →{} "),  // Or custom syntax
    }
    // Print codomain
}

// Print Lambda with Icit
Syntax::Lambda(lam) => {
    match lam.icit {
        Icit::Explicit => buf.push_str("λ "),
        Icit::Implicit => buf.push_str("λ{} "),  // Or λ {...}
    }
    // Print body
}

// Print Application with Icit
Syntax::Application(app) => {
    print_syntax(buf, &app.function);
    match app.icit {
        Icit::Explicit => {
            buf.push(' ');
            print_syntax(buf, &app.argument);
        }
        Icit::Implicit => {
            buf.push_str(" {");
            print_syntax(buf, &app.argument);
            buf.push('}');
        }
    }
}
```

**Surface syntax decision:** Choose notation for implicit in coordination with parser team.



### Task 1.9: Compilation Fixes (Day 5)

**Goal:** Make the entire workspace compile with all Icit changes.

**Strategy:**
1. Use `Icit::Explicit` as default everywhere initially
2. Search for all PiCode/Application construction sites
3. Update to pass Icit::Explicit explicitly
4. Fix any compilation errors

**Commands:**
```bash
# Find all PiCode constructions
rg "PiCode\(" --type rust

# Find all Application constructions
rg "Application\(" --type rust

# Find all Syntax::pi, Syntax::app calls
rg "Syntax::(pi|app)" --type rust

# Compile and fix errors iteratively
cargo check --workspace
```

**Expected files to update:**
- `crates/hwml-elab/src/elab/*.rs` - Elaboration logic
- `crates/hwml-core/tests/*.rs` - Core tests
- Any other files that construct core AST nodes

**Change pattern:**
```rust
// OLD
Syntax::PiCode(dom, cod)
Syntax::Application(Application { function, argument })

// NEW
Syntax::PiCode(dom, Icit::Explicit, cod)
Syntax::Application(Application { function, argument, icit: Icit::Explicit })

// Or using constructors:
Syntax::pi_rc(dom, Icit::Explicit, cod)
Syntax::app_rc(fun, arg, Icit::Explicit)
Application::explicit(fun, arg)
```

---

## Phase 1 Summary

### Deliverables

✅ **Week 1 Complete** when:

1. ✅ `Icit` enum exists in `common.rs`
2. ✅ All AST nodes (Syntax & Value) track Icit
3. ✅ Evaluation preserves and checks Icit
4. ✅ Quotation preserves Icit
5. ✅ Equality checking enforces strict Icit matching
6. ✅ Pattern unification respects Icit
7. ✅ Printer shows implicit vs explicit correctly
8. ✅ **All tests pass** with Icit::Explicit everywhere
9. ✅ Workspace compiles without warnings

### Testing Strategy

```bash
# After each task:
cargo check --workspace

# After Task 1.4 (Evaluation):
cargo test -p hwml_core --lib

# After Task 1.9 (Compilation fixes):
cargo test --workspace
```

### Success Criteria

**Phase 1 is complete when:**

1. ✅ No compilation errors
2. ✅ All 510 tests pass (same as before)
3. ✅ No behavioral changes (all uses Icit::Explicit)
4. ✅ Infrastructure ready for Phase 2 (parser)

### Files Modified Summary

| File | Lines Changed | Complexity |
|------|--------------|------------|
| `common.rs` | +15 | Low |
| `syntax.rs` | +50 | Medium |
| `val.rs` | +40 | Medium |
| `eval.rs` | +80 | High (critical) |
| `quote.rs` | +60 | High |
| `equal.rs` | +30 | Medium |
| `pattern_unify.rs` | +10 | Low |
| `print.rs` | +40 | Low |
| Various call sites | +200 | Low (mechanical) |
| **TOTAL** | **~525 LOC** | **5 days** |

---

## Critical Architectural Corrections Applied

### 🔧 Correction 1: Lambda MUST Track Icit

**Problem:** Original plan omitted Icit from Lambda
**Impact:** Quotation would fail, sanity checks impossible
**Fix:** Added `icit: Icit` to both `syn::Lambda` and `val::Lambda`

### 🔧 Correction 2: No Type Inference in Eval

**Problem:** Original plan suggested inferring types during eval
**Impact:** Performance trap in NbE hot path
**Fix:** Types come from Pi for neutrals, lambda just β-reduces

### 🔧 Correction 3: Icit Sanity Checking

**Problem:** No validation during application
**Impact:** Silent bugs when Icit mismatches
**Fix:** Added `debug_assert_eq!` in apply functions

---

## Next Steps After Phase 1

### Phase 2: Parser & Surface Syntax (Week 2)

**See:** `IMPLICIT-ARGUMENTS-IMPLEMENTATION-PLAN-PART2.md` for full details

**Preview:**
1. Extend surface AST with Icit
2. Parse `{x : A} → B` syntax
3. Parse `f {x}` implicit applications
4. Basic elaboration integration
5. Test simple cases

### Phase 3-5: DOE Implementation & Testing (Weeks 3-5)

**See:** `IMPLICIT-ARGUMENTS-IMPLEMENTATION-PLAN-PART2.md` for full details

**Preview:**
- Postponed checks
- Placeholder metas
- Retry logic
- Comprehensive testing

---

## Review Checklist

Before starting implementation:

- [ ] Read `wiki/research/implicit-arguments-first-class-polymorphism.md`
- [ ] Understand why Lambda needs Icit (quotation & sanity checks)
- [ ] Understand why eval doesn't infer types (performance)
- [ ] Review current NbE architecture (`eval.rs`, `quote.rs`)
- [ ] Set up tracking issue with 9 tasks for Phase 1

Before moving to Phase 2:

- [ ] All 510 tests pass
- [ ] No compiler warnings
- [ ] All TODOs/FIXMEs addressed
- [ ] Code review complete
- [ ] Update this document with any lessons learned

---

## Document History

- **Created:** 2026-05-13 (Initial DOE implementation plan)
- **Updated:** 2026-05-13 (Architectural corrections: Lambda Icit, eval performance, sanity checks)
- **Status:** Ready for implementation

**Related Documents:**
- `wiki/research/implicit-arguments-first-class-polymorphism.md` - Full research
- `IMPLICIT-ARGUMENTS-IMPLEMENTATION-PLAN-PART2.md` - Phases 2-5
- `IMPLICIT-ARGUMENTS-RESEARCH-SUMMARY.md` - Executive summary
- `IMPLICIT-ARGUMENTS-QUICK-REF.md` - Quick reference

---

**END OF PHASE 1 PLAN**
