# Migration Map: Old Architecture → NbE Architecture

This document maps the current `hwml-rust` architecture to the new NbE architecture.

## Type Definitions

### Old: `syn::Syntax<'db>` (Monolithic)

```rust
// OLD: crates/hwml-core/src/syn/syntax.rs
pub enum Syntax<'db> {
    Universe(Universe<'db>),           // Type 0, Type 1, ...
    Pi(Pi<'db>),                       // (x : A) -> B
    Lambda(Lambda<'db>),               // fun x => body
    Application(Application<'db>),     // f x
    Variable(Variable<'db>),           // %0, %1, ...
    Constant(Constant<'db>),           // @Nat, @zero
    Metavariable(Metavariable<'db>),   // ?M[x, y]
    TypeConstructor(...),              // Nat, Vec A n
    DataConstructor(...),              // zero, succ n
    HArrow(HArrow<'db>),               // Signal => Module
    // ... 30+ variants
}
```

### New: Split into 4 Enums

```rust
// NEW: crates/hwml-core/src/nbe/syntax.rs
pub enum Syntax<'db> {
    UniverseCode(usize),               // Type 0, Type 1 (codes only!)
    PiCode(RcSyntax, Binder),          // Pi type code
    Lam(Binder),                       // Lambda
    App(RcSyntax, RcSyntax),           // Application
    Var(Index),                        // Variable
    Const(QualifiedName),              // Constant
    Meta(MetaVariableId, Vec<RcSyntax>), // Metavariable
    TypeConstructorCode(...),          // Type constructor code
    DataConstructorCode(...),          // Data constructor
    HArrowCode(...),                   // Hardware arrow code
    // ... ~15 variants
}

// NEW: crates/hwml-core/src/nbe/value.rs
pub enum Value<'db> {
    UniverseCode(usize),               // Evaluated universe code
    PiCode(RcValue, Rc<Closure>),      // Evaluated Pi code
    Lam(Rc<Closure>),                  // Evaluated lambda
    Neutral(Rc<Neutral>),              // Stuck term
    // ... ~10 variants
}

// NEW: crates/hwml-core/src/nbe/ty.rs
pub enum TySyntax<'db> {
    UniverseType,                      // The type of Type 0, Type 1, ...
    Pi(RcTySyntax, TyBinder),          // Dependent function type
    HArrow(RcTySyntax, RcTySyntax),    // Hardware arrow type
    El(RcSyntax),                      // Decode a type code
    // ... ~7 variants
}

pub enum Ty<'db> {
    UniverseType,                      // Evaluated universe type
    Pi(RcTy, Rc<TyClosure>),           // Evaluated Pi type
    HArrow(RcTy, RcTy),                // Evaluated hardware arrow
    El(RcValue),                       // Decoded type code
    // ... ~7 variants
}
```

## Key Mappings

### Universe Types

| Old | New (Syntax) | New (Ty) |
|-----|--------------|----------|
| `Syntax::Universe(Universe { level: 0 })` | `Syntax::UniverseCode(0)` | `Ty::El(Value::UniverseCode(0))` |
| `Syntax::Universe(Universe { level: 1 })` | `Syntax::UniverseCode(1)` | `Ty::El(Value::UniverseCode(1))` |
| N/A (no top-level Type) | N/A | `Ty::UniverseType` |

### Function Types

| Old | New (Syntax) | New (Ty) |
|-----|--------------|----------|
| `Syntax::Pi(Pi { domain, target })` | `Syntax::PiCode(dom, Binder { body })` | `Ty::Pi(dom_ty, TyClosure { body })` |

**Key Difference:** In the new architecture, Pi is **both** a code (in `Syntax`) and a top-level type (in `Ty`).

### Lambdas

| Old | New (Syntax) | New (Value) |
|-----|--------------|-------------|
| `Syntax::Lambda(Lambda { body })` | `Syntax::Lam(Binder { body })` | `Value::Lam(Closure { env, body })` |

**Key Difference:** Values use closures (environment + body), not just syntax.

### Variables

| Old | New (Syntax) | New (Value) |
|-----|--------------|-------------|
| `Syntax::Variable(Variable { index })` | `Syntax::Var(index)` | `Value::Neutral(Neutral { head: Head::Var(level), spine: [] })` |

**Key Difference:** Values use **Levels**, syntax uses **Indices**.

### Metavariables

| Old | New (Syntax) | New (Value) |
|-----|--------------|-------------|
| `Syntax::Metavariable(Metavariable { id, substitution })` | `Syntax::Meta(id, subst)` | `Value::Neutral(Neutral { head: Head::Meta(id, subst), spine: [] })` |

**Key Difference:** Unsolved metas are neutral terms in the value domain.

## Function Mappings

### Evaluation

| Old | New |
|-----|-----|
| `eval::eval(env, syntax) -> Result<Value>` | `eval::eval(global, env, syntax) -> Result<Value>` |
| `eval::eval_universe(...)` | Handled in `eval` match arm |
| `eval::eval_pi(...)` | Handled in `eval` match arm |
| `eval::run_application(...)` | `eval::apply(global, fun, arg)` |

**Key Difference:** New evaluator is simpler (no separate functions for each variant).

### Quotation

| Old | New |
|-----|-----|
| `quote::quote(env, value, ty) -> Syntax` | `quote::quote(global, depth, value) -> Syntax` |
| `quote::quote_variable(...)` | Handled in `quote` match arm |
| `quote::quote_lambda(...)` | Handled in `quote` match arm |

**Key Difference:** New quotation doesn't need the type (NbE is untyped).

### Unification

| Old | New |
|-----|-----|
| `unify::unify(state, t1, t2, ty) -> Result<()>` | `unify::unify_val(state, depth, v1, v2) -> Result<()>` |
| `unify::unify_pi(...)` | `unify::unify_ty(Ty::Pi(...), Ty::Pi(...))` |
| `unify::solve_flex_rigid(...)` | `unify::solve_meta(...)` |

**Key Difference:** New unifier operates on `Ty` (no universe levels!), delegates to `unify_val` for codes.

### Elaboration

| Old | New |
|-----|-----|
| `elaborate::check(ctx, expr, ty) -> Syntax` | `elaborate::check(ctx, expr, ty) -> Syntax` |
| `elaborate::synth(ctx, expr) -> (Syntax, Value)` | `elaborate::synth(ctx, expr) -> (Syntax, Ty)` |
| N/A | `elaborate::elab_type(ctx, expr) -> Ty` |

**Key Difference:** New elaborator has `elab_type` for automatic `El` insertion.

## Data Structure Mappings

### Closures

| Old | New |
|-----|-----|
| `val::Closure { env, body }` | `value::Closure { env, body }` |
| `val::LocalEnv` (list of values) | `value::LocalEnv { values: Vec<RcValue> }` |

**Key Difference:** Same concept, cleaner implementation.

### Neutrals

| Old | New |
|-----|-----|
| `val::Rigid { head, spine }` | `value::Neutral { head: Head::Var(...), spine }` |
| `val::Flex { meta, spine }` | `value::Neutral { head: Head::Meta(...), spine }` |

**Key Difference:** Unified `Neutral` type instead of separate `Rigid`/`Flex`.

### Environments

| Old | New |
|-----|-----|
| `eval::Environment { global, local, transparent }` | `eval::eval(global, local, ...)` |
| `check::TCEnvironment { types, values }` | `elaborate::ElabContext { types, values, state }` |

**Key Difference:** Simpler environment structure.

## File Structure

### Old

```
crates/hwml-core/src/
  ├── syn/
  │   ├── syntax.rs      (Syntax enum, 744 lines)
  │   ├── declaration.rs (Type/data constructors)
  │   └── print.rs       (Pretty printing)
  ├── val/
  │   └── value.rs       (Value enum)
  ├── eval.rs            (Evaluation)
  ├── quote.rs           (Quotation)
  └── check.rs           (Type checking)

crates/hwml-elab/src/
  ├── unify.rs           (Unification, 2,500 lines)
  ├── elaborate.rs       (Elaboration, partial)
  └── engine.rs          (Solver state)
```

### New

```
crates/hwml-core/src/
  └── nbe/
      ├── mod.rs
      ├── syntax.rs      (Syntax enum, ~200 lines)
      ├── value.rs       (Value enum, ~150 lines)
      ├── ty.rs          (TySyntax, Ty enums, ~150 lines)
      ├── eval.rs        (Evaluation, ~300 lines)
      └── quote.rs       (Quotation, ~200 lines)

crates/hwml-elab/src/
  └── nbe/
      ├── mod.rs
      ├── unify.rs       (Unification, ~200 lines)
      └── elaborate.rs   (Elaboration, ~300 lines)
```

**Total:** ~1,500 lines (vs. ~3,500 lines in old architecture)

## Migration Checklist

- [ ] Create `crates/hwml-core/src/nbe/` directory
- [ ] Implement `syntax.rs` (Quadrant 1)
- [ ] Implement `value.rs` (Quadrant 2)
- [ ] Implement `ty.rs` (Quadrants 3 & 4)
- [ ] Implement `eval.rs`
- [ ] Implement `quote.rs`
- [ ] Create `crates/hwml-elab/src/nbe/` directory
- [ ] Implement `unify.rs`
- [ ] Implement `elaborate.rs`
- [ ] Update CLI to use new pipeline
- [ ] Migrate tests
- [ ] Delete old `syn/` and `val/` modules
- [ ] Update documentation

## Breaking Changes

1. **No more `Value::Universe`:** Universes are codes, not values
2. **No more `Syntax::Pi` as a type:** Use `TySyntax::Pi` or `Ty::Pi`
3. **Closures are mandatory:** Can't have `Value::Lambda` without a closure
4. **Levels in values:** Variables in `Value` use `Level`, not `Index`
5. **No type-directed quotation:** `quote` doesn't take a type argument

## Compatibility Layer (Optional)

If you want to keep the old API temporarily:

```rust
// Adapter functions
pub fn old_eval(env: &OldEnv, syntax: &OldSyntax) -> OldValue {
    let new_syntax = convert_syntax_old_to_new(syntax);
    let new_value = nbe::eval(env.global, &env.local, &new_syntax).unwrap();
    convert_value_new_to_old(&new_value)
}
```

**Recommendation:** Don't do this. Clean break is better.

