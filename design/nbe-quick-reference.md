# NbE Quick Reference Guide

## The 4 Quadrants at a Glance

```
                    TERMS (Computing)          TYPES (Classifying)
                    ─────────────────          ───────────────────
SYNTACTIC (AST)  │  Syntax<'db>            │  TySyntax<'db>
                 │  - UniverseCode(n)      │  - UniverseType
                 │  - PiCode(A, B)         │  - Pi(A, B)
                 │  - Lam(body)            │  - El(code)
                 │  - Var(idx)             │  - HArrow(A, B)
                 │                         │
SEMANTIC (Value) │  Value<'db>             │  Ty<'db>
                 │  - UniverseCode(n)      │  - UniverseType
                 │  - PiCode(A, clos)      │  - Pi(A, clos)
                 │  - Lam(clos)            │  - El(value)
                 │  - Neutral(head, spine) │  - HArrow(A, B)
```

## The 3 Core Operations

### 1. Evaluation: `Syntax → Value`, `TySyntax → Ty`

```rust
eval(global, env, Syntax::Lam(body))
  → Value::Lam(Closure { env, body })

eval_ty(global, env, TySyntax::Pi(A, B))
  → Ty::Pi(eval_ty(A), TyClosure { env, B })
```

**Key Rule:** Variables are looked up in the environment by **Level**, not Index.

### 2. Quotation: `Value → Syntax`, `Ty → TySyntax`

```rust
quote(global, depth, Value::Lam(closure))
  → Syntax::Lam(quote(depth+1, closure.apply(fresh_var)))

quote_ty(global, depth, Ty::El(code))
  → TySyntax::El(quote(depth, code))
```

**Key Rule:** To quote a closure, apply it to a fresh variable at the current depth.

### 3. Unification: `Ty × Ty → Result`, `Value × Value → Result`

```rust
unify_ty(Ty::Pi(A1, B1), Ty::Pi(A2, B2))
  → unify_ty(A1, A2) && unify_ty(B1(x), B2(x))

unify_ty(Ty::El(v1), Ty::El(v2))
  → unify_val(v1, v2)  // Drop to value unification

unify_val(Value::Neutral(meta), value)
  → solve_meta(meta, value)  // Pattern unification!
```

**Key Rule:** `El` absorbs `Lift` (Sterling's commuting rule).

## The Tarski Bridge: `El`

The `El` operator decodes type codes into semantic types:

```rust
// User writes: Nat : Type
// Elaborates to:

// The code (what Nat *is*):
Syntax::TypeConstructorCode("Nat", [])

// The type (what Nat *classifies*):
Ty::El(Value::TypeConstructorCode("Nat", []))

// The type of Nat (the classifier):
Ty::UniverseType
```

**Automatic Insertion:** The elaborator inserts `El` automatically:

```rust
// User writes: (x : Nat) -> Nat
// Elaborates to:

TySyntax::Pi(
  TySyntax::El(Syntax::TypeConstructorCode("Nat", [])),
  TyBinder {
    body: TySyntax::El(Syntax::TypeConstructorCode("Nat", []))
  }
)
```

## Pattern Unification: The Firewall

When solving `?M x y = rhs`, we check:

1. **Inversion:** The spine `[x, y]` must be distinct bound variables
2. **Occurs:** `?M` must not occur in `rhs` (prevents `?M = ?M -> Nat`)
3. **Scope:** `rhs` must only reference variables in the spine (prevents escapes)

If all checks pass, assign `?M := λx. λy. rhs`.

## De Bruijn Indices vs. Levels

- **Index:** Counts from the *end* (most recent binder = 0)
- **Level:** Counts from the *beginning* (first binder = 0)

```
Context:
  Level 0: x : Nat     (Index 2 when depth=3)
  Level 1: y : Nat     (Index 1 when depth=3)
  Level 2: z : Nat     (Index 0 when depth=3)
```

**Conversion:**
```rust
level.to_index(depth) = Index(depth - level - 1)
index.to_level(depth) = Level(depth - index - 1)
```

**Rule:** Use **Levels** in `Value` (they're stable under extension), **Indices** in `Syntax`.

## Closures

A closure captures an environment and a term with one free variable:

```rust
struct Closure<'db> {
  env: LocalEnv<'db>,      // Values for free variables
  body: RcSyntax<'db>,     // Term with one additional free var (Index 0)
}

impl Closure<'db> {
  fn apply(&self, arg: RcValue<'db>) -> RcValue<'db> {
    let mut extended_env = self.env.clone();
    extended_env.push(arg);
    eval(global, &extended_env, &self.body)
  }
}
```

**Type Closures** are similar but produce types:

```rust
struct TyClosure<'db> {
  env: LocalEnv<'db>,
  body: RcTySyntax<'db>,
}
```

## Neutrals and Spines

A **neutral** is a stuck term: a variable or metavariable applied to arguments.

```rust
struct Neutral<'db> {
  head: Head<'db>,        // Var(level) | Const(name) | Meta(id, subst)
  spine: Vec<Elim<'db>>,  // [App(arg1), App(arg2), ...]
}
```

**Example:** `f x y` where `f` is a variable:

```rust
Value::Neutral(Neutral {
  head: Head::Var(Level(0)),  // f
  spine: vec![
    Elim::App(Value::Neutral(...)),  // x
    Elim::App(Value::Neutral(...)),  // y
  ]
})
```

## Elaboration: Check vs. Synth

### Check Mode: Push types down

```rust
check(ctx, expr, expected_ty) -> RcSyntax<'db>

// Example: fun x => x
check(ctx, Fun { expr: Id("x") }, Ty::Pi(A, B))
  → Syntax::Lam(check(ctx', Id("x"), B))
```

### Synth Mode: Infer types up

```rust
synth(ctx, expr) -> (RcSyntax<'db>, RcTy<'db>)

// Example: f x
synth(ctx, App([f, x]))
  → let (f_syn, Ty::Pi(A, B)) = synth(ctx, f)
    let x_syn = check(ctx, x, A)
    (Syntax::App(f_syn, x_syn), B.apply(eval(x_syn)))
```

### Elab Type: Automatic El insertion

```rust
elab_type(ctx, expr) -> RcTy<'db>

// Example: Nat
elab_type(ctx, Id("Nat"))
  → let (code, Ty::UniverseType) = synth(ctx, Id("Nat"))
    Ty::El(eval(code))
```

## Common Patterns

### Pattern 1: Going under a binder

```rust
// In the elaborator:
let var_level = Level::new(ctx.depth());
let var_val = Value::var(var_level);
ctx.push_var(ty, var_val);
let body = elaborate_body(ctx, ...);
ctx.pop_var();
```

### Pattern 2: Quoting a closure

```rust
// To quote Value::Lam(closure):
let fresh_var = Value::var(Level::new(depth));
let body_val = closure.apply(global, fresh_var);
let body_syn = quote(global, depth + 1, body_val);
Syntax::Lam(Binder { body: body_syn })
```

### Pattern 3: Unifying Pi types

```rust
// To unify Ty::Pi(A1, B1) with Ty::Pi(A2, B2):
unify_ty(state, depth, A1, A2).await?;
let var = Value::var(Level::new(depth));
let B1_ty = B1.apply(global, var.clone())?;
let B2_ty = B2.apply(global, var)?;
unify_ty(state, depth + 1, B1_ty, B2_ty).await
```

## File Organization

```
crates/hwml-core/src/nbe/
  ├── mod.rs           # Module exports
  ├── syntax.rs        # Quadrant 1: Syntax<'db>
  ├── value.rs         # Quadrant 2: Value<'db>, Closure, Neutral
  ├── ty.rs            # Quadrants 3 & 4: TySyntax<'db>, Ty<'db>
  ├── eval.rs          # eval, eval_ty, apply
  └── quote.rs         # quote, quote_ty

crates/hwml-elab/src/nbe/
  ├── mod.rs           # Module exports
  ├── unify.rs         # unify_ty, unify_val, solve_meta
  └── elaborate.rs     # check, synth, elab_type
```

