# Let Expression Data Flow

This document shows how Let expressions flow through the hwml-rust compiler pipeline.

## Pipeline Overview

```
Surface Syntax (future)
        ↓
    [Parser]
        ↓
Core Syntax (Syntax::Let)
        ↓
   [Typechecker]
        ↓
Core Syntax (type-checked)
        ↓
   [Evaluator]
        ↓
Semantic Value (Value::Let)
        ↓
   [Quotation]
        ↓
Core Syntax (normalized)
        ↓
    [Printer]
        ↓
   Output Text
```

## Detailed Data Flow

### 1. Parsing (Future)

**Input:** `let x : Nat = zero; succ x`

**Output:**
```rust
Syntax::Let(Let {
    name: "x",
    type_ann: Syntax::Constant("Nat"),
    expr: Syntax::Constant("zero"),
    body: Syntax::Application(
        Syntax::Constant("succ"),
        Syntax::Variable(0)  // de Bruijn index
    )
})
```

### 2. Typechecking

**Input:** `Syntax::Let` (from parser)

**Process:**
1. Check `type_ann` is a type: `Nat : U0` ✓
2. Evaluate `type_ann`: `Nat` → `Value::TypeConstructor(Nat, [])`
3. Check `expr` has type `Nat`: `zero : Nat` ✓
4. Extend context: `Γ, x : Nat`
5. Synthesize body type: `succ x : Nat`
6. Return: `Nat`

**Output:** Type-checked `Syntax::Let` + type `Nat`

### 3. Evaluation

**Input:** `Syntax::Let` (type-checked)

**Process:**
```rust
eval_let(env, let_expr) {
    // Evaluate type annotation
    ty = eval(env, Syntax::Constant("Nat"))
       = Value::TypeConstructor(Nat, [])
    
    // Evaluate bound expression
    value = eval(env, Syntax::Constant("zero"))
          = Value::DataConstructor(zero, [])
    
    // Create closure for body
    body = Closure {
        env: env.local,
        term: Syntax::Application(succ, Variable(0))
    }
    
    // Return Let value (PRESERVE STRUCTURE)
    return Value::Let {
        name: "x",
        ty: Value::TypeConstructor(Nat, []),
        value: Value::DataConstructor(zero, []),
        body: Closure { ... }
    }
}
```

**Output:**
```rust
Value::Let(Let {
    name: "x",
    ty: TypeConstructor(Nat, []),
    value: DataConstructor(zero, []),
    body: Closure { env, term }
})
```

**Key Point:** We do NOT substitute! The Let structure is preserved.

### 4. Quotation (Readback)

**Input:** `Value::Let` + body type `Nat`

**Process:**
```rust
quote_let(let_val, body_ty, depth) {
    // Quote type annotation
    ty_syn = quote(TypeConstructor(Nat, []), Universe, depth)
           = Syntax::Constant("Nat")
    
    // Quote bound value
    val_syn = quote(DataConstructor(zero, []), TypeConstructor(Nat, []), depth)
            = Syntax::Constant("zero")
    
    // Quote body: apply closure to fresh variable
    var = Value::Rigid(Variable(depth), [], TypeConstructor(Nat, []))
    body_val = run_closure(let_val.body, [var])
             = Value::DataConstructor(succ, [var])
    
    body_syn = quote(body_val, Nat, depth + 1)
             = Syntax::Application(
                   Syntax::Constant("succ"),
                   Syntax::Variable(0)
               )
    
    // Reconstruct Let syntax
    return Syntax::Let {
        name: "x",
        type_ann: ty_syn,
        expr: val_syn,
        body: body_syn
    }
}
```

**Output:**
```rust
Syntax::Let(Let {
    name: "x",
    type_ann: Constant("Nat"),
    expr: Constant("zero"),
    body: Application(Constant("succ"), Variable(0))
})
```

**Key Point:** The Let structure is perfectly preserved!

### 5. Conversion Checking

**Scenario:** Check if `let x : Nat = zero; x` ≡ `let y : Nat = zero; y`

**Process:**
```rust
equate_let(lhs, rhs, ty) {
    // Both are Value::Let
    
    // 1. Compare types
    type_equiv(TypeConstructor(Nat, []), TypeConstructor(Nat, []))
    // ✓ Equal
    
    // 2. Compare bound values
    equate(DataConstructor(zero, []), DataConstructor(zero, []), Nat)
    // ✓ Equal
    
    // 3. Compare bodies
    var = fresh_variable(depth, Nat)
    lhs_body = run_closure(lhs.body, [var])
             = var  // Variable(depth)
    rhs_body = run_closure(rhs.body, [var])
             = var  // Variable(depth)
    
    equate(var, var, Nat)
    // ✓ Equal
    
    return Ok(())
}
```

**Result:** The two Let expressions are definitionally equal.

## Comparison with Eager Substitution

### With Eager Substitution (REJECTED)

```
Syntax::Let("x", Nat, zero, succ x)
        ↓ eval
Value::DataConstructor(succ, [zero])  ← Let structure LOST!
        ↓ quote
Syntax::Application(succ, zero)       ← Cannot recover Let!
```

### With Let Preservation (CHOSEN)

```
Syntax::Let("x", Nat, zero, succ x)
        ↓ eval
Value::Let("x", Nat, zero, Closure)   ← Let structure PRESERVED!
        ↓ quote
Syntax::Let("x", Nat, zero, succ x)   ← Perfect roundtrip!
```

## Key Invariants

1. **Roundtrip Preservation:**
   ```
   quote(eval(let x : T = e; body)) ≡ let x : T = e; body
   ```

2. **Type Preservation:**
   ```
   If Γ ⊢ let x : T = e; body : A
   Then eval(let x : T = e; body) : A
   ```

3. **Definitional Equality:**
   ```
   let x : T = e; x  ≡  e  (via conversion checking)
   ```

## Memory Layout

### Syntax::Let
```
┌─────────────────────────────┐
│ Let                         │
├─────────────────────────────┤
│ name: String                │ ← "x"
│ type_ann: RcSyntax          │ ─→ Syntax::Constant("Nat")
│ expr: RcSyntax              │ ─→ Syntax::Constant("zero")
│ body: RcSyntax              │ ─→ Syntax::Application(...)
└─────────────────────────────┘
```

### Value::Let
```
┌─────────────────────────────┐
│ Let                         │
├─────────────────────────────┤
│ name: String                │ ← "x"
│ ty: Rc<Value>               │ ─→ Value::TypeConstructor(Nat, [])
│ value: Rc<Value>            │ ─→ Value::DataConstructor(zero, [])
│ body: Closure               │ ─→ Closure { env, term }
└─────────────────────────────┘
                                    ↓
                            ┌───────────────────┐
                            │ Closure           │
                            ├───────────────────┤
                            │ env: LocalEnv     │
                            │ term: RcSyntax    │
                            └───────────────────┘
```

## Performance Considerations

**Memory:** Let values are slightly larger than substituted values (store closure + value)

**Speed:** 
- Evaluation: Same (no substitution work)
- Quotation: Slightly slower (need to run closure)
- Conversion: Same (structural comparison)

**Trade-off:** Small performance cost for much better structure preservation and readability.

## Future: δ-Reduction

When we add δ-reduction, conversion checking will unfold Let bindings:

```rust
equate(lhs, rhs, ty) {
    match (lhs, rhs) {
        (Value::Let(let_val), other) => {
            // Unfold: run the body with the bound value
            let result = run_closure(let_val.body, [let_val.value]);
            equate(result, other, ty)  // Retry with unfolded value
        }
        _ => ...
    }
}
```

This enables: `let x = zero; x` ≡ `zero` (comparing Let vs non-Let)

