# Let Expression Technical Design

## Problem Statement

We need to add `let` expressions to the Core IR that:
1. Preserve their structure through evaluation/quotation (for readability)
2. Support definitional equality (let x = e; x ≡ e)
3. Integrate cleanly with the existing NbE architecture

## The Core Challenge: Preservation vs. Transparency

The fundamental tension:
- **Preservation**: We want `quote(eval(let x = e; x))` to produce `let x = e; x`, not just `e`
- **Transparency**: We want `let x = succ zero; x` to be definitionally equal to `succ zero`

## Solution Approaches

### Approach 1: Eager Substitution (REJECTED)

**How it works:**
```rust
fn eval_let(env, let_expr) {
    let value = eval(env, let_expr.expr);
    env.push(value);
    let result = eval(env, let_expr.body);
    env.pop();
    result  // Returns body result directly
}
```

**Pros:**
- Simple implementation
- Natural definitional equality

**Cons:**
- ❌ Loses Let structure completely
- ❌ Cannot preserve for pretty printing
- ❌ Violates the preservation requirement

**Decision:** REJECTED - doesn't meet our goals.

---

### Approach 2: Glued Evaluation (FUTURE)

**How it works:**
```rust
enum Value {
    Glued {
        rigid: Rc<Neutral>,      // Syntax face: the variable
        semantic: Lazy<Rc<Value>>, // Semantic face: the unfolded value
    }
}

fn eval_let(env, let_expr) {
    let value = eval(env, let_expr.expr);
    let var_level = env.depth();
    
    // Create glued value: syntax face is variable, semantic face is value
    let glued = Value::Glued {
        rigid: Neutral::Var(var_level),
        semantic: Lazy::new(value),
    };
    
    env.push(glued);
    let result = eval(env, let_expr.body);
    env.pop();
    result
}

fn quote(value, ty) {
    match value {
        Value::Glued { rigid, .. } => quote_neutral(rigid),  // Use syntax face
        _ => ...
    }
}

fn is_def_eq(lhs, rhs, ty) {
    match (lhs, rhs) {
        (Value::Glued { rigid: r1, .. }, Value::Glued { rigid: r2, .. }) 
            if r1 == r2 => Ok(()),  // Fast path: same variable
        (Value::Glued { semantic, .. }, other) => {
            // Slow path: unfold and retry
            is_def_eq(semantic.force(), other, ty)
        }
        _ => ...
    }
}
```

**Pros:**
- ✅ Preserves structure perfectly
- ✅ Supports δ-reduction transparently
- ✅ Industry standard (Agda, Lean, Hazel)

**Cons:**
- Complex implementation
- Requires Lazy evaluation
- Affects entire Value representation

**Decision:** DEFERRED - implement simpler approach first, upgrade later if needed.

---

### Approach 3: Let as Value Constructor (CHOSEN)

**How it works:**
```rust
enum Value {
    Let {
        name: String,
        ty: Rc<Value>,
        value: Rc<Value>,
        body: Closure,
    }
}

fn eval_let(env, let_expr) {
    let ty = eval(env, let_expr.type_ann);
    let value = eval(env, let_expr.expr);
    let body = Closure::new(env.local.clone(), let_expr.body.clone());
    
    Value::Let { name, ty, value, body }  // Preserve structure
}

fn quote_let(let_val, depth) {
    let ty_syn = quote(let_val.ty, Value::universe(...));
    let value_syn = quote(let_val.value, let_val.ty);
    
    // Quote body by applying to fresh variable
    let var = Value::variable(depth, let_val.ty);
    let body_val = run_closure(let_val.body, [var]);
    let body_syn = quote(body_val, ...);  // Need body type!
    
    Syntax::Let { name, type_ann: ty_syn, expr: value_syn, body: body_syn }
}
```

**Pros:**
- ✅ Preserves Let structure
- ✅ Simpler than gluing
- ✅ Follows existing patterns (Pi, Lambda, etc.)
- ✅ Can add δ-reduction later

**Cons:**
- Need to track body type for quotation
- Conversion checking needs special handling
- Not as elegant as gluing

**Decision:** CHOSEN - best balance of simplicity and functionality.

---

## Key Design Decisions

### Decision 1: Body Type Tracking

**Problem:** When quoting the body, we need its type for type-directed quotation.

**Options:**

A. **Store body type in Let value**
```rust
struct Let {
    body_ty: Rc<Value>,  // Add this field
    body: Closure,
}
```
- Pro: Always available
- Con: Redundant (can be computed)

B. **Re-synthesize during quotation**
```rust
fn quote_let(let_val, depth) {
    // Synthesize body type on demand
    let var = Value::variable(depth, let_val.ty);
    let body_val = run_closure(let_val.body, [var]);
    let body_ty = synthesize_type(body_val);  // Need typechecker access!
    ...
}
```
- Pro: No redundancy
- Con: Requires typechecker in quotation (architectural violation)

C. **Pass body type from outside**
```rust
fn quote_let(let_val, let_ty, depth) {
    // let_ty is the type of the entire let expression (= body type)
    ...
}
```
- Pro: Clean separation
- Con: Caller must provide it

**CHOSEN:** Option C - pass body type as parameter to quote.

### Decision 2: Conversion Checking

**Problem:** How to compare Let bindings?

**Strategy:**
```rust
fn equate_let(lhs: Let, rhs: Let, ty: Value) {
    // 1. Compare types
    type_equiv(lhs.ty, rhs.ty)?;
    
    // 2. Compare bound values
    equate(lhs.value, rhs.value, lhs.ty)?;
    
    // 3. Compare bodies
    let var = fresh_variable(lhs.ty);
    let lhs_body = run_closure(lhs.body, [var]);
    let rhs_body = run_closure(rhs.body, [var]);
    equate(lhs_body, rhs_body, ty)?;  // ty is the body type
    
    Ok(())
}
```

**Note:** The type parameter `ty` is the type of the entire Let expression, which equals the body type.

### Decision 3: Environment Binding During Evaluation

**Question:** Should we bind the value in the environment when evaluating the body?

**Current Plan:** NO
- The body is stored as a Closure with the current environment
- The value is stored separately in the Let value
- When we need to run the body (e.g., in conversion), we extend the environment then

**Rationale:**
- Keeps evaluation pure (no side effects on environment)
- Preserves structure cleanly
- Follows the pattern used for Pi/Lambda

## Implementation Checklist

- [x] Define `syn::Let` struct
- [x] Add `Syntax::Let` variant
- [ ] Define `val::Let` struct  
- [ ] Add `Value::Let` variant
- [ ] Implement `eval_let`
- [ ] Implement `quote_let` (with body type parameter)
- [ ] Implement `check_let` (synth mode)
- [ ] Implement `equate_let`
- [ ] Implement `print_let`
- [ ] Implement `parse_let`
- [ ] Write tests

## Testing Strategy

1. **Roundtrip test**: `quote(eval(let x : T = e; body)) ≡ let x : T = e; body`
2. **Transparency test**: `let x : Nat = zero; x` ≡ `zero` (via conversion)
3. **Nested lets**: `let x = a; let y = b; f x y`
4. **Dependent types**: `let n : Nat = zero; Vec n`
5. **Type preservation**: Ensure typechecking is sound

## Future Work

1. **δ-reduction**: Add unfolding when comparing Let vs non-Let
2. **Glued evaluation**: Upgrade to full gluing if performance/elegance demands it
3. **Optimization**: Consider environment binding for performance
4. **Surface syntax**: Add let to the surface language elaborator

