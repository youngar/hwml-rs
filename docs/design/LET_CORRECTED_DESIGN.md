# Let Expression - CORRECTED Design (Based on Feedback)

## Critical Corrections from Review

### ❌ FATAL FLAW 1: "No δ-reduction"

**Original Plan:** Never unfold Let bindings during conversion checking.

**Why This Breaks:**
```rust
let y = f x;
let h : Eq Nat (f x) y = refl;
```

When checking `refl`:
- Expected type: `Eq Nat (f x) y`
- Synthesized type: `Eq Nat (f x) (f x)`
- Conversion must prove: `y ≡ f x`
- Without δ-reduction: `y` (variable) ≠ `f x` (application) → **TYPE ERROR**

**CORRECTION:** **MUST implement δ-reduction.** When structural equality fails, unfold Let-bound variables.

---

### ❌ FATAL FLAW 2: `body: Closure<'db>` in Value::Let

**Original Plan:** Store body as unevaluated `Closure`.

**Why This Breaks:**
- In NbE, `Value` represents **fully evaluated** normal forms
- `Closure` is an **unevaluated thunk**
- Storing a closure violates the eval/quote separation
- Quotation would have to evaluate the closure, breaking architectural boundaries

**CORRECTION:** **Body must be `Rc<Value<'db>>`** - fully evaluated.

---

## CORRECTED Architecture: "Transparent Bindings"

### Core Insight

We can preserve Let structure WITHOUT gluing by using **transparent bindings**:

1. During evaluation: Push value to environment as **transparent binding**
2. When eval hits the variable: Return `Value::Rigid(var)` (preserves structure)
3. During conversion: Look up transparent bindings and unfold (enables δ-reduction)

### CORRECTED Data Structures

```rust
// Syntax (unchanged)
pub struct Let<'db> {
    pub name: String,
    pub type_ann: RcSyntax<'db>,
    pub expr: RcSyntax<'db>,
    pub body: RcSyntax<'db>,
}

// Value (CORRECTED)
pub struct Let<'db> {
    pub name: String,
    pub ty: Rc<Value<'db>>,
    pub value: Rc<Value<'db>>,
    pub body: Rc<Value<'db>>,  // ✅ FULLY EVALUATED (not Closure!)
}
```

### CORRECTED Evaluation

```rust
fn eval_let<'db, 'g>(
    env: &mut Environment<'db, 'g>,
    let_expr: &syn::Let<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    // 1. Evaluate type annotation
    let ty = eval(env, &let_expr.type_ann)?;
    
    // 2. Evaluate the bound expression
    let value = eval(env, &let_expr.expr)?;
    
    // 3. Push TRANSPARENT binding to environment
    //    This allows:
    //    - eval(Variable(0)) → Value::Rigid(var) (preserves structure)
    //    - conversion checking to unfold the variable (enables δ-reduction)
    env.push_transparent(let_expr.name.clone(), value.clone());
    
    // 4. Evaluate body (FULLY EVALUATE, not store as closure!)
    let body_val = eval(env, &let_expr.body)?;
    
    // 5. Pop binding
    env.pop();
    
    // 6. Return Let value with EVALUATED body
    Ok(Rc::new(Value::Let(val::Let {
        name: let_expr.name.clone(),
        ty,
        value,
        body: body_val,  // ✅ Fully evaluated!
    })))
}
```

**Key Point:** The body is evaluated in an environment where the variable is transparently bound, so:
- If the body references the variable, it evaluates to `Value::Rigid(var)` (structure preserved)
- If the body doesn't reference it, it evaluates normally
- Either way, we get a fully evaluated `Value`

### CORRECTED Quotation

```rust
fn quote_let<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    let_val: &val::Let<'db>,
    body_ty: &Value<'db>,  // Type of the entire Let expression
) -> Result<'db, RcSyntax<'db>> {
    // Quote type annotation
    let ty_syn = quote(global, depth, &let_val.ty, &Value::universe(...))?;
    
    // Quote bound value
    let val_syn = quote(global, depth, &let_val.value, &let_val.ty)?;
    
    // Quote body (already evaluated!)
    // Push a fresh variable to maintain de Bruijn indices
    let body_syn = quote(global, depth + 1, &let_val.body, body_ty)?;
    
    Ok(Rc::new(Syntax::Let(syn::Let {
        name: let_val.name.clone(),
        type_ann: ty_syn,
        expr: val_syn,
        body: body_syn,
    })))
}
```

**Key Point:** No need to run a closure - the body is already evaluated!

### CORRECTED Conversion Checking

```rust
pub fn equate_let<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    lhs: &val::Let<'db>,
    rhs: &val::Let<'db>,
    body_ty: &Value<'db>,
) -> Result<'db> {
    // 1. Compare types
    type_equiv(global, depth, &lhs.ty, &rhs.ty)?;
    
    // 2. Compare bound values
    equate(global, depth, &lhs.value, &rhs.value, &lhs.ty)?;
    
    // 3. Compare bodies (already evaluated!)
    //    Push transparent binding for conversion environment
    //    (This allows δ-reduction to work)
    equate(global, depth + 1, &lhs.body, &rhs.body, body_ty)?;
    
    Ok(())
}
```

### CRITICAL: δ-Reduction in Conversion

**Must add to `equal.rs`:**

```rust
pub fn equate<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    lhs: &Value<'db>,
    rhs: &Value<'db>,
    ty: &Value<'db>,
) -> Result<'db> {
    // Try structural equality first
    match (lhs, rhs) {
        // ... existing cases ...
        
        // NEW: δ-reduction fallback
        (Value::Rigid(rigid_lhs), _) => {
            // Check if this variable is transparently bound
            if let Some(unfolded) = global.lookup_transparent(rigid_lhs.head) {
                // Unfold and retry
                return equate(global, depth, &unfolded, rhs, ty);
            }
            // Otherwise, fall through to structural comparison
            equate_rigid_instances(global, depth, lhs, rhs, rigid)
        }
        
        (_, Value::Rigid(rigid_rhs)) => {
            // Symmetric case
            if let Some(unfolded) = global.lookup_transparent(rigid_rhs.head) {
                return equate(global, depth, lhs, &unfolded, ty);
            }
            equate_rigid_instances(global, depth, lhs, rhs, rigid)
        }
        
        _ => Err(Error::NotConvertible)
    }
}
```

**This is the key fix:** When comparing a variable against something else, check if it's Let-bound and unfold it.

## Environment Changes Needed

The `Environment` needs to track transparent bindings:

```rust
pub struct Environment<'db, 'g> {
    pub global: &'g GlobalEnv<'db>,
    pub local: LocalEnv<'db>,
    pub transparent: TransparentEnv<'db>,  // NEW: Track Let bindings
}

pub struct TransparentEnv<'db> {
    bindings: Vec<(Level, Rc<Value<'db>>)>,  // Map variables to their Let values
}

impl<'db, 'g> Environment<'db, 'g> {
    pub fn push_transparent(&mut self, name: String, value: Rc<Value<'db>>) {
        let level = Level::new(self.local.len());
        self.transparent.bindings.push((level, value));
        // Also push to local env so variables work normally
        self.local.push(Value::variable(level, /* type */));
    }
    
    pub fn lookup_transparent(&self, level: Level) -> Option<Rc<Value<'db>>> {
        self.transparent.bindings.iter()
            .find(|(l, _)| *l == level)
            .map(|(_, v)| v.clone())
    }
}
```

## Direct Answers to Open Questions

### Question 1: Body Type Tracking
**Answer:** Pass as parameter to `quote` (Option C). The type of the Let expression equals the body type.

### Question 2: δ-Reduction Strategy
**Answer:** **MUST implement immediately** (not "Phase 2 future"). Add fallback in `equate` that unfolds transparent bindings.

### Question 3: Environment Binding
**Answer:** **YES, must bind.** Push transparent binding during evaluation so:
- Variables preserve structure (eval returns `Value::Rigid`)
- Conversion can unfold them (δ-reduction works)

## Summary of Changes from Original Plan

| Aspect | Original Plan | Corrected Plan |
|--------|---------------|----------------|
| Value::Let body | `Closure<'db>` | `Rc<Value<'db>>` ✅ |
| Evaluation | Don't bind in env | Push transparent binding ✅ |
| δ-reduction | "Never (Phase 2)" | **MUST implement now** ✅ |
| Environment | No changes | Add `TransparentEnv` ✅ |

## Why This Works

1. **Preservation:** Body is evaluated with variable as `Rigid`, so structure preserved
2. **Transparency:** Conversion checker can unfold via transparent bindings
3. **NbE Compliance:** All Values are fully evaluated (no Closures)
4. **No Gluing:** Simpler than full glued evaluation, but mathematically sound

This is the **pragmatic middle-ground** that achieves all goals without full gluing complexity!

