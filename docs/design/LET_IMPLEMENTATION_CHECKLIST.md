# Let Expression Implementation Checklist (CORRECTED)

## Phase 0: Environment Infrastructure (NEW - REQUIRED)

### Add Transparent Binding Support

**File:** `crates/hwml-core/src/val.rs`

- [ ] Add `TransparentEnv` struct to track Let bindings
  ```rust
  pub struct TransparentEnv<'db> {
      bindings: Vec<(Level, Rc<Value<'db>>)>,
  }
  ```

- [ ] Update `Environment` to include transparent bindings
  ```rust
  pub struct Environment<'db, 'g> {
      pub global: &'g GlobalEnv<'db>,
      pub local: LocalEnv<'db>,
      pub transparent: TransparentEnv<'db>,  // NEW
  }
  ```

- [ ] Add methods:
  - [ ] `push_transparent(name, value)` - Add Let binding
  - [ ] `lookup_transparent(level)` - Get Let value for variable
  - [ ] Update `pop()` to also pop transparent bindings

**Why:** This is the foundation for transparent bindings that enable both structure preservation and δ-reduction.

---

## Phase 1: Core Data Structures

### 1.1 Syntax

**File:** `crates/hwml-core/src/syn/basic.rs`

- [ ] Define `Let` struct:
  ```rust
  pub struct Let<'db> {
      pub name: String,
      pub type_ann: RcSyntax<'db>,
      pub expr: RcSyntax<'db>,
      pub body: RcSyntax<'db>,
  }
  ```

- [ ] Add `Let(Let<'db>)` variant to `Syntax` enum

- [ ] Add constructor methods:
  - [ ] `Syntax::let_expr(name, type_ann, expr, body)`
  - [ ] `Syntax::let_expr_rc(...)`

### 1.2 Value

**File:** `crates/hwml-core/src/val.rs`

- [ ] Define `Let` struct:
  ```rust
  pub struct Let<'db> {
      pub name: String,
      pub ty: Rc<Value<'db>>,
      pub value: Rc<Value<'db>>,
      pub body: Rc<Value<'db>>,  // ✅ FULLY EVALUATED (not Closure!)
  }
  ```

- [ ] Add `Let(Let<'db>)` variant to `Value` enum

- [ ] Add constructor method:
  - [ ] `Value::let_expr(name, ty, value, body)`

---

## Phase 2: Evaluation (CORRECTED)

**File:** `crates/hwml-core/src/eval.rs`

- [ ] Implement `eval_let`:
  ```rust
  fn eval_let<'db, 'g>(
      env: &mut Environment<'db, 'g>,
      let_expr: &syn::Let<'db>,
  ) -> Result<Rc<Value<'db>>, Error> {
      let ty = eval(env, &let_expr.type_ann)?;
      let value = eval(env, &let_expr.expr)?;
      
      // ✅ CRITICAL: Push transparent binding
      env.push_transparent(let_expr.name.clone(), value.clone());
      
      // ✅ CRITICAL: Fully evaluate body (not store as closure!)
      let body_val = eval(env, &let_expr.body)?;
      
      env.pop();
      
      Ok(Rc::new(Value::Let(val::Let {
          name: let_expr.name.clone(),
          ty,
          value,
          body: body_val,  // ✅ Evaluated!
      })))
  }
  ```

- [ ] Add `Syntax::Let(let_expr) => eval_let(env, let_expr)` to main `eval` match

**Test:** Verify that `eval(let x : Nat = zero; x)` produces `Value::Let` with evaluated body.

---

## Phase 3: Quotation (CORRECTED)

**File:** `crates/hwml-core/src/quote.rs`

- [ ] Implement `quote_let`:
  ```rust
  fn quote_let<'db>(
      global: &GlobalEnv<'db>,
      depth: usize,
      let_val: &val::Let<'db>,
      body_ty: &Value<'db>,
  ) -> Result<'db, RcSyntax<'db>> {
      let ty_syn = quote(global, depth, &let_val.ty, &Value::universe(...))?;
      let val_syn = quote(global, depth, &let_val.value, &let_val.ty)?;
      
      // ✅ Body is already evaluated - just quote it!
      let body_syn = quote(global, depth + 1, &let_val.body, body_ty)?;
      
      Ok(Rc::new(Syntax::Let(syn::Let {
          name: let_val.name.clone(),
          type_ann: ty_syn,
          expr: val_syn,
          body: body_syn,
      })))
  }
  ```

- [ ] Add case to main `quote` function (dispatch based on type)
  - Note: Let values don't have a specific "type" - they appear when quoting at any type
  - May need to add special handling in quote dispatch

**Test:** Verify that `quote(eval(let x : Nat = zero; x))` preserves Let structure.

---

## Phase 4: Conversion Checking (CRITICAL - CORRECTED)

**File:** `crates/hwml-core/src/equal.rs`

### 4.1 Add Let Comparison

- [ ] Implement `equate_let`:
  ```rust
  pub fn equate_let<'db>(
      global: &GlobalEnv<'db>,
      depth: usize,
      lhs: &val::Let<'db>,
      rhs: &val::Let<'db>,
      body_ty: &Value<'db>,
  ) -> Result<'db> {
      type_equiv(global, depth, &lhs.ty, &rhs.ty)?;
      equate(global, depth, &lhs.value, &rhs.value, &lhs.ty)?;
      equate(global, depth + 1, &lhs.body, &rhs.body, body_ty)?;
      Ok(())
  }
  ```

### 4.2 Add δ-Reduction (CRITICAL!)

- [ ] **MUST IMPLEMENT:** Add δ-reduction fallback to `equate`:
  ```rust
  pub fn equate<'db>(...) -> Result<'db> {
      match (lhs, rhs) {
          // ... existing cases ...
          
          // ✅ CRITICAL: δ-reduction for Let-bound variables
          (Value::Rigid(rigid_lhs), _) => {
              if let Some(unfolded) = env.lookup_transparent(rigid_lhs.head) {
                  return equate(global, depth, &unfolded, rhs, ty);
              }
              equate_rigid_instances(global, depth, lhs, rhs, rigid_lhs)
          }
          
          (_, Value::Rigid(rigid_rhs)) => {
              if let Some(unfolded) = env.lookup_transparent(rigid_rhs.head) {
                  return equate(global, depth, lhs, &unfolded, ty);
              }
              equate_rigid_instances(global, depth, lhs, rhs, rigid_rhs)
          }
          
          _ => Err(Error::NotConvertible)
      }
  }
  ```

**Test:** Verify that `let y = f x; refl : Eq Nat (f x) y` typechecks correctly.

---

## Phase 5: Typechecking

**File:** `crates/hwml-core/src/check.rs`

- [ ] Implement `synth_let`:
  ```rust
  fn synth_let<'db>(
      ctx: &mut Context<'db>,
      let_expr: &syn::Let<'db>,
  ) -> Result<Rc<Value<'db>>, Error> {
      // Check type annotation is a type
      check(ctx, &let_expr.type_ann, &Value::universe(...))?;
      let ty = eval(ctx.env, &let_expr.type_ann)?;
      
      // Check expression has that type
      check(ctx, &let_expr.expr, &ty)?;
      
      // Synthesize body type in extended context
      let value = eval(ctx.env, &let_expr.expr)?;
      ctx.push_transparent(let_expr.name.clone(), ty.clone(), value);
      let body_ty = synth(ctx, &let_expr.body)?;
      ctx.pop();
      
      Ok(body_ty)  // Type of Let = type of body
  }
  ```

- [ ] Add `Syntax::Let(let_expr) => synth_let(ctx, let_expr)` to synth dispatch

**Test:** Verify that `let x : Nat = zero; succ x` synthesizes type `Nat`.

---

## Phase 6: Printing

**File:** `crates/hwml-core/src/syn/print.rs`

- [ ] Implement `print_let` for `Syntax::Let`
  - Format: `let %name : type = expr; body`

- [ ] Handle precedence and parenthesization

**Test:** Verify pretty printing produces readable output.

---

## Phase 7: Parsing

**File:** `crates/hwml-core/src/syn/parse.rs`

- [ ] Add `let` keyword
- [ ] Implement parser for: `"let" identifier ":" expr "=" expr ";" expr`
- [ ] Handle de Bruijn index for body

**Test:** Verify round-trip: `parse(print(let_expr)) == let_expr`

---

## Phase 8: Testing

- [ ] **Roundtrip test:** `quote(eval(let x : T = e; body)) ≡ let x : T = e; body`
- [ ] **Transparency test:** `let x : Nat = zero; x` ≡ `zero` (via δ-reduction)
- [ ] **Dependent proof test:** `let y = f x; refl : Eq Nat (f x) y` typechecks
- [ ] **Nested lets:** `let x = a; let y = b; f x y`
- [ ] **Type preservation:** Ensure all tests pass

---

## Critical Success Criteria

✅ **MUST WORK:** `let y = f x; refl : Eq Nat (f x) y` typechecks
✅ **MUST PRESERVE:** `quote(eval(let ...))` preserves Let structure
✅ **MUST BE SOUND:** All existing tests still pass

## What Changed from Original Plan

| Original | Corrected | Why |
|----------|-----------|-----|
| `body: Closure` | `body: Rc<Value>` | NbE requires fully evaluated Values |
| No environment binding | Push transparent binding | Enables both preservation and δ-reduction |
| δ-reduction "Phase 2" | **MUST implement now** | Required for dependent proofs to work |
| No TransparentEnv | Add TransparentEnv | Infrastructure for transparent bindings |

