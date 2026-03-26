# Legacy NbE → Type Code Architecture Migration Plan

## Executive Summary

**Goal**: Migrate the legacy NbE implementation (`crates/hwml-core/src/{eval.rs, quote.rs, syn/syntax.rs, val.rs}`) to use the **type code architecture** from `crates/hwml-core/src/nbe/`, enabling **subsumption** and **cumulativity** for universe levels.

**Status**: Fresh start migration - we're not continuing previous work.

---

## 1. Architectural Transformation

### Current Legacy Architecture

```rust
// Syntax: Types are constructors
enum Syntax<'db> {
    Universe(Universe<'db>),  // Type constructor
    Pi(Pi<'db>),              // Type constructor
    Lambda(Lambda<'db>),      // Term
    Application(Application<'db>), // Term
    // ...
}

// Value: Types are values
enum Value<'db> {
    Universe(Universe<'db>),  // Type value
    Pi(Pi<'db>),              // Type value
    Lambda(Lambda<'db>),      // Term value
    // ...
}
```

### Target Type Code Architecture

```rust
// Syntax: Type CODES are terms
enum Syntax<'db> {
    // ========== Type Codes (these are TERMS!) ==========
    UniverseCode(usize),      // Type 0, Type 1, ...
    PiCode(RcSyntax, Binder), // Pi type code
    BitCode,                  // Bit type code
    
    // ========== Terms ==========
    Lam(Binder),
    App(RcSyntax, RcSyntax),
    // ...
}

// Value: Evaluated type codes
enum Value<'db> {
    // ========== Evaluated Type Codes ==========
    UniverseCode(usize),
    PiCode(RcValue, Closure),
    BitCode,
    
    // ========== Terms ==========
    Lam(Closure),
    Neutral(Neutral),
    // ...
}

// NEW: Semantic Types (separate from terms!)
enum Ty<'db> {
    UniverseType,             // The type OF universes
    Pi(RcTy, TyClosure),      // Top-level Pi (no levels!)
    El(RcValue),              // Decode a type code
}
```

---

## 2. Key Conceptual Changes

### Change 1: Types Become Terms

**Before**: `Syntax::Universe(level)` is a **type**  
**After**: `Syntax::UniverseCode(level)` is a **term** (a type code)

**Before**: `Value::Pi(source, target)` is a **type value**  
**After**: `Value::PiCode(source, target)` is an **evaluated type code** (still a term!)

### Change 2: The Tarski Bridge

**New concept**: `Ty::El(code)` decodes a type code into a semantic type.

```rust
// Example: The type of (λx. x) : Nat → Nat
let nat_code = Syntax::TypeCon(DefId(NAT), vec![]);
let nat_type = Ty::El(eval(nat_code)); // Decode Nat code to type

let pi_code = Syntax::PiCode(nat_code.clone(), Binder::new(nat_code));
let pi_type = Ty::El(eval(pi_code)); // Decode Pi code to type
```

### Change 3: Cumulativity Lives in Subtyping

**New**: Subsumption rule in the typechecker:

```rust
// If Γ ⊢ e : A and A <: B, then Γ ⊢ e : B
fn check_subsumption(term: &Syntax, ty_a: &Ty, ty_b: &Ty) -> Result<()> {
    if is_subtype(ty_a, ty_b) {
        Ok(())
    } else {
        Err(TypeError::NotASubtype)
    }
}

// Cumulativity: Type i <: Type j when i ≤ j
fn is_subtype(a: &Ty, b: &Ty) -> bool {
    match (a, b) {
        (Ty::El(Value::UniverseCode(i)), Ty::El(Value::UniverseCode(j))) => i <= j,
        (Ty::Pi(a1, b1), Ty::Pi(a2, b2)) => {
            // Contravariant in domain, covariant in codomain
            is_subtype(a2, a1) && is_subtype(b1, b2)
        }
        _ => a == b, // Structural equality otherwise
    }
}
```

---

## 3. Migration Steps

### Phase 1: Add Type Code Variants (Non-Breaking)

**Files**: `crates/hwml-core/src/syn/syntax.rs`, `crates/hwml-core/src/val.rs`

**Action**: Add new variants alongside existing ones:

```rust
// In Syntax enum
pub enum Syntax<'db> {
    // OLD (keep for now)
    Universe(Universe<'db>),
    Pi(Pi<'db>),
    
    // NEW (add these)
    UniverseCode(usize),
    PiCode(RcSyntax<'db>, BindingSyntax<'db>),
    BitCode,
    
    // ... rest unchanged
}

// In Value enum
pub enum Value<'db> {
    // OLD (keep for now)
    Universe(Universe<'db>),
    Pi(Pi<'db>),
    
    // NEW (add these)
    UniverseCode(usize),
    PiCode(RcValue<'db>, Closure<'db>),
    BitCode,
    
    // ... rest unchanged
}
```

### Phase 2: Create Ty Module

**File**: `crates/hwml-core/src/ty.rs` (new file)

**Action**: Create the semantic type system:

```rust
pub enum Ty<'db> {
    UniverseType,
    Pi(RcTy<'db>, TyClosure<'db>),
    El(RcValue<'db>),
    // Hardware types
    SignalUniverseType,
    SignalEl(RcValue<'db>),
    ModuleUniverseType,
    ModuleEl(RcValue<'db>),
}

pub struct TyClosure<'db> {
    pub local: LocalEnv<'db>,
    pub body: RcTy<'db>,
}
```

### Phase 3: Update Eval for Type Codes

**File**: `crates/hwml-core/src/eval.rs`

**Action**: Add evaluation cases for type codes:

```rust
pub fn eval<'db>(env: &mut Environment<'db>, stx: &Syntax<'db>) -> Result<RcValue<'db>> {
    match stx {
        // NEW: Evaluate type codes
        Syntax::UniverseCode(level) => Ok(Rc::new(Value::UniverseCode(*level))),
        Syntax::PiCode(source, target) => {
            let source_val = eval(env, source)?;
            let closure = Closure::new(env.local.clone(), target.0.clone());
            Ok(Rc::new(Value::PiCode(source_val, closure)))
        }
        Syntax::BitCode => Ok(Rc::new(Value::BitCode)),

        // OLD: Keep existing cases for backward compat
        Syntax::Universe(uni) => eval_universe(env, uni),
        Syntax::Pi(pi) => eval_pi(env, pi),
        // ...
    }
}
```

### Phase 4: Update Quote for Type Codes

**File**: `crates/hwml-core/src/quote.rs`

**Action**: Add quotation cases (type-free!):

```rust
pub fn quote_value<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    value: &Value<'db>,
) -> Result<RcSyntax<'db>> {
    match value {
        // NEW: Quote type codes (no type needed!)
        Value::UniverseCode(level) => Ok(Rc::new(Syntax::UniverseCode(*level))),
        Value::PiCode(source, target) => {
            let source_syn = quote_value(global, depth, source)?;
            let fresh_var = Value::variable_rc(Level::new(depth), /* dummy type */);
            let target_val = run_closure(global, target, [fresh_var])?;
            let target_syn = quote_value(global, depth + 1, &target_val)?;
            Ok(Rc::new(Syntax::PiCode(source_syn, Binding(target_syn))))
        }
        Value::BitCode => Ok(Rc::new(Syntax::BitCode)),

        // OLD: Keep type-directed quotation for backward compat
        _ => quote(global, depth, value, /* infer type */)
    }
}
```

### Phase 5: Implement Subsumption

**File**: `crates/hwml-core/src/check.rs`

**Action**: Add subtyping and subsumption:

```rust
/// Check if A is a subtype of B
pub fn is_subtype<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    a: &Ty<'db>,
    b: &Ty<'db>,
) -> bool {
    match (a, b) {
        // Cumulativity: Type i <: Type j when i ≤ j
        (Ty::El(val_a), Ty::El(val_b)) => {
            match (&**val_a, &**val_b) {
                (Value::UniverseCode(i), Value::UniverseCode(j)) => i <= j,
                _ => false,
            }
        }

        // Pi types: contravariant in domain, covariant in codomain
        (Ty::Pi(a1, b1), Ty::Pi(a2, b2)) => {
            is_subtype(global, depth, a2, a1) && {
                let fresh = Value::var(Level::new(depth));
                let b1_applied = b1.apply(global, fresh.clone()).unwrap();
                let b2_applied = b2.apply(global, fresh).unwrap();
                is_subtype(global, depth + 1, &b1_applied, &b2_applied)
            }
        }

        // Structural equality otherwise
        _ => a == b,
    }
}

/// Apply subsumption: if term has type A and we expect B, check A <: B
pub fn check_with_subsumption<'db>(
    env: &mut Environment<'db>,
    term: &Syntax<'db>,
    expected: &Ty<'db>,
) -> Result<()> {
    let inferred = infer_type(env, term)?;
    if is_subtype(env.global, env.local.depth(), &inferred, expected) {
        Ok(())
    } else {
        Err(Error::NotASubtype {
            inferred,
            expected: expected.clone(),
        })
    }
}
```

### Phase 6: Gradual Migration

**Strategy**: Dual-mode operation during transition

1. **Add feature flag**: `use_type_codes: bool` in `GlobalEnv`
2. **Parallel paths**: Both old and new code paths coexist
3. **Incremental testing**: Migrate one feature at a time
4. **Remove old code**: Once all tests pass with type codes

---

## 4. Files to Modify

### Core Files (Required)

1. **`crates/hwml-core/src/syn/syntax.rs`** (~50 lines)
   - Add `UniverseCode`, `PiCode`, `BitCode` variants
   - Add helper constructors

2. **`crates/hwml-core/src/val.rs`** (~50 lines)
   - Add `UniverseCode`, `PiCode`, `BitCode` variants
   - Add helper constructors

3. **`crates/hwml-core/src/ty.rs`** (~200 lines, NEW FILE)
   - Define `Ty` enum
   - Define `TyClosure`
   - Implement `eval_ty` and `quote_ty`

4. **`crates/hwml-core/src/eval.rs`** (~100 lines)
   - Add evaluation for type codes
   - Add `eval_ty` function

5. **`crates/hwml-core/src/quote.rs`** (~100 lines)
   - Add type-free quotation for type codes
   - Add `quote_ty` function

6. **`crates/hwml-core/src/check.rs`** (~150 lines)
   - Implement `is_subtype`
   - Implement `check_with_subsumption`
   - Update type checking to use `Ty`

### Supporting Files (Optional)

7. **`crates/hwml-core/src/syn/print.rs`** (~30 lines)
   - Add printing for type codes

8. **`crates/hwml-core/src/equal.rs`** (~50 lines)
   - Update equality checking for type codes

---

## 5. Testing Strategy

### Test 1: Identity Law for Type Codes

```rust
#[test]
fn test_universe_code_identity() {
    let global = GlobalEnv::mock();
    let syntax = Syntax::UniverseCode(0);
    let value = eval(&global, &Env::new(), &syntax).unwrap();
    let quoted = quote(&global, 0, &value).unwrap();
    assert_eq!(*quoted, syntax);
}
```

### Test 2: Cumulativity

```rust
#[test]
fn test_cumulativity() {
    let global = GlobalEnv::mock();
    let type0 = Ty::El(Rc::new(Value::UniverseCode(0)));
    let type1 = Ty::El(Rc::new(Value::UniverseCode(1)));

    // Type 0 <: Type 1
    assert!(is_subtype(&global, 0, &type0, &type1));

    // Type 1 </: Type 0
    assert!(!is_subtype(&global, 0, &type1, &type0));
}
```

### Test 3: Subsumption in Practice

```rust
#[test]
fn test_subsumption_usage() {
    // If we have (λx. x) : Type 0 → Type 0
    // We should be able to use it where Type 1 → Type 1 is expected
    let id_fn = Syntax::Lam(Binder::new(Syntax::Var(Index(0))));
    let type0_to_type0 = /* ... */;
    let type1_to_type1 = /* ... */;

    assert!(check_with_subsumption(&env, &id_fn, &type1_to_type1).is_ok());
}
```

---

## 6. Risk Assessment

### Low Risk ✅
- Adding new variants (non-breaking)
- Creating new `ty.rs` module
- Adding tests

### Medium Risk ⚠️
- Updating `eval.rs` and `quote.rs` (many call sites)
- Changing `check.rs` (core typechecker logic)

### High Risk 🔴
- Removing old `Universe`, `Pi` variants (breaking change)
- Updating all downstream code

### Mitigation
- **Incremental approach**: Keep both old and new code paths
- **Feature flag**: Toggle between architectures
- **Comprehensive tests**: Ensure identity law holds

---

## 7. Timeline Estimate

- **Phase 1-2**: Add variants and `ty.rs` module (1 day)
- **Phase 3-4**: Update eval and quote (1 day)
- **Phase 5**: Implement subsumption (1 day)
- **Phase 6**: Testing and migration (2 days)

**Total**: 5 days

---

## 8. Success Criteria

✅ All existing tests pass
✅ Identity law holds for type codes
✅ Cumulativity tests pass
✅ Subsumption works in practice
✅ No performance regression

---

## Next Steps

**Immediate**: Start with Phase 1 - add type code variants to `Syntax` and `Value` enums.

Would you like me to:
1. **Start Phase 1** - Add the type code variants?
2. **Create the `ty.rs` module** - Implement the semantic type system?
3. **Write the tests first** - TDD approach?

