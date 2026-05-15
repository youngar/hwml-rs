# Architectural Fix: Values Should Store Semantic Types, Not Type Codes

## The Real Issue

Instead of just removing "placeholder" comments, we discovered and fixed a **fundamental architectural bug** in the Tarski implementation:

### What Was Wrong

Several value structures were storing their types as **type codes** (`RcValue<'db>`) instead of **semantic types** (`val::RcTy<'db>`):

1. `Rigid::ty: RcValue<'db>` ❌
2. `Flex::ty: RcValue<'db>` ❌  
3. `Let::ty: RcValue<'db>` ❌
4. `StuckApplication::ty: RcValue<'db>` ❌
5. `PatternBinding::ty: RcValue<'db>` ❌

This violated the **Tarski separation principle**: 
- **Types** (`Ty`) and **Terms** (`Value`) are distinct domains
- Values should know their TYPES, not their type codes
- Type codes are terms that must be decoded via `El(code)` to get types

### The Symptom

This led to "placeholder" hacks like:
```rust
let ty_code = match ty.as_ref() {
    val::Ty::El(code) => code.clone(),
    val::Ty::SignalEl(code) => code.clone(),
    val::Ty::ModuleEl(code) => code.clone(),
    _ => Rc::new(Value::UniverseCode(0)), // ❌ HACK for native types
};
```

**Why this was wrong**: Variables of native types like `Pi(A, B)` or `UniverseType` don't HAVE type codes - they only exist at the type level!

## The Fix

### 1. Changed Value Structures to Store Semantic Types ✅

```rust
// Before ❌
pub struct Rigid<'db> {
    pub ty: RcValue<'db>,  // type CODE
    // ...
}

// After ✅
pub struct Rigid<'db> {
    pub ty: val::RcTy<'db>,  // semantic TYPE
    // ...
}
```

Applied to:
- `Rigid::ty`
- `Flex::ty`
- `Let::ty`
- `StuckApplication::ty`
- `PatternBinding::ty`

### 2. Updated Environment Signatures ✅

```rust
// Before ❌
pub fn push_var(&mut self, ty: RcValue<'db>) -> RcValue<'db>

// After ✅
pub fn push_var(&mut self, ty: val::RcTy<'db>) -> RcValue<'db>
```

Applied to:
- `LocalEnv::push_var`
- `LocalEnv::extend_vars`
- `Environment::push_var`
- `Environment::extend_vars`
- `Environment::push_transparent`

### 3. Removed UniverseCode(0) Placeholders ✅

No more hacks needed! Variables of native types like `Pi` simply store their actual type:
```rust
pub fn push_var(&mut self, ty: val::RcTy<'db>) -> RcValue<'db> {
    let var = Value::variable_rc(Level::new(self.depth()), ty.clone());
    self.push(var.clone(), ty);
    var
}
```

## What Stays as Type Codes

Not everything should be changed! These correctly store type CODES:

1. **`Normal::ty: RcValue<'db>`** ✅ - Used in eliminators/spines for application
2. **`EqType::ty: RcValue<'db>`** ✅ - `Eq A x y` where A is a code
3. **`SLift::ty: RcValue<'db>`** ✅ - Lifts a signal type code
4. **`MLift::ty: RcValue<'db>`** ✅ - Lifts a module type code

These need codes because they're used for type-directed operations that pattern-match on codes.

## Remaining Work

Code that creates variables for quotation/equality checking needs to wrap type codes in `El`:

```rust
// Before ❌
let var = Value::variable_rc(Level::new(depth), pi_source.clone());

// After ✅
let var = Value::variable_rc(Level::new(depth), val::Ty::el_rc(pi_source.clone()));
```

## Why This Matters

This fix enforces the mathematical rigor of the Tarski architecture:
- ✅ Values know their semantic TYPES
- ✅ Type codes are properly decoded via `El`
- ✅ No more "placeholder" hacks for native types
- ✅ Clear separation between types and terms

The architecture is now mathematically sound!
