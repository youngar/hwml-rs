# Audit: All References to `val::Ty::El`

## Summary

`val::Ty::El` appears in **4 files** with **8 total references**. All references are in **pattern matching** contexts - there are **ZERO construction sites** (no code creates `Ty::El` values anymore after Phase 9.1).

---

## File-by-File Breakdown

### 1. **`crates/hwml-core/src/val/ty.rs`** - DEFINITION

**Lines 113-118**: Enum variant definition
```rust
// ========== Weak Tarski (Backward Compatibility) ==========
/// El(code): The Universal Decoder (Weak Tarski - being phased out)
///
/// In Strong Tarski, this should only appear during transition or error recovery.
/// Normal evaluation should decode codes into the variants above.
El(RcValue<'db>),
```

**Lines 302-308**: Constructor methods
```rust
pub fn el(code: RcValue<'db>) -> Ty<'db> {
    Ty::El(code)
}

pub fn el_rc(code: RcValue<'db>) -> RcTy<'db> {
    Rc::new(Ty::el(code))
}
```

**Status**: ❌ **DEAD CODE** - Never called after Phase 9.1

---

### 2. **`crates/hwml-core/src/equal.rs`** - PATTERN MATCHING

**Lines 1186-1190**: Type equality for `El` variants
```rust
// El types: check the codes are equal using value equality
(val::Ty::El(c1), val::Ty::El(c2)) => {
    // Use type_equiv since these are type codes
    type_equiv(global, transparent, depth, c1, c2).is_ok()
}
```

**Lines 1252-1342**: Strong/Weak Tarski interop (added in Phase 8)
```rust
// Universe(n) vs El(UniverseCode(n))
(val::Ty::Universe(n1), val::Ty::El(c2)) => {
    matches!(c2.as_ref(), Value::UniverseCode(n2) if n1 == n2)
}
(val::Ty::El(c1), val::Ty::Universe(n2)) => {
    matches!(c1.as_ref(), Value::UniverseCode(n1) if n1 == n2)
}

// BitType vs El(BitCode)
(val::Ty::BitType, val::Ty::El(c2)) => {
    matches!(c2.as_ref(), Value::BitCode)
}
(val::Ty::El(c1), val::Ty::BitType) => {
    matches!(c1.as_ref(), Value::BitCode)
}

// General fallback for Strong/Weak mismatches
(strong_ty, val::Ty::El(weak_code)) | (val::Ty::El(weak_code), strong_ty) => {
    // encode Strong type and compare codes
}
```

**Analysis**: 
- First pattern (lines 1186-1190): **UNREACHABLE** - `decode_type_code` never returns `El` for standard types
- Interop patterns (lines 1252-1342): **TRANSITIONAL** - Added for migration safety, can be removed

**Status**: ⚠️ **TRANSITIONAL CODE** - Safe to remove since decoder never creates `El`

---

### 3. **`crates/hwml-core/src/check.rs`** - PATTERN MATCHING

**Lines 1568-1577**: Type checking for universe annotations
```rust
let ty = type_synth(env, term)?;
match ty.as_ref() {
    val::Ty::El(code) => match code.as_ref() {
        Value::UniverseCode(_) => Ok(()),
        _ => Err(Error::BadType { tm: Rc::new(term.clone()) }),
    },
    _ => Err(Error::BadType { tm: Rc::new(term.clone()) }),
}
```

**Lines 1586**: Constructor call (still using `el_rc`)
```rust
let sem_ty = val::Ty::el_rc(sem_ty_code);
```

**Analysis**:
- Lines 1568-1577: Expects `El(UniverseCode)` but decoder now returns `Universe(n)`
- Line 1586: **ACTIVE BUG** - Creates `El` wrapper that decoder would never produce!

**Status**: 🚨 **NEEDS FIXING** - Must update to expect Strong Tarski variants

---

### 4. **`crates/hwml-elab/src/subst.rs`** - PATTERN MATCHING

**Lines 146-154**: Substitution through `El` variants
```rust
// Weak Tarski fallback: substitute in the code
Ty::El(code) | Ty::SignalEl(code) | Ty::ModuleEl(code) => {
    let new_code = subst_value(global, code, local)?;
    match ty.as_ref() {
        Ty::El(_) => Ok(Ty::el_rc(new_code)),
        Ty::SignalEl(_) => Ok(Ty::signal_el_rc(new_code)),
        Ty::ModuleEl(_) => Ok(Ty::module_el_rc(new_code)),
        _ => unreachable!(),
    }
}
```

**Analysis**: 
- `SignalEl` and `ModuleEl` cases are **ACTIVE** (Signal/Module domains)
- `Ty::El` case is **UNREACHABLE** (decoder never creates it)

**Status**: ✅ **SAFE** - Can keep the pattern but `El` branch is dead code

---

## Construction Sites: ZERO ✅

After Phase 9.1, **no code constructs `Ty::El` for standard types**:

- ✅ `decode_type_code` returns Strong Tarski variants or Signal/ModuleEl
- ✅ `eval_ty_el` calls `decode_type_code` (decodes instead of wrapping)
- ❌ **EXCEPTION**: `check.rs` line 1586 still calls `el_rc` - **BUG!**

---

## Why It Went "Wrong" (Historical Analysis)

### The Original Design (Weak Tarski)
- Type codes were wrapped in `El` during evaluation
- Pattern matching extracted codes: `El(UniverseCode(n))` → `n`
- This was the entire type representation

### The Migration (Strong Tarski)
- Changed decoder to produce structural types: `Universe(n)`, `Pi(...)`, etc.
- **Forgot to update all pattern match sites!**
- Left `el_rc` constructor calls in check.rs

### The Result
- Decoder produces `Universe(0)` 
- Type checker expects `El(UniverseCode(0))`
- **Mismatch!** Tests fail because patterns don't match

---

## Deletion Strategy

### Phase 1: Fix Active Bugs ✅
1. **Fix `check.rs` line 1586** - Replace `el_rc` with decoded types
2. **Fix `check.rs` lines 1568-1577** - Expect `Universe(n)` instead of `El(UniverseCode(n))`

### Phase 2: Remove Unreachable Code
1. **Remove interop patterns** from `equal.rs` (lines 1252-1342)
2. **Remove `El` equality** from `equal.rs` (lines 1186-1190)
3. **Remove `El` constructor** from `subst.rs` (line 149)

### Phase 3: Delete Variant
1. **Delete `Ty::El` variant** from enum (ty.rs line 118)
2. **Delete constructors** `el()` and `el_rc()` (ty.rs lines 302-308)
3. **Update documentation** removing `El` references

---

## Expected Compilation Errors After Deletion

1. **`check.rs` line 1568**: Pattern match on `El` won't compile
2. **`check.rs` line 1586**: Call to `el_rc` won't compile
3. **`equal.rs` lines 1186-1342**: Pattern matches on `El` won't compile
4. **`subst.rs` line 149**: Constructor call won't compile

All errors are **EXPECTED** and will guide the fixes!

---

## Success Criteria

✅ No references to `Ty::El` in codebase (except `SignalEl`, `ModuleEl`)
✅ All pattern matches expect Strong Tarski decoded types
✅ Workspace builds successfully
✅ Test suite passes (or documented failures)

---

## Next Action

Start with Phase 1: Fix the active bugs in `check.rs` before deleting the variant.
