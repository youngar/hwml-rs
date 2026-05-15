# Phase 9: Delete `El` - Strong Tarski Purity

## Philosophical Foundation

### Why `El` Must Die

1. **`El` is a verb, not a noun**
   - `decode_type_code()` *is* the `El` operation
   - Once a code is decoded, the wrapper is redundant
   - We don't store the operation, we store the result

2. **Neutral types already represent stuck codes**
   - `El(Rigid(...))` ≡ `RigidTy(...)`  
   - `El(Flex(...))` ≡ `FlexTy(...)`
   - Keeping both is architectural duplication

3. **The fallback masks type errors**
   - If `decode_type_code` sees `Value::Nat(5)`, that's a **type error**
   - Wrapping it in `El(Nat(5))` hides the bug instead of surfacing it

### The Goal

Make `Ty` a **perfectly sealed structural representation**:
- Every variant corresponds to a distinct semantic type
- No "escape hatch" for unrecognized values
- Exhaustive pattern matching enforces correctness

---

## Impact Analysis

### Files That Reference `El` Variants

Based on codebase retrieval:

#### Core Type System
1. **`crates/hwml-core/src/val/ty.rs`** - Enum definition
   - Lines 118-124: `El`, `SignalEl`, `ModuleEl` variants
   - Lines 302-324: Constructor methods

2. **`crates/hwml-core/src/syn/ty.rs`** - Syntax-level enum
   - Lines 30-40: `El`, `SignalEl`, `ModuleEl` variants  
   - Lines 124-146: Constructor methods

#### Evaluation & Quotation
3. **`crates/hwml-core/src/eval.rs`**
   - Lines 1015-1017: `eval_ty_el`, `eval_ty_signal_el`, `eval_ty_module_el`
   - These call `decode_type_code` (will become the *only* path)

4. **`crates/hwml-core/src/quote.rs`**
   - Lines 1292-1294: Quotation of `El` variants
   - Lines 1286-1288: Encoding of Strong Tarski types back to `syn::Ty::El`

#### Equality & Substitution
5. **`crates/hwml-core/src/equal.rs`**
   - Lines 1187-1200: Equality for `El`, `SignalEl`, `ModuleEl`
   - Lines 1252-1342: Strong/Weak interop cases (transitional fix)

6. **`crates/hwml-elab/src/subst.rs`**
   - Lines 146-154: Substitution through `El` variants

#### Type Checking & Elaboration
7. **`crates/hwml-core/src/check.rs`**
   - Multiple pattern matches on `val::Ty::El`
   - Type synthesis/checking against `El(UniverseCode)`

8. **`crates/hwml-elab/src/unify/mod.rs`**
   - Line 119: Eta-expansion under `El(PiCode)`

9. **`crates/hwml-elab/src/diagnostic.rs`**
   - Lines 29-42: Formatting `El` variants for error messages

---

## Migration Strategy

### Phase 9.1: Make `decode_type_code` Exhaustive ✅

**File**: `crates/hwml-core/src/eval.rs`

**Current**: Has a fallback that wraps unknown values in `El`
**Target**: Return `Error::NotATypeCode` for non-type values

```rust
// BEFORE
_ => Ok(val::Ty::el_rc(code.clone())), // Fallback

// AFTER
_ => Err(Error::NotATypeCode { value: code.clone() })
```

### Phase 9.2: Update Type Checking to Expect Decoded Types

**Files**: `crates/hwml-core/src/check.rs`, `crates/hwml-elab/src/unify/mod.rs`

Replace patterns like:
```rust
// BEFORE
match ty.as_ref() {
    val::Ty::El(code) => {
        let Value::UniverseCode(level) = code.as_ref() else { ... };
        // ...
    }
}

// AFTER
match ty.as_ref() {
    val::Ty::Universe(level) => {
        // Direct structural match!
    }
}
```

### Phase 9.3: Update Quotation

**File**: `crates/hwml-core/src/quote.rs`

Lines 1286-1288 already encode Strong Tarski types and wrap in `syn::Ty::El`.
This is **correct** because syntax-level types keep `El` as the decoding operation.

**Keep**: `syn::Ty::El` (syntax-level)
**Delete**: `val::Ty::El` (semantic-level)

### Phase 9.4: Update Equality

**File**: `crates/hwml-core/src/equal.rs`

- Remove lines 1187-1200 (`El`, `SignalEl`, `ModuleEl` equality)
- Remove lines 1252-1342 (Strong/Weak interop - no longer needed)
- Equality becomes pure structural comparison

### Phase 9.5: Update Substitution

**File**: `crates/hwml-elab/src/subst.rs`

- Remove lines 146-154 (`El` substitution)
- Substitution now only handles Strong Tarski variants

### Phase 9.6: Delete Enum Variants

**File**: `crates/hwml-core/src/val/ty.rs`

- Delete lines 113-124 (variants)
- Delete lines 302-324 (constructors)
- Update module documentation

---

## Testing Strategy

1. **Run tests after each phase** to catch breakages early
2. **Expect failures** in code that relied on `El` wrapping
3. **Fix by updating to Strong Tarski patterns**

Expected test fixes:
- Replace `val::Ty::El(UniverseCode(n))` → `val::Ty::Universe(n)`
- Replace `val::Ty::El(BitCode)` → `val::Ty::BitType`
- Add type annotations where synthesis is required

---

## Success Criteria

✅ `val::Ty` enum has no `El`, `SignalEl`, or `ModuleEl` variants
✅ `decode_type_code` is exhaustive (no fallback)
✅ All pattern matches are structural
✅ Workspace builds successfully
✅ Test suite passes (or failures are documented as test bugs)

---

## Order of Execution

1. Phase 9.1: Make decoder exhaustive
2. Phase 9.2: Update type checking patterns
3. Phase 9.3: Verify quotation (should already be correct)
4. Phase 9.4: Update equality
5. Phase 9.5: Update substitution
6. Phase 9.6: Delete enum variants and constructors
7. Fix any remaining compilation errors
8. Run tests and document failures

**Estimated Time**: 2-3 hours for full migration
