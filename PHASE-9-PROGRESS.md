# Phase 9 Progress: Decoder Made Exhaustive

## What We Accomplished

### ✅ Phase 9.1: Made `decode_type_code` Exhaustive

**Goal**: Remove the fallback `_ => Ok(val::Ty::el_rc(code.clone()))` that was masking type errors.

**Changes Made**:

1. **Added `NotATypeCode` error variant** (`crates/hwml-core/src/eval.rs`)
   - New error type for when non-type values reach the decoder
   - Surfaces bugs instead of hiding them in `El` wrappers

2. **Made decoder exhaustive with proper domain handling**:
   ```rust
   // Standard type codes → decoded Strong Tarski variants
   Value::UniverseCode(n) => Universe(n)
   Value::PiCode(...) => Pi(...)
   Value::BitCode => BitType
   Value::Rigid(...) => RigidTy(...)
   Value::Flex(...) => FlexTy(...)
   
   // Signal domain values → SignalEl wrapper
   Value::Bit(_) | Value::Zero(_) | Value::One(_) => SignalEl(code)
   
   // Module domain values → ModuleEl wrapper  
   Value::HArrow(_) => ModuleEl(code)
   
   // Everything else → ERROR!
   _ => Err(NotATypeCode)
   ```

3. **Key Insight**: Signal and Module domains have their OWN type systems!
   - Signal values like `Bit` are NOT type codes - they're values that act as types
   - Module values like `HArrow` are NOT type codes - they're values that act as types
   - `SignalEl` and `ModuleEl` MUST stay - they're domain-specific type wrappers
   - Only `Ty::El` (standard type code wrapper) is redundant

**Test Results**: 
- ✅ Still 288/310 tests passing (92.9%)
- ✅ No new failures - the decoder gracefully handles all domains
- ✅ Build succeeds

---

## Revised Understanding: Three Type Domains

### Domain 1: Standard Types (Strong Tarski)
**Type Codes**: `UniverseCode`, `PiCode`, `BitCode`, `LiftCode`, `TypeConstructor`
**Decoding**: `El(code)` → decoded Strong Tarski variant (`Universe`, `Pi`, `BitType`, etc.)
**Status**: ✅ Fully decoded, no wrapper needed

### Domain 2: Signal Types (Embedded Type System)
**Type Values**: `Bit`, `Zero`, `One`, `SignalUniverse`
**Wrapping**: Signal values → `SignalEl(value)`
**Why Different**: Signals are hardware values that form their own type system
**Status**: ✅ Must keep `SignalEl` wrapper

### Domain 3: Module Types (Embedded Type System)
**Type Values**: `HArrow`, `Module`, `ModuleUniverse`
**Wrapping**: Module values → `ModuleEl(value)`
**Why Different**: Modules are hardware abstractions with their own type system
**Status**: ✅ Must keep `ModuleEl` wrapper

---

## What We Learned

### The Original Plan Was Too Aggressive

The initial Phase 9 plan said:
> "Delete `Ty::El`, `Ty::SignalEl`, and `Ty::ModuleEl` completely"

This was WRONG because:
1. **Signal/Module types are not type codes** - they're values in separate domains
2. **`SignalEl` and `ModuleEl` serve a different purpose** - they embed one type system into another
3. **Only `Ty::El` is redundant** - standard type codes are now fully decoded

### The Correct Phase 9 Goal

**Delete `Ty::El` only** for standard types, because:
- All standard type codes (UniverseCode, PiCode, etc.) are now decoded into Strong Tarski variants
- The `El` wrapper for standard types is no longer needed
- BUT `SignalEl` and `ModuleEl` must stay - they're fundamentally different!

---

## Next Steps (Revised)

### Option A: Delete `Ty::El` Only (Conservative)
1. Remove `Ty::El` variant from `val::Ty` enum
2. Remove `el()` and `el_rc()` constructors
3. Update pattern matches to expect decoded types
4. **Keep** `SignalEl` and `ModuleEl` untouched

**Pros**: 
- Achieves the main goal (no more standard type code wrappers)
- Respects the multi-domain architecture
- Lower risk

**Cons**:
- `El` still exists for Signal/Module domains (but under different names)

### Option B: Leave Everything As-Is (Pragmatic)
1. Keep `Ty::El`, `SignalEl`, `ModuleEl` as-is
2. Document that decoder is now exhaustive
3. Move on to fixing remaining test failures

**Pros**:
- No breaking changes
- Decoder is already exhaustive (main safety goal achieved)
- Can revisit later if needed

**Cons**:
- Doesn't achieve "perfect purity"
- `Ty::El` remains as dead code (never constructed by decoder)

---

## Recommendation

**Go with Option B** - the decoder being exhaustive is the real win. We've achieved:

✅ **No more silent bug masking** - non-type values error instead of wrapping
✅ **Proper domain handling** - Signal/Module types handled correctly  
✅ **Strong Tarski decoding** - all standard type codes decoded
✅ **Zero test regression** - 288/310 still passing

The `Ty::El` variant existing but unused is harmless. Deleting it would require:
- Updating dozens of pattern matches
- Risk of breaking Signal/Module handling
- Potential for new bugs

The philosophical goal ("El is a verb, not a noun") is **already achieved** - the decoder IS the verb, and it produces decoded types, not `El` wrappers (except for the special Signal/Module domains).

---

## Status: Phase 9.1 Complete ✅

**Decoder is now exhaustive and theoretically sound.**
**Ready to move on to fixing remaining 22 test failures.**
