# syn::Ty Implementation - Task Summary

## Overview

This document provides a quick reference for implementing `syn::Ty` - syntax-level types following the Tarski universe pattern.

## Completed

- [x] **Analysis and Planning** - Detailed analysis of codebase and implementation plan created

## Implementation Tasks (10 tasks)

### Phase 1: Core Infrastructure (Non-Breaking)

1. **Create syn::Ty module** 
   - File: `crates/hwml-core/src/syn/ty.rs` (NEW)
   - Define `Ty<'db>` enum with 8 variants
   - Add type aliases: `RcTy<'db>`, `BindingTy<'db>`
   - Implement constructor methods (following `val::Ty` pattern)

2. **Module system integration**
   - File: `crates/hwml-core/src/syn/mod.rs`
   - Add `pub mod ty;` and `pub use ty::*;`
   - File: `crates/hwml-core/src/lib.rs`
   - Update re-exports for syn::Ty

3. **Add type evaluation**
   - File: `crates/hwml-core/src/eval.rs`
   - Implement `eval_ty(&mut Environment, &syn::Ty) -> Result<RcTy<val::Ty>>`
   - Handle all 8 syn::Ty variants
   - Special care for Pi types (extend context)

4. **Add type quotation**
   - File: `crates/hwml-core/src/quote.rs`
   - Implement `quote_ty(db, global, depth, &val::Ty) -> Result<syn::RcTy>`
   - Mirror eval_ty structure
   - Handle De Bruijn level management

5. **Implement printing for syn::Ty**
   - File: `crates/hwml-core/src/syn/print.rs`
   - Add `Print` trait for `syn::Ty`, `syn::RcTy`, `syn::BindingTy`
   - Format Pi types as `(x : A) → B`
   - Format El decoders as `El(code)`

6. **Implement parsing for syn::Ty**
   - File: `crates/hwml-core/src/syn/parse.rs`
   - Add `p_type()` parser function
   - Parse universe types, Pi types, El decoders
   - Handle precedence correctly

7. **Add helper functions**
   - File: `crates/hwml-core/src/syn/ty.rs`
   - Add `Ty::universe(level)` - common El(UniverseCode) pattern
   - Add `Ty::pi_code()` - El(PiCode) pattern
   - Add `Ty::bit()` - El(BitCode) pattern

### Phase 2: Breaking Changes

8. **Update Check node structure**
   - File: `crates/hwml-core/src/syn/syntax.rs`
   - Change `Check::ty` from `RcSyntax<'db>` to `RcTy<'db>`
   - Update `Check::new()` signature
   - Update `Syntax::check()` and `Syntax::check_rc()` helpers

9. **Update typechecking**
   - File: `crates/hwml-core/src/check.rs`
   - Update `type_synth_check()` to work with syn::Ty
   - Call `eval_ty()` to get semantic type
   - Handle conversion from val::Ty to val::Value (type codes)

10. **Update test cases**
    - Files: Multiple test files across codebase
    - Pattern: `Syntax::check_rc(Syntax::UniverseCode(0).into(), term)`
    - Replace: `Syntax::check_rc(syn::Ty::el_rc(Syntax::UniverseCode(0).into()), term)`
    - Update all Check node creations

## Testing Tasks (5 tasks)

1. **Round-trip tests** - syn::Ty → val::Ty → syn::Ty
2. **Printing tests** - Verify correct output for all variants
3. **Parsing tests** - Parse and verify type expressions
4. **Check node tests** - Test Check with syn::Ty
5. **Integration tests** - Full test suite passes

## Key Files to Modify

| File | Type | Changes |
|------|------|---------|
| `crates/hwml-core/src/syn/ty.rs` | NEW | Complete new module |
| `crates/hwml-core/src/syn/mod.rs` | MINOR | Add exports |
| `crates/hwml-core/src/lib.rs` | MINOR | Add re-exports |
| `crates/hwml-core/src/syn/syntax.rs` | BREAKING | Change Check::ty type |
| `crates/hwml-core/src/eval.rs` | MAJOR | Add eval_ty function |
| `crates/hwml-core/src/quote.rs` | MAJOR | Add quote_ty function |
| `crates/hwml-core/src/syn/print.rs` | MAJOR | Add Print impls |
| `crates/hwml-core/src/syn/parse.rs` | MAJOR | Add p_type parser |
| `crates/hwml-core/src/check.rs` | MAJOR | Update type_synth_check |
| Test files (multiple) | BREAKING | Update Check constructors |

## Migration Strategy

### Recommended Order

1. Tasks 1-7 (non-breaking additions)
2. Run tests to ensure no regressions
3. Tasks 8-10 (breaking changes)
4. Fix all compilation errors
5. Run full test suite
6. Tasks 11-15 (new tests)

### Risk Mitigation

- **Low Risk**: Tasks 1-7 add new code without changing existing behavior
- **Medium Risk**: Tasks 8-9 change types but are mechanical
- **High Risk**: Task 10 requires finding all Check creations

## Success Criteria

- [ ] All 10 implementation tasks complete
- [ ] All 5 testing tasks complete
- [ ] Full test suite passes
- [ ] No compilation errors or warnings
- [ ] Round-trip property holds for all syn::Ty variants
- [ ] Check nodes properly use syn::Ty instead of RcSyntax

## References

- **Detailed Plan**: `design/syn-ty-implementation-plan.md`
- **Tarski Universes**: `design/to-ingest/universes.md`
- **val::Ty Reference**: `crates/hwml-core/src/val/ty.rs`
- **val::Value Reference**: `crates/hwml-core/src/val/value.rs`

## Next Steps

Start with Task 1: Create the syn::Ty module as the foundation for all other work.
