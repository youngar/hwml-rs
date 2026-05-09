# Phase 4: Complete Implementation Roadmap

**Date:** 2026-05-08  
**Status:** Ready to implement  
**Total Effort:** 8-12 days (~2 weeks)

---

## Overview

Phase 4 adds **elaboration backtrace** to HWML's diagnostic system, showing users the call stack of elaboration operations that led to an error.

**Key Innovation:** Combines **3 types of context** in one error:
1. **Elaboration backtrace** - How we got here (Phase 4.1-4.5)
2. **Constraint provenance** - Why constraints exist (Phase 2.5 - complete)
3. **Meta provenance** - Metavariable dependency graph (Phase 2 - complete)

**No other type checker has all three!**

---

## Complete Phase Breakdown

### Phase 4.0: Source Tracking (NEW - CRITICAL)

**Problem:** Current code creates "synthetic" sources, losing file information  
**Solution:** Thread real `Source<'db>` through `ElabContext`  
**Effort:** 1-2 days

**Changes:**
- Add `current_source: Source<'db>` to `ElabContext`
- Update file elaboration entry points to create real `Source`
- Remove all `Source::new(db, SourceInfo::Synthetic(...))` calls
- Add `expr_byte_range()` helper

**Deliverables:**
- ✅ Errors show real file paths (not "synthetic")
- ✅ Works across file boundaries (imports)
- ✅ Foundation for Ariadne multi-file diagnostics

**Plan:** `wiki/implementation/provenance/PHASE-4.0-SOURCE-TRACKING-PLAN.md`

---

### Phase 4.1: Infrastructure (1-2 days)

**Build the foundation**

**Changes:**
- Create `crates/hwml-elab/src/context.rs` (~200 lines)
  - `ElabContext` with trace stack and source tracking
  - `ElabFrame` and `ElabFrameKind` types
  - `TraceGuard` RAII pattern
- Update `ElabError` enum (add `elab_backtrace` to all 9 variants)
- Add `code()` method for error codes (E001-E009)
- Add `context: ElabContext<'db>` field to `Elaborator`

**Deliverables:**
- ✅ Context module complete and tested
- ✅ Error types ready for backtrace
- ✅ Elaborator has context field
- ✅ Compiles (with temporary `Vec::new()` for backtraces)

---

### Phase 4.2: Error Helpers (1 day)

**Make error construction easy**

**Changes:**
- Add 8 error helper methods to `Elaborator`
  - `error_type_mismatch(expected, actual)`
  - `error_not_in_scope(name)`
  - `error_cannot_infer()`
  - `error_unification_failure(lhs, rhs)`
  - `error_occurs_check(meta)`
  - `error_scope_violation(meta)`
  - `error_meta_already_solved(meta)`
  - `error_not_implemented(feature)`
- Helpers automatically capture location and backtrace from context

**Deliverables:**
- ✅ Less boilerplate in error construction
- ✅ Impossible to forget backtrace capture
- ✅ Consistent error creation across codebase

---

### Phase 4.3: Instrumentation (2-3 days)

**Add trace guards and replace error sites**

**Changes:**
- Instrument `synth()` and `check()` with trace guards
- Replace 58 error construction sites with helper methods:
  - 19 `NotInScope` errors
  - 8 `CannotInfer` errors  
  - 7 `UnificationFailure` errors
  - 4 `TypeMismatch` errors
  - Others (ScopeViolation, OccursCheck, etc.)
- Update solver/unifier to accept `&Elaborator` (not just `&mut SolverState`)

**Strategy:**
- Compiler-driven: Add field → compiler finds all sites → replace one-by-one
- Use incremental testing

**Deliverables:**
- ✅ All elaboration operations traced
- ✅ All errors use helpers
- ✅ Backtraces captured everywhere

---

### Phase 4.4: Enhanced Display (1 day)

**Make errors beautiful**

**Changes:**
- Update `Display` implementation for `ElabError`
  - Show error code: `error[E001]:`
  - Show elaboration backtrace (if non-empty)
  - Show constraint context (existing - for UnsolvedMeta)
  - Show provenance chain (existing - for UnsolvedMeta)
- Add `format_elab_backtrace()` helper

**Example output:**
```
error[E001]: type mismatch at main.hwml:10..15
  expected: Nat
  got:      Bool

elaboration backtrace:
  0: checking expression against Nat at main.hwml:10..15
  1: checking function application at main.hwml:8..20
  2: checking definition 'test' at main.hwml:1..100

constraint context:
  origin: return type check
  created by: C10
```

**Deliverables:**
- ✅ Professional error output
- ✅ Error codes in messages
- ✅ Combined backtrace display

---

### Phase 4.5: Testing & Documentation (1-2 days)

**Ensure quality**

**Changes:**
- Update existing tests (fix error construction)
- Add integration tests:
  - Single-file errors show file path
  - Multi-file errors show correct files
  - Backtrace depth is reasonable
  - Error codes are correct
- Create `docs/error-codes.md`
  - Document all 9 error codes
  - Add examples and "how to fix"
- Performance benchmarking

**Deliverables:**
- ✅ All tests passing
- ✅ Error code documentation complete
- ✅ Performance acceptable (<10% regression)

---

## Timeline Summary

| Phase | Description | Days | Cumulative |
|-------|-------------|------|------------|
| **4.0** | Source tracking | 1-2 | 1-2 |
| **4.1** | Infrastructure | 1-2 | 2-4 |
| **4.2** | Error helpers | 1 | 3-5 |
| **4.3** | Instrumentation | 2-3 | 5-8 |
| **4.4** | Display | 1 | 6-9 |
| **4.5** | Testing | 1-2 | 7-11 |
| **Buffer** | Unknown issues | 1 | 8-12 |
| **TOTAL** | | **8-12 days** | **~2 weeks** |

---

## Key Documents

**Planning:**
- `PHASE-4-GAP-ANALYSIS.md` - Current vs. ideal comparison (605 lines)
- `PHASE-4.0-SOURCE-TRACKING-PLAN.md` - Source tracking plan (150 lines)
- `PHASE-4-COMPLETE-ROADMAP.md` - This document

**Research:**
- `asai-vs-hwml-comparison.md` - What to build (636 lines)
- `asai-detailed-review.md` - Asai internals (401 lines)
- `ASAI-COMPARISON-SUMMARY.md` - Executive summary (150 lines)
- `LOCATION-TRACKING-CRITICAL-ISSUE.md` - Source tracking issue (150 lines)

**Architecture:**
- `ADR-015-elaboration-provenance-architecture.md` - Design decisions (560+ lines)

**Total:** ~2,700 lines of comprehensive planning documentation

---

## Success Criteria

### Minimum Viable Phase 4
- ✅ All errors have error codes (E001-E009)
- ✅ All errors capture elaboration backtrace
- ✅ Errors show real file paths (not "synthetic")
- ✅ `synth()` and `check()` instrumented with trace guards
- ✅ Display shows error code + backtrace
- ✅ Tests passing

### Ideal Phase 4
- ✅ All 58 error sites use helpers
- ✅ No `span: None` in user-facing errors
- ✅ Cross-file errors work correctly
- ✅ Backtraces are informative (not too deep/shallow)
- ✅ `docs/error-codes.md` complete
- ✅ Performance <10% regression

---

## Expected Impact

**Before Phase 4:**
```
error: type mismatch at 142..150
  expected: Nat
  got:      Bool
```

**After Phase 4:**
```
error[E001]: type mismatch at main.hwml:142..150
  expected: Nat
  got:      Bool

elaboration backtrace:
  0: checking expression against Nat at main.hwml:142..150
  1: checking function return type at main.hwml:140..155
  2: checking definition 'process' at main.hwml:135..200

constraint context:
  origin: return type check
  created by: C10
  blocking: C10, C15

provenance chain:
  ?42 <- created from underscore at main.hwml:142
  ?40 <- parameter type inference at main.hwml:95
```

**Unique to HWML:** Shows elaboration + constraint + provenance in ONE error!

---

## Risk Mitigation

**High Risk:**
1. Signature changes cascade → Use compiler to find all sites
2. Test breakage → Incremental fixes, use `Vec::new()` initially

**Medium Risk:**
3. Performance regression → Benchmark, optimize with SmallVec if needed
4. Missing instrumentation → Grep for all elaboration functions

**Low Risk:**
5. Display formatting → Test with real errors, iterate

---

## Next Steps

1. **Review this plan**
2. **Choose start date**
3. **Begin Phase 4.0** (source tracking)
4. **Daily check-ins** to track progress
5. **Celebrate** when complete! 🎉

---

## Notes

- This builds on completed work: Phases 1-3 (constraint/meta provenance)
- Asai review informed the design (effect handlers → RAII)
- ADR-015 documents the "why" for this architecture
- Phase 5 (Ariadne) will use this foundation for colored multi-span output

**Phase 4 will make HWML's diagnostics best-in-class!** 🚀
