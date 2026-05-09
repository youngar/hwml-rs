# Asai vs HWML Comparison - Executive Summary

**Date:** 2026-05-08  
**Status:** ✅ Analysis Complete, Ready for Phase 4 Implementation  
**Full Details:** See `wiki/research/asai-vs-hwml-comparison.md`

---

## TL;DR

**HWML has strong constraint/meta provenance that Asai lacks.**  
**Asai has elaboration backtrace that HWML needs.**  
**Together = Best-in-class diagnostics.**

---

## Critical Gaps Identified

### 1. 🔴 Elaboration Backtrace (P1 - Critical)
- **What's missing:** Call stack of elaboration operations
- **Impact:** Users don't know "how we got here" in complex errors
- **Effort:** 5-7 days
- **Solution:** RAII-based trace guards (Phase 4)

### 2. 🟡 Location Inheritance (P2 - High)
- **What's missing:** Automatic location propagation
- **Impact:** Verbose error construction, easy to forget spans
- **Effort:** 1-2 days
- **Solution:** Store current location in `ElabContext`

### 3. 🟢 Error Codes (P3 - Medium)
- **What's missing:** Short, Google-able codes like "E001"
- **Impact:** Harder to document, track, and search for errors
- **Effort:** 1 day
- **Solution:** Add `code()` method to `ElabError`

### 4. 🟡 Unified Display (P4 - High)
- **What's missing:** Integration of elaboration + constraint backtraces
- **Impact:** Incomplete diagnostic story
- **Effort:** 1 day
- **Solution:** Enhanced `Display` implementation

---

## What HWML Does Better Than Asai

✅ **Constraint Provenance** - Tracks why constraints were created  
✅ **Meta Provenance** - Tracks metavariable origins and dependencies  
✅ **Zero-Overhead Side-Tables** - No cost in success case  
✅ **Type Flow Tracking** - `ConstraintOrigin` shows value flow  

These features are **unique to HWML** and should be preserved!

---

## Expected Error Output After Phase 4

```
error[E001]: type mismatch at 142..150
  expected: Nat
  got:      Bool

elaboration backtrace:
  0: checking expression against Nat at 142..150
  1: checking function return type at 140..155
  2: checking definition 'process' at 135..200
  3: elaborating module '/main' at 1..500

constraint context:
  origin: return type check at 142..150
  created by: C10
  blocking: C10, C15

provenance chain:
  ?42 <- created from underscore at 100..101
  ?40 <- parameter type inference at 95..100
```

**This combines:**
- Elaboration context (from Asai)
- Constraint context (unique to HWML)
- Provenance chain (unique to HWML)
- Error codes (from Asai)

---

## Implementation Roadmap

### Week 1: Infrastructure
- Create `ElabContext` with `trace_stack`
- Implement `TraceGuard` RAII pattern
- Add `elab_backtrace` to all `ElabError` variants

### Week 2: Instrumentation
- Wrap `check()`, `synth()` with traces
- Add error helper methods
- Update all error construction sites

### Week 3: Polish
- Add error codes
- Enhanced `Display` implementation
- Integration tests
- Document error codes

**Total: 2-3 weeks for production-ready diagnostics**

---

## Key Design Decisions

### ✅ Keep Both Provenance Systems
- Constraint provenance: "Why this constraint?"
- Elaboration backtrace: "How did we get here?"
- They're complementary, not redundant

### ✅ Use RAII, Not Effects
- Rust doesn't have effect handlers
- RAII guards are idiomatic and safe
- Automatic cleanup on early returns

### ✅ Eager Frames, Lazy Formatting
- Push frames immediately (small cost)
- Format descriptions only on error
- Use `SmallVec` to avoid heap allocation

### ✅ Error Helper Methods
```rust
// Clean API:
elab.error_not_in_scope(name)

// Instead of:
ElabError::NotInScope {
    name,
    span: Some(location.clone()),
    elab_backtrace: elab.context.snapshot(),
}
```

---

## Performance Impact

**Before (Current):**
- Zero overhead for provenance (side-tables)
- Manual span threading (error-prone)

**After (Phase 4):**
- ~10-20 cycles per elaboration call (negligible)
- Automatic span inheritance (correct by default)
- Small memory cost (~40 bytes per stack frame)

**Optimization:**
- Use `SmallVec<[ElabFrame; 8]>` (no heap for shallow calls)
- Lazy description formatting (only on error)

**Trade-off:** Small runtime cost for dramatically better diagnostics.

---

## References

- **Full Comparison:** `wiki/research/asai-vs-hwml-comparison.md`
- **Asai Deep Dive:** `wiki/research/asai-detailed-review.md`
- **Architecture:** `wiki/decisions/ADR-015-elaboration-provenance-architecture.md`
- **Current Progress:** `wiki/implementation/provenance/SESSION-SUMMARY.md`

---

## Recommendation

**✅ APPROVED:** Proceed with all 4 priorities in Phase 4.

HWML will have **best-in-class diagnostics** that combine:
- Elaboration backtrace (Asai's strength)
- Constraint/meta provenance (HWML's unique strength)
- Rust-quality error messages

**Next Step:** Begin Phase 4.1 implementation (Infrastructure).
