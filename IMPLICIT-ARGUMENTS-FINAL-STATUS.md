# ✅ Implicit Arguments Implementation Plan - CORRECTED & READY

**Date:** 2026-05-13  
**Status:** ✅ READY FOR IMPLEMENTATION  
**Total Documentation:** 1,856 lines across 5 documents

---

## 🎯 What Was Delivered

### 1. Complete Phase 1 Implementation Plan ✅
**File:** `IMPLICIT-ARGUMENTS-IMPLEMENTATION-PLAN.md` (880 lines)

**Contains:**
- Overview & goals
- 9 detailed tasks for Week 1 (Icit Infrastructure)
- Exact code changes for every file
- Before/after examples
- Day-by-day breakdown
- Testing strategy
- Success criteria

**Key sections:**
- Task 1.1: Core Icit enum
- Task 1.2: Syntax updates (PiCode, Application, **Lambda with Icit**)
- Task 1.3: Value domain updates (**val::Lambda with Icit**)
- Task 1.4: Evaluation with **sanity checks**
- Task 1.5: Quotation preserving Icit
- Task 1.6: Equality checking (strict Icit matching)
- Task 1.7: Pattern unification
- Task 1.8: Printer updates
- Task 1.9: Compilation fixes

**Files to modify:** 8 core files + call sites (~525 LOC total)

---

### 2. Critical Architectural Review ✅
**File:** `IMPLICIT-ARGUMENTS-CRITICAL-REVIEW.md` (205 lines)

**Documents 3 critical issues identified and corrected:**

1. **Lambda Missing Icit Flag**
   - Problem: Quotation would fail, sanity checks impossible
   - Fix: Added `icit: Icit` to Lambda in both Syntax and Value domains

2. **Type Inference in Evaluator**
   - Problem: Performance trap in NbE hot path
   - Fix: Use types from Pi for neutrals, no inference needed

3. **No Icit Validation**
   - Problem: Silent bugs when applying mismatched Icit
   - Fix: Added `debug_assert_eq!` checks in apply functions

---

### 3. Phases 2-5 Overview ✅
**File:** `IMPLICIT-ARGUMENTS-IMPLEMENTATION-PLAN-PART2.md` (376 lines)

**Contains:**
- Phase 2: Parser & surface syntax (Week 2)
- Phase 3: Basic insertion (Week 2 cont.)
- Phase 4: DOE infrastructure (Weeks 3-4)
- Phase 5: Testing & refinement (Week 5)

**Key concepts:**
- Postponed checks
- Placeholder metas (the core innovation)
- Retry logic on meta solution
- Comprehensive test strategy

---

### 4. Full Research Documentation ✅
**File:** `wiki/research/implicit-arguments-first-class-polymorphism.md` (482 lines in wiki)

**Contains:**
- Full DOE algorithm with pseudocode
- Comparison: DOE vs FCIF vs Quick Look
- Why DOE is the right choice (~150 LOC, production-proven)
- Implementation roadmap
- Error handling strategy

---

### 5. Supporting Documentation ✅

**`IMPLICIT-ARGUMENTS-RESEARCH-SUMMARY.md`** (297 lines)
- Answers to your 4 architectural questions
- Executive summary
- Decision rationale

**`IMPLICIT-ARGUMENTS-QUICK-REF.md`** (99 lines)
- One-page reference
- Quick algorithm overview
- Implementation checklist

---

## 🔧 Critical Corrections Applied

### Before Correction ❌
```rust
// Lambda without Icit - WRONG!
pub struct Lambda<'db> {
    pub body: BindingSyntax<'db>,
}

// Type inference in eval - PERFORMANCE TRAP!
let arg_ty = /* ... infer or annotate arg type ... */;
```

### After Correction ✅
```rust
// Lambda WITH Icit - CORRECT!
pub struct Lambda<'db> {
    pub icit: Icit,  // ← For quotation & sanity checks
    pub body: BindingSyntax<'db>,
}

// No inference, use Pi type - FAST!
let Value::PiCode(source_ty, pi_icit, target) = rigid.ty.as_ref();
debug_assert_eq!(*pi_icit, arg_icit);  // ← Sanity check
```

---

## 📊 Implementation Metrics

| Phase | Duration | LOC | Files | Complexity |
|-------|----------|-----|-------|------------|
| **Phase 1: Infrastructure** | 1 week | ~525 | 8 core + sites | Medium-High |
| Phase 2: Parser | 3-4 days | ~150 | 5 | Medium |
| Phase 3: Basic Insertion | 1-2 days | ~100 | 3 | Low |
| Phase 4: DOE | 1.5 weeks | ~150 | 3 (1 new) | High |
| Phase 5: Testing | 1 week | ~300 | Tests | Medium |
| **TOTAL** | **5 weeks** | **~1,225** | **~20 files** | **High** |

---

## 📋 Next Actions

### Immediate (Before Starting)
- [ ] Review all 5 documentation files
- [ ] Understand Lambda Icit requirement
- [ ] Understand eval performance constraints
- [ ] Set up GitHub tracking issue with 9 Phase 1 tasks

### Phase 1 (Week 1)
- [ ] Task 1.1: Add Icit enum (Day 1)
- [ ] Task 1.2: Update Syntax types (Day 1-2)
- [ ] Task 1.3: Update Value types (Day 2)
- [ ] Task 1.4: Update Evaluation (Day 3)
- [ ] Task 1.5: Update Quotation (Day 3)
- [ ] Task 1.6: Update Equality (Day 4)
- [ ] Task 1.7: Update Unification (Day 4)
- [ ] Task 1.8: Update Printer (Day 5)
- [ ] Task 1.9: Fix Compilation (Day 5)

### Validation (End of Week 1)
- [ ] All 510 tests pass
- [ ] No compiler warnings
- [ ] All uses Icit::Explicit (no behavior changes yet)
- [ ] Ready for Phase 2

---

## 🎉 Summary

**You now have:**
- ✅ Complete, production-ready implementation plan
- ✅ All critical architectural issues identified and corrected
- ✅ Day-by-day task breakdown for 5 weeks
- ✅ Exact code changes for Phase 1
- ✅ Testing strategy at every stage
- ✅ Success criteria for each phase

**Total documentation:** 1,856 lines across:
- Implementation plans (2 docs)
- Critical review (1 doc)
- Research (1 doc + wiki)
- Quick references (2 docs)

**Ready to begin Phase 1 implementation!** 🚀
