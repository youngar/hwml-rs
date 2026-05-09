# Provenance Tracking Gap Analysis

**Date:** 2026-05-08  
**Context:** Deep dive comparison of current implementation vs. research best practices

---

## Executive Summary

We've made **excellent progress** on metavariable provenance (Phase 1-2 complete, Phase 3 in progress), but we're **missing a critical component**: **Constraint Origin Tracking**. According to the research, this is just as important as metavariable origins for quality error messages.

### What We Have ✅

1. **MetaProvenance Side-Table** - Tracks where/why metas were created
2. **Rich MetaOrigin Variants** - Detailed semantic origins for all user-facing metas
3. **Typed Origins** - Expected types stored in origin data
4. **Constraint Tracking** - Links metas to constraints that create/block them
5. **Display Utilities** - Nice formatting for provenance chains
6. **Enriched Errors** - `ElabError::UnsolvedMeta` uses full provenance

### What We're Missing ❌

1. **Constraint Origin Tracking** - NO `ConstraintOrigin` enum exists
2. **Source Locations on Constraints** - Constraints don't store `created_at: SourceRange`
3. **Semantic Constraint Origins** - No explanation of WHY constraints exist
4. **Multi-span Error Rendering** - Can't show "value flows from X to Y"
5. **Constraint Graph Diagnosis** - Can't find minimal unsatisfiable subsets

---

## Research Says: We Need BOTH Meta AND Constraint Origins

From `wiki/research/elaboration-error-messages.md`:

> **Key Findings**  
> 1. Track constraint origins, not just constraints
> 2. Metavariable origin tracking is ESSENTIAL
> 3. Data flow explanations work best
> 4. Modern compilers (Rust, GHC, Lean) track origins extensively

### The Pattern from Production Systems

**Rust:**
```rust
pub struct ObligationCause<'tcx> {
    pub span: Span,
    pub code: ObligationCauseCode<'tcx>,  // 50+ variants!
}
```

**GHC:**
```haskell
data CtOrigin
  = GivenOrigin GivenLoc
  | TypeEqOrigin { uo_actual, uo_expected, uo_thing }
  | FunDepOrigin1 { ... }
  -- 40+ more variants
```

**Lean 4:**
```lean
structure Justification where
  -- Full proof tree of why constraint exists
```

---

## Current State Assessment

### ✅ Phase 1-2: Metavariable Provenance (DONE)

| Component | Status | Quality |
|-----------|--------|---------|
| `MetaProvenance` side-table | ✅ | Excellent |
| `MetaOrigin` with 7 variants | ✅ | Good |
| Type information in origins | ✅ | Good |
| Parent/child meta links | ✅ | Excellent |
| Blocking constraint tracking | ✅ | Excellent |
| Creation constraint linking | ✅ | Excellent |
| Display utilities | ✅ | Good |

**Test Coverage:** 21/21 tests passing ✅

### ❌ Phase 2.5: Constraint Provenance (MISSING)

| Component | Status | Impact |
|-----------|--------|--------|
| `ConstraintOrigin` enum | ❌ Missing | **CRITICAL** |
| `created_at` on constraints | ❌ Missing | **HIGH** |
| `origin` on `Constraint` | ❌ Missing | **CRITICAL** |
| Updated `emit_eq` API | ❌ Missing | **HIGH** |
| Call site migrations | ❌ Missing | **HIGH** |
| Multi-span error rendering | ❌ Missing | **MEDIUM** |

**Impact:** Cannot explain "why" constraints exist, only "what" they are.

---

## Gap Analysis: What Errors Can/Can't We Explain?

### ✅ Errors We CAN Explain Well Now

1. **Unsolved underscore:** "underscore placeholder at line 10"
2. **Unsolved dot resolution:** "dot notation `.foo` at line 15"
3. **Meta dependencies:** "?2 depends on ?1 which depends on ?0"
4. **Blocking info:** "?42 is blocking constraints [C5, C7]"

### ❌ Errors We CANNOT Explain Yet

1. **Unification failures:** ❌ Can't say "because function expects X but called with Y"
2. **Type mismatches:** ❌ Can't show data flow "value from line 5 flows to line 10"
3. **Constraint context:** ❌ Can't say "constraint from function application at line 8"
4. **Minimal error sets:** ❌ Can't find "real" error among many failures

### Example: What We're Missing

**Current error (without constraint origins):**
```
error: unsolved metavariable ?0
  origin: underscore placeholder in expression
  blocking: [C5, C7]
```

**Target error (with constraint origins):**
```
error: could not infer type for underscore
  ┌─ foo.hwml:10:15
  │
10│     let x = _ in
  │             ^ type cannot be inferred
  │
  = note: constrained by:
    • C5: function application at line 12 requires Nat
    • C7: return type annotation at line 3 requires Bool
  = error: conflicting constraints: Nat ≠ Bool
  = help: add explicit type annotation
```

**The difference:** Constraint origins tell us WHY constraints exist, not just that they're blocked.

---

## Next Steps: Constraint Origin Implementation

Based on research and our design docs, here's the critical path:

### Step 1: Add `ConstraintOrigin` enum (2-3 hours)

Start with the most common origins:

```rust
#[derive(Debug, Clone)]
pub enum ConstraintOrigin<'db> {
    /// Function application: argument type must match parameter
    FunctionApplication {
        function_span: SourceRange<'db>,
        argument_span: SourceRange<'db>,
        param_index: usize,
    },
    
    /// Return type check: inferred type must match declared type
    ReturnTypeCheck {
        declared_span: SourceRange<'db>,
        returned_span: SourceRange<'db>,
    },
    
    /// Type annotation: expression must have annotated type
    TypeAnnotation {
        annotation_span: SourceRange<'db>,
        expression_span: SourceRange<'db>,
    },
    
    /// Field access on record type
    FieldAccess {
        receiver_span: SourceRange<'db>,
        field_span: SourceRange<'db>,
        field_name: String,
    },
    
    // Add 10-15 more as we encounter them
    Other {
        description: String,
        span: Option<SourceRange<'db>>,
    },
}
```

### Step 2: Add origin fields to `Constraint` and `ConstraintEntry` (1 hour)

```rust
pub struct ConstraintEntry<'db> {
    pub id: ConstraintId,
    pub constraint: Constraint<'db>,
    pub status: ConstraintStatus,

    // NEW: Provenance information
    pub created_at: SourceRange<'db>,
    pub origin: ConstraintOrigin<'db>,
}
```

### Step 3: Update constraint emission APIs (2 hours)

```rust
impl<'db> SolverState<'db> {
    pub fn emit_eq(
        &mut self,
        lhs: RcValue<'db>,
        rhs: RcValue<'db>,
        ty: RcTy<'db>,
        depth: usize,
        // NEW parameters:
        origin: ConstraintOrigin<'db>,
        location: SourceRange<'db>,
    ) -> ConstraintId {
        // ... create constraint with origin
    }
}
```

### Step 4: Migrate call sites (~3-4 hours)

Priority order:
1. `elab::expr::check()` - Type annotation checks (most visible)
2. Function application sites
3. Return type checks
4. Field access constraints
5. Pattern matching

### Step 5: Enhance error rendering (2 hours)

Add constraint origin info to error messages:

```rust
impl<'db> ElabError<'db> {
    pub fn format_with_constraints(&self, state: &SolverState<'db>) -> String {
        match self {
            ElabError::UnsolvedMeta { blocking_constraints, .. } => {
                // Show WHY each constraint was created
                for cid in blocking_constraints {
                    let entry = state.constraint(*cid);
                    msg.push_str(&format!(
                        "\n  • {}: {}",
                        entry.origin.description(),
                        entry.created_at.format()
                    ));
                }
            }
        }
    }
}
```

---

## Comparison: Where We Stand vs. Best Practices

### Metavariable Provenance: ⭐⭐⭐⭐⭐ (5/5)

| Feature | Rust | GHC | Lean 4 | HWML | Status |
|---------|------|-----|--------|------|--------|
| Creation location | ✅ | ✅ | ✅ | ✅ | **Done** |
| Semantic origin | ✅ | ✅ | ✅ | ✅ | **Done** |
| Type information | ✅ | ✅ | ✅ | ✅ | **Done** |
| Parent links | ✅ | ✅ | ✅ | ✅ | **Done** |
| Constraint links | ✅ | ✅ | ✅ | ✅ | **Done** |

**Assessment:** Our meta provenance is **production-quality**.

### Constraint Provenance: ⭐⭐ (2/5)

| Feature | Rust | GHC | Lean 4 | HWML | Status |
|---------|------|-----|--------|------|--------|
| Creation location | ✅ | ✅ | ✅ | ❌ | **Missing** |
| Semantic origin | ✅ | ✅ | ✅ | ❌ | **Missing** |
| Rich origin variants | ✅ | ✅ | ✅ | ❌ | **Missing** |
| Data flow tracking | ✅ | ✅ | Partial | ❌ | **Missing** |
| Multi-span errors | ✅ | ✅ | ✅ | ❌ | **TODO** |

**Assessment:** Major gap. This is Phase 2.5 work we didn't anticipate.

### Error Rendering: ⭐⭐⭐ (3/5)

| Feature | Rust | GHC | Lean 4 | HWML | Status |
|---------|------|-----|--------|------|--------|
| Basic formatting | ✅ | ✅ | ✅ | ✅ | **Done** |
| Provenance chain | ✅ | ✅ | ✅ | ✅ | **Done** |
| Constraint context | ✅ | ✅ | ✅ | ❌ | **Blocked** |
| Multi-span | ✅ | ✅ | ✅ | ❌ | **TODO** |
| Ariadne integration | N/A | N/A | N/A | ❌ | **Phase 4** |

**Assessment:** Good foundation, but blocked on constraint origins.

---

## Recommendations

### Immediate (This Session)

1. ✅ Complete gap analysis (this document)
2. ⚠️ **Create `ConstraintOrigin` enum** - Critical blocker for quality errors
3. ⚠️ **Add origin to `ConstraintEntry`** - Foundation for everything else
4. Update task list to reflect this discovery

### Short-term (Next Session)

1. Migrate `emit_eq` and top 5 call sites
2. Add constraint origin display to errors
3. Test on real examples

### Medium-term (Phase 4)

1. Multi-span error rendering
2. Ariadne integration
3. Error recovery suggestions

---

## Lessons Learned

### What We Got Right

1. **Side-table architecture** - Perfect for keeping meta entries lean
2. **Phased approach** - Each phase delivers value independently
3. **Rich `MetaOrigin` types** - Following Rust/GHC/Lean patterns
4. **Test-driven** - 21 tests give us confidence

### What We Missed

1. **Constraint origins are equally important** - Research was clear, we skipped it
2. **Design docs mentioned it** - Phase 4 in provenance-tracking-design.md, but we jumped ahead
3. **No constraint origin = incomplete errors** - Can't explain WHY constraints failed

### Key Insight

> **Metavariable provenance + Constraint provenance = Complete error story**
>
> - Meta origins answer: "Why does ?42 exist?"
> - Constraint origins answer: "Why must ?42 = Nat?"
> - Together they explain: "?42 must be Nat because it flows into function f at line 10"

---

## Updated Task Priority

### Critical Path (Must Do)

1. [/] Implement `ConstraintOrigin` enum
2. [ ] Add origin to `ConstraintEntry`
3. [ ] Update `emit_eq` API
4. [ ] Migrate top 5 constraint call sites
5. [ ] Display constraint origins in errors

### Lower Priority (Can Defer)

1. Multi-span rendering (needs Ariadne)
2. Error recovery suggestions
3. Performance optimization
4. Full constraint graph analysis

---

## Conclusion

We have **excellent meta provenance** (matching Rust/GHC/Lean quality), but we're **missing constraint provenance** which is equally critical for error quality. This is a 6-8 hour fix that will dramatically improve error messages.

**Next action:** Implement `ConstraintOrigin` enum and update `ConstraintEntry`.

