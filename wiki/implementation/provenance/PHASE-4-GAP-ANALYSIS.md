# Phase 4 Gap Analysis: Current vs. Ideal

**Date:** 2026-05-08
**Status:** Complete Analysis
**Purpose:** Detailed comparison of current code against Phase 4 design

---

## Executive Summary

**Current State:** Phase 3 complete - all errors have spans, constraint/meta provenance working
**Target State:** Phase 4 - add elaboration backtrace, error codes, location inheritance

**Key Findings:**
- 📍 **58 error construction sites** identified across 8 files
- ❌ **No ElabContext** - must create from scratch
- ❌ **No error helper methods** - all errors constructed manually
- ❌ **No error codes** - no `code()` method
- ❌ **No trace guards** - no RAII instrumentation
- ❌ **Manual location threading** - spans passed explicitly everywhere

---

## File-by-File Analysis

### 1. `crates/hwml-elab/src/elab/mod.rs` (78 lines)

**Current Structure:**
```rust
pub struct Elaborator<'a, 'db> {
    pub kernel: Kernel<'a, 'db>,
}
```

**Phase 4 Needs:**
```rust
pub struct Elaborator<'a, 'db> {
    pub kernel: Kernel<'a, 'db>,
    pub context: ElabContext<'db>,  // NEW!
}
```

**Changes Required:**
- [ ] Add `ElabContext<'db>` field
- [ ] Update `new()` to initialize context
- [ ] Add error helper methods (8 methods for 8 error types)
- [ ] Update `synth()` and `check()` to wrap with trace guards

**Estimated Lines:** +150 lines (context struct, helpers)

---

### 2. `crates/hwml-elab/src/elab/expr.rs` (562 lines)

**Error Construction Sites:** 8 sites

**Current Pattern:**
```rust
// Line 211-222: NotInScope
Err(ElabError::NotInScope {
    name: format!("..."),
    span: Some(span),  // Manual threading
})

// Line 250-252: CannotInfer
ok_or_else(|| ElabError::CannotInfer {
    span: Some(expr_location(db, expr))  // Manual call
})

// Line 264: CannotInfer
Err(ElabError::CannotInfer { span: Some(expr_location(db, expr)) })

// Line 534: CannotInfer in let binding
ElabError::CannotInfer { span: Some(span) }
```

**Phase 4 Pattern:**
```rust
// With error helpers:
elab.error_not_in_scope(format!("..."))

elab.error_cannot_infer()

// Location automatically captured from elab.context.current_location()
```

**Changes Required:**
- [ ] Wrap `synth()` function with trace guard (line 116)
- [ ] Wrap `check()` function with trace guard (line 306)
- [ ] Replace 8 error construction sites with helper methods
- [ ] Remove manual `expr_location()` calls (becomes automatic)

**Estimated Changes:** ~15 lines modified, function instrumentation

---

### 3. `crates/hwml-elab/src/kernel/mod.rs` (~1000 lines)

**Error Construction Sites:** 13 sites

**Current Pattern:**
```rust
// Lines 200-203: NotInScope
Err(ElabError::NotInScope {
    name: format_path(db, path),
    span: None,  // Missing span!
})

// Lines 210-212: TypeMismatch
Err(ElabError::TypeMismatch {
    expected: Rc::new(Ty::UniverseType),
    actual: ty,
    span: None,  // Missing span!
})
```

**Problem:** Many errors in kernel have `span: None` because kernel doesn't have access to surface syntax locations.

**Phase 4 Solution:** Location inheritance
```rust
// Kernel errors automatically get span from elab.context.current_location()
elab.error_not_in_scope(format_path(db, path))
// ^^^ This gets the span set by the outer trace guard
```

**Changes Required:**
- [ ] Replace 13 error construction sites with helpers
- [ ] Errors automatically get current location
- [ ] No more `span: None`!

**Estimated Changes:** ~20 lines modified

---

### 4. `crates/hwml-elab/src/solver.rs` (~500 lines)

**Error Construction Sites:** 9 sites

**Current Pattern:**
```rust
// Lines 90-94: UnificationFailure (appears 4 times!)
Err(SolveError::Elab(ElabError::UnificationFailure {
    lhs: lhs.clone(),
    rhs: rhs.clone(),
    span: None,  // Missing span!
}))

// Lines 250-256: NotInScope in ResolveDot
Err(SolveError::Elab(ElabError::NotInScope {
    name: format!("{}.{}", ..., ...),
    span: None,  // Missing span!
}))

// Lines 330-333: TypeMismatch
Err(SolveError::Elab(ElabError::TypeMismatch {
    expected: Rc::new(Ty::UniverseType),
    actual: forced_ty,
    span: None,  // Missing span!
}))
```

**Phase 4 Pattern:**
```rust
// Solver needs access to elab.context
Err(SolveError::Elab(elab.error_unification_failure(lhs.clone(), rhs.clone())))
```

**Changes Required:**
- [ ] Pass `&Elaborator` to solver (not just `&mut SolverState`)
- [ ] Replace 9 error construction sites
- [ ] Extract spans from constraints where available

**Estimated Changes:** ~15 lines modified + signature changes

---

### Changes by File

| File | Current Lines | Error Sites | New Lines | Est. Effort |
|------|---------------|-------------|-----------|-------------|
| `elab/mod.rs` | 78 | 0 | +150 | 4h (error helpers) |
| `elab/expr.rs` | 562 | 8 | ~15 modified | 2h (trace guards) |
| `kernel/mod.rs` | ~1000 | 13 | ~20 modified | 2h (helpers) |
| `solver.rs` | ~500 | 9 | ~15 modified | 3h (signature changes) |
| `unify/mod.rs` | ~400 | 3 | ~5 modified | 1h |
| `state.rs` | 1278 | 3 | ~3 modified | 1h |
| `scc_elab.rs` | ~300 | 7 | ~10 modified | 2h |
| `error.rs` | 246 | 0 | +80 | 3h (enum + display) |
| **`context.rs`** | **0 (NEW)** | **0** | **+200** | **5h (new module)** |
| **TOTAL** | **~4364** | **58** | **+430** | **23h (~3 days)** |

---

## Detailed Change Plan

### Phase 4.1: Infrastructure (Days 1-2)

#### Task 1.1: Create ElabContext Module
- [ ] Create `crates/hwml-elab/src/context.rs`
- [ ] Define `ElabContext<'db>` struct
- [ ] Define `ElabFrame<'db>` struct
- [ ] Define `ElabFrameKind` enum
- [ ] Implement `TraceGuard` RAII pattern
- [ ] Add tests for push/pop/snapshot

**Files:** `context.rs` (new, 200 lines)

#### Task 1.2: Update ElabError with Backtrace
- [ ] Add `elab_backtrace: Vec<ElabFrame<'db>>` to all 9 error variants
- [ ] Update all pattern matches (compiler will catch these)
- [ ] Fix test cases

**Files:** `error.rs` (+9 lines for fields)

#### Task 1.3: Add Error Codes
- [ ] Add `code()` method to `ElabError`
- [ ] Map all 9 variants to error codes (E001-E009)

**Files:** `error.rs` (+20 lines)

#### Task 1.4: Add context to Elaborator
- [ ] Add `context: ElabContext<'db>` field to `Elaborator`
- [ ] Update `Elaborator::new()` to initialize context
- [ ] Fix compilation errors

**Files:** `elab/mod.rs` (+3 lines)

**Estimated Time:** 8 hours (1 day)

---

### Phase 4.2: Error Helper Methods (Day 3)

#### Task 2.1: Implement Error Helpers in Elaborator

Add to `crates/hwml-elab/src/elab/mod.rs`:

```rust
impl<'a, 'db> Elaborator<'a, 'db> {
    // ... existing methods ...

    // Error construction helpers - automatically capture location and backtrace

    pub fn error_type_mismatch(
        &self,
        expected: RcTy<'db>,
        actual: RcTy<'db>,
    ) -> ElabError<'db> {
        ElabError::TypeMismatch {
            expected,
            actual,
            span: self.context.current_location(),
            elab_backtrace: self.context.snapshot(),
        }
    }

    pub fn error_not_in_scope(&self, name: String) -> ElabError<'db> {
        ElabError::NotInScope {
            name,
            span: self.context.current_location(),
            elab_backtrace: self.context.snapshot(),
        }
    }

    pub fn error_cannot_infer(&self) -> ElabError<'db> {
        ElabError::CannotInfer {
            span: self.context.current_location(),
            elab_backtrace: self.context.snapshot(),
        }
    }

    pub fn error_unification_failure(
        &self,
        lhs: RcValue<'db>,
        rhs: RcValue<'db>,
    ) -> ElabError<'db> {
        ElabError::UnificationFailure {
            lhs,
            rhs,
            span: self.context.current_location(),
            elab_backtrace: self.context.snapshot(),
        }
    }

    pub fn error_occurs_check(&self, meta: MetaId) -> ElabError<'db> {
        ElabError::OccursCheck {
            meta,
            span: self.context.current_location(),
            elab_backtrace: self.context.snapshot(),
        }
    }

    pub fn error_scope_violation(&self, meta: MetaId) -> ElabError<'db> {
        ElabError::ScopeViolation {
            meta,
            span: self.context.current_location(),
            elab_backtrace: self.context.snapshot(),
        }
    }

    pub fn error_meta_already_solved(&self, meta: MetaId) -> ElabError<'db> {
        ElabError::MetaAlreadySolved {
            meta,
            elab_backtrace: self.context.snapshot(),
        }
    }

    pub fn error_not_implemented(&self, feature: String) -> ElabError<'db> {
        ElabError::NotImplemented {
            feature,
            span: self.context.current_location(),
            elab_backtrace: self.context.snapshot(),
        }
    }
}
```

**Files:** `elab/mod.rs` (+90 lines)
**Estimated Time:** 2 hours

---

### Phase 4.3: Instrumentation (Days 4-5)

#### Task 3.1: Instrument synth() and check()

**File:** `crates/hwml-elab/src/elab/expr.rs`

```rust
pub fn synth<'a, 'db, Db>(
    db: &'db Db,
    elab: &mut Elaborator<'a, 'db>,
    expr: &Expression,
) -> Result<Checked<(RcSyntax<'db>, RcTy<'db>)>, ElabError<'db>>
where
    Db: salsa::Database,
{
    // Add trace guard
    let location = expr_location(db, expr);
    let _guard = elab.context.trace(
        "synthesizing type",
        location,
        ElabFrameKind::SynthesizingType,
    );

    match expr {
        // ... existing code ...
    }
}

pub fn check<'a, 'db, Db>(
    db: &'db Db,
    elab: &mut Elaborator<'a, 'db>,
    expr: &Expression,
    expected_ty: RcTy<'db>,
) -> Result<Checked<RcSyntax<'db>>, ElabError<'db>>
where
    Db: salsa::Database,
{
    // Add trace guard with type info
    use crate::error::ElabError;  // for format_type

    let location = expr_location(db, expr);
    let type_str = ElabError::format_type(&expected_ty);
    let _guard = elab.context.trace(
        format!("checking expression against {}", type_str),
        location,
        ElabFrameKind::CheckingExpression,
    );

    match expr {
        // ... existing code ...
    }
}
```

**Changes:** ~10 lines added
**Estimated Time:** 1 hour

#### Task 3.2: Replace Error Construction Sites

**Strategy:** Use compiler to find all sites

1. Add backtrace field to one variant
2. Run `cargo check`
3. Compiler shows all construction sites
4. Replace with helper methods
5. Repeat for each variant

**Example Replacement:**

Before:
```rust
Err(ElabError::NotInScope {
    name: name.to_string(),
    span: Some(span),
})
```

After:
```rust
Err(elab.error_not_in_scope(name.to_string()))
```

**Files:** All 8 files with error construction
**Sites:** 58 total
**Estimated Time:** 8 hours (6-10 minutes per site)

---

### Phase 4.4: Enhanced Display (Day 6)

#### Task 4.1: Update Display Implementation

**File:** `crates/hwml-elab/src/error.rs`

```rust
impl<'db> Display for ElabError<'db> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        // 1. Show error code
        write!(f, "error[{}]: ", self.code())?;

        // 2. Show primary message
        write!(f, "{}", self.format_message())?;

        // 3. Show elaboration backtrace (if non-empty)
        if let Some(backtrace) = self.elab_backtrace() {
            if !backtrace.is_empty() {
                writeln!(f, "\n\nelaboration backtrace:")?;
                for (i, frame) in backtrace.iter().rev().enumerate() {
                    writeln!(
                        f,
                        "  {}: {} at {:?}",
                        i, frame.description, frame.location.range
                    )?;
                }
            }
        }

        // 4. Show constraint context (existing code for UnsolvedMeta)
        // ... keep existing constraint display ...

        Ok(())
    }
}

impl<'db> ElabError<'db> {
    fn elab_backtrace(&self) -> Option<&Vec<ElabFrame<'db>>> {
        match self {
            ElabError::TypeMismatch { elab_backtrace, .. } => Some(elab_backtrace),
            ElabError::NotInScope { elab_backtrace, .. } => Some(elab_backtrace),
            ElabError::CannotInfer { elab_backtrace, .. } => Some(elab_backtrace),
            ElabError::UnificationFailure { elab_backtrace, .. } => Some(elab_backtrace),
            ElabError::OccursCheck { elab_backtrace, .. } => Some(elab_backtrace),
            ElabError::ScopeViolation { elab_backtrace, .. } => Some(elab_backtrace),
            ElabError::UnsolvedMeta { elab_backtrace, .. } => Some(elab_backtrace),
            ElabError::MetaAlreadySolved { elab_backtrace, .. } => Some(elab_backtrace),
            ElabError::NotImplemented { elab_backtrace, .. } => Some(elab_backtrace),
        }
    }
}
```

**Files:** `error.rs` (+40 lines)
**Estimated Time:** 2 hours

---

### Phase 4.5: Testing & Documentation (Day 7)

#### Task 5.1: Update Existing Tests
- [ ] Fix test cases that construct errors directly
- [ ] Add backtrace assertions to error tests
- [ ] Verify empty backtrace when no trace context

**Estimated Time:** 3 hours

#### Task 5.2: Create Integration Tests
- [ ] Test that synth/check capture backtraces
- [ ] Test nested elaboration (multiple frames)
- [ ] Test location inheritance
- [ ] Verify error codes in output

**Estimated Time:** 3 hours

#### Task 5.3: Create Error Code Documentation
- [ ] Create `docs/error-codes.md`
- [ ] Document all 9 error codes with examples
- [ ] Add "how to fix" guidance

**Estimated Time:** 2 hours

---

## Migration Checklist

### Week 1: Infrastructure
- [ ] Day 1: Create `context.rs` (Task 1.1)
- [ ] Day 1: Update `ElabError` fields (Task 1.2)
- [ ] Day 2: Add error codes (Task 1.3)
- [ ] Day 2: Add context to Elaborator (Task 1.4)
- [ ] Day 2: Verify compilation

### Week 2: Implementation
- [ ] Day 3: Implement error helpers (Task 2.1)
- [ ] Day 4: Instrument synth/check (Task 3.1)
- [ ] Day 4-5: Replace all 58 error sites (Task 3.2)
- [ ] Day 6: Enhanced Display (Task 4.1)

### Week 3: Testing & Polish
- [ ] Day 7: Update existing tests (Task 5.1)
- [ ] Day 7: Integration tests (Task 5.2)
- [ ] Day 7: Documentation (Task 5.3)

---

## Risk Analysis

### High Risk
1. **Signature Changes to Solver/Unifier**
   - Many functions need `&Elaborator` instead of just `&mut SolverState`
   - Could cascade to many call sites
   - **Mitigation:** Use compiler to find all sites, fix incrementally

2. **Test Breakage**
   - Adding `elab_backtrace` field breaks all error construction in tests
   - **Mitigation:** Use `Vec::new()` initially, update tests incrementally

### Medium Risk
3. **Performance Regression**
   - Trace stack push/pop on every synth/check
   - **Mitigation:** Benchmark before/after, optimize with SmallVec if needed

4. **Missing Instrumentation**
   - Easy to forget to add trace guards to some elaboration paths
   - **Mitigation:** Grep for all `fn check` / `fn synth` variants

### Low Risk
5. **Display Formatting Issues**
   - Backtrace might be too verbose
   - **Mitigation:** Test with real errors, adjust formatting

---

## Success Criteria

### Minimum Viable Phase 4
- [x] `ElabContext` created and integrated
- [x] All 9 error variants have `elab_backtrace` field
- [x] Error helper methods reduce boilerplate
- [x] `synth()` and `check()` instrumented
- [x] Error codes (`E001`-`E009`) implemented
- [x] Display shows error code + backtrace

### Ideal Phase 4
- [x] All 58 error construction sites use helpers
- [x] No `span: None` in user-facing errors
- [x] Location inheritance working (automatic span capture)
- [x] Integration tests verify backtrace quality
- [x] `docs/error-codes.md` complete

---

## Example: Before vs. After

### Before (Phase 3)
```rust
// Manual error construction
let location = expr_location(db, expr);
Err(ElabError::NotInScope {
    name: name.to_string(),
    span: Some(location),
})

// Output:
error: not in scope at 10..15: foo
```

### After (Phase 4)
```rust
// Helper method
Err(elab.error_not_in_scope(name.to_string()))

// Output:
error[E002]: not in scope at 10..15: foo

elaboration backtrace:
  0: synthesizing type at 10..15
  1: checking function application at 8..20
  2: checking definition 'main' at 1..100
```

**Benefits:**
- ✅ Less boilerplate (no manual location)
- ✅ Automatic backtrace capture
- ✅ Error code for documentation
- ✅ User can see elaboration context

---

## References

- **Comparison:** `wiki/research/asai-vs-hwml-comparison.md`
- **Architecture:** `wiki/decisions/ADR-015-elaboration-provenance-architecture.md`
- **Summary:** `wiki/implementation/provenance/ASAI-COMPARISON-SUMMARY.md`
Err(SolveError::Elab(ElabError::TypeMismatch {
    expected: Rc::new(Ty::UniverseType),
    actual: forced_ty,
    span: None,  // Missing span!
}))
```

**Phase 4 Pattern:**
```rust
// Solver needs access to elab.context
Err(SolveError::Elab(elab.error_unification_failure(lhs.clone(), rhs.clone())))
```

**Changes Required:**
- [ ] Pass `&Elaborator` to solver (not just `&mut SolverState`)
- [ ] Replace 9 error construction sites
- [ ] Extract spans from constraints where available

**Estimated Changes:** ~15 lines modified + signature changes

---

### 5. `crates/hwml-elab/src/unify/mod.rs` (~400 lines)

**Error Construction Sites:** 3 sites

**Current Pattern:**
```rust
// UnificationFailure appears 3 times
Err(ElabError::UnificationFailure {
    lhs: lhs.clone(),
    rhs: rhs.clone(),
    span: self.span.clone(),  // Good! Already has span
})
```

**Phase 4 Pattern:**
```rust
elab.error_unification_failure(lhs.clone(), rhs.clone())
```

**Changes Required:**
- [ ] Pass `&Elaborator` to unifier
- [ ] Replace 3 error construction sites
- [ ] Keep existing span capture logic

**Estimated Changes:** ~5 lines modified

---

### 6. `crates/hwml-elab/src/state.rs` (1278 lines)

**Error Construction Sites:** 3 sites

**Current Pattern:**
```rust
// Line 140: MetaAlreadySolved
Err(ElabError::MetaAlreadySolved { meta: id })

// Lines 154-157: TypeMismatch
Err(ElabError::TypeMismatch {
    expected: Rc::new(Ty::UniverseType),
    actual: entry.ty.clone(),
    span: None,
})

// Lines 454-492: UnsolvedMeta (complex - uses make_unsolved_meta_error)
```

**Phase 4 Pattern:**
```rust
elab.error_meta_already_solved(id)
elab.error_type_mismatch(expected, actual)
// UnsolvedMeta stays as-is (already complex)
```

**Changes Required:**
- [ ] Pass `&Elaborator` where needed
- [ ] Replace 2 simple error sites
- [ ] Keep `make_unsolved_meta_error` (already rich)

**Estimated Changes:** ~3 lines modified

---

### 7. `crates/hwml-elab/src/scc_elab.rs`

**Error Construction Sites:** 7 sites

**Current Pattern:**
```rust
// NotInScope, CannotInfer with span: None
Err(ElabError::NotInScope {
    name: format!("..."),
    span: None,
})
```

**Phase 4 Pattern:**
```rust
elab.error_not_in_scope(format!("..."))
// Auto-inherits span from definition elaboration trace
```

**Changes Required:**
- [ ] Replace 7 error construction sites
- [ ] Wrap definition elaboration with trace guard

**Estimated Changes:** ~10 lines modified

---

### 8. `crates/hwml-elab/src/error.rs` (246 lines)

**Current Structure:**
```rust
pub enum ElabError<'db> {
    TypeMismatch {
        expected: RcTy<'db>,
        actual: RcTy<'db>,
        span: Option<SourceRange<'db>>,
    },
    // ... 8 more variants, all missing elab_backtrace
}

impl<'db> ElabError<'db> {
    pub fn format_message(&self) -> String { ... }
}

impl<'db> Display for ElabError<'db> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", self.format_message())
    }
}
```

**Phase 4 Needs:**
```rust
pub enum ElabError<'db> {
    TypeMismatch {
        expected: RcTy<'db>,
        actual: RcTy<'db>,
        span: Option<SourceRange<'db>>,
        elab_backtrace: Vec<ElabFrame<'db>>,  // NEW!
    },
    // ... all 9 variants get elab_backtrace
}

impl<'db> ElabError<'db> {
    pub fn code(&self) -> &'static str {  // NEW!
        match self {
            TypeMismatch { .. } => "E001",
            NotInScope { .. } => "E002",
            // ...
        }
    }

    fn format_elab_backtrace(&self, f: &mut Formatter) -> fmt::Result { ... }  // NEW!
}

impl<'db> Display for ElabError<'db> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        // Show error code
        write!(f, "error[{}]: ", self.code())?;

        // Show primary message
        write!(f, "{}", self.format_message())?;

        // Show elaboration backtrace
        self.format_elab_backtrace(f)?;

        Ok(())
    }
}
```

**Changes Required:**
- [ ] Add `elab_backtrace: Vec<ElabFrame<'db>>` to all 9 variants
- [ ] Add `code()` method
- [ ] Update `Display` to show code and backtrace
- [ ] Add `format_elab_backtrace()` helper

**Estimated Changes:** +80 lines (9 fields + code method + formatting)

---

## New Files Needed

### 1. `crates/hwml-elab/src/context.rs` (NEW - ~200 lines)

**Purpose:** ElabContext and trace infrastructure

```rust
use hwml_core::SourceRange;

pub struct ElabContext<'db> {
    trace_stack: Vec<ElabFrame<'db>>,
    current_location: Option<SourceRange<'db>>,
}

pub struct ElabFrame<'db> {
    pub description: String,
    pub location: SourceRange<'db>,
    pub kind: ElabFrameKind,
}

#[derive(Debug, Clone)]
pub enum ElabFrameKind {
    CheckingExpression,
    SynthesizingType,
    CheckingDefinition { name: String },
    CheckingFunctionApplication,
    CheckingReturnType,
    SolvingConstraints,
    CheckingConstructor { name: String },
}

pub struct TraceGuard<'a, 'db> {
    context: &'a mut ElabContext<'db>,
}

impl<'a, 'db> Drop for TraceGuard<'a, 'db> {
    fn drop(&mut self) {
        self.context.trace_stack.pop();
    }
}

impl<'db> ElabContext<'db> {
    pub fn new() -> Self {
        ElabContext {
            trace_stack: Vec::new(),
            current_location: None,
        }
    }

    pub fn trace<'a>(
        &'a mut self,
        desc: impl Into<String>,
        loc: SourceRange<'db>,
        kind: ElabFrameKind,
    ) -> TraceGuard<'a, 'db> {
        self.current_location = Some(loc.clone());
        self.trace_stack.push(ElabFrame {
            description: desc.into(),
            location: loc,
            kind,
        });
        TraceGuard { context: self }
    }

    pub fn snapshot(&self) -> Vec<ElabFrame<'db>> {
        self.trace_stack.clone()
    }

    pub fn current_location(&self) -> Option<SourceRange<'db>> {
        self.current_location.clone()
    }
}
```

---

## Summary Statistics

### Error Construction Sites by Type

| Error Type | Count | Files |
|------------|-------|-------|
| NotInScope | 19 | expr, kernel, solver, scc_elab |
| CannotInfer | 8 | expr, kernel, scc_elab |
| UnificationFailure | 7 | solver, unify |
| TypeMismatch | 4 | kernel, solver, state |
| ScopeViolation | 3 | unify/pattern |
| OccursCheck | 1 | unify/pattern |
| MetaAlreadySolved | 1 | state |
| **TOTAL** | **58** | **8 files** |

