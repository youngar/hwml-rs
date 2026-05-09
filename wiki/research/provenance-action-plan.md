# HWML Provenance Tracking: Concrete Action Plan

**Date:** 2026-05-06  
**Based on:** [[provenance-deep-dive]], [[provenance-implementation-examples]]  
**Status:** Ready for Implementation

---

## Executive Summary

After comprehensive research into Lean 4, Agda, GHC, Idris 2, and the RedPRL lineage, we have identified **provenance tracking as essential error reporting infrastructure**, not optional debug information.

**Key Finding:** All production-quality dependently typed elaborators track:
1. WHERE each metavariable was created (source location)
2. WHY it was created (implicit arg, type inference, etc.)  
3. WHICH constraints involve it
4. HOW it relates to user code

**Current HWML Gap:** Zero provenance tracking → poor error messages

**Estimated Implementation:** 4-6 weeks for full provenance + rich diagnostics

---

## The Problem: Current HWML Error Quality

### Current Error (Unusable)
```
error: unsolved metavariable ?42
```

### What Users Need (Actionable)
```
error: unsolved metavariable ?42
  ┌─ Counter.hwml:15:10
  │
12│ def increment (state : BitVec 8) : BitVec 8 :=
  │                        ───────── 'state' has type BitVec 8
13│   let next = state + 1 in
14│   if next > 255 then
15│     wrap_around next
  │                 ^^^^ metavariable ?42 created here
  │                      (implicit type argument for 'wrap_around')
  │
  = note: constrained by:
  = note:   constraint #23: ?42 ≡ Nat (from 'wrap_around' signature)
  = note:   constraint #47: ?42 ≡ BitVec 8 (from argument type)
  = error: conflict: Nat ≠ BitVec 8
  = help: add explicit type annotation or change 'wrap_around' signature
```

**Difference:** The second error is **actionable**. The user knows exactly what to fix.

---

## Implementation Phases

### Phase 1: Minimal Provenance (Week 1)
**Goal:** Track creation location and simple origin for every metavariable

**Changes:**

```rust
// crates/hwml-elab/src/meta.rs
#[derive(Debug, Clone)]
pub struct MetaEntry<'db> {
    pub id: MetaId,
    pub ty: RcTy<'db>,
    pub arity: usize,
    pub solution: Option<MetaSolution<'db>>,
    pub kind: MetaKind,
    
    // NEW: Minimal provenance
    pub created_at: Location<'db>,
    pub origin: String,  // Simple description for MVP
}

// crates/hwml-elab/src/state.rs
impl<'db> SolverState<'db> {
    pub fn fresh_meta(
        &mut self,
        ty: RcTy<'db>,
        arity: usize,
        kind: MetaKind,
        created_at: Location<'db>,
        origin: String,
    ) -> MetaId {
        let id = MetaId(self.next_meta);
        self.next_meta += 1;
        let entry = MetaEntry {
            id,
            ty,
            arity,
            solution: None,
            kind,
            created_at,
            origin,
        };
        self.metas.insert(id, entry);
        id
    }
}
```

**Action Items:**
- [ ] Add `created_at` and `origin` fields to `MetaEntry`
- [ ] Update `fresh_meta()` signature in `SolverState`
- [ ] Update ALL `fresh_meta()` call sites (~30 locations) to provide origin
- [ ] Update `ElabError::UnsolvedMeta` to include provenance

**Estimated Effort:** 8-12 hours

---

### Phase 2: Typed Origins (Week 2)
**Goal:** Replace `String` origins with typed enum for structured errors

```rust
// crates/hwml-elab/src/meta.rs
#[derive(Clone, Debug)]
pub enum MetaOrigin<'db> {
    ImplicitArgument {
        function_loc: Location<'db>,
        param_name: String,
        param_index: usize,
    },
    TypeInference {
        expression_loc: Location<'db>,
        reason: String,
    },
    UniverseLevel {
        type_annotation_loc: Location<'db>,
    },
    UnificationVariable {
        constraint_loc: Location<'db>,
    },
    PatternSynthesis {
        pattern_loc: Location<'db>,
        constructor: String,
    },
    Hole {
        hole_loc: Location<'db>,
    },
    Other(String),  // Fallback
}

pub struct MetaEntry<'db> {
    // ...
    pub created_by: MetaOrigin<'db>,  // Replaces `origin: String`
}
```

**Action Items:**
- [ ] Define `MetaOrigin<'db>` enum
- [ ] Update `MetaEntry` to use `MetaOrigin`
- [ ] Update call sites to use typed origins
- [ ] Implement `Display` for rich error messages

**Estimated Effort:** 12-16 hours

---

### Phase 3: Constraint Provenance (Week 3)
**Goal:** Track WHERE and WHY each constraint was created

```rust
// crates/hwml-elab/src/constraint.rs
#[derive(Clone, Debug)]
pub enum ConstraintOrigin<'db> {
    FunctionApplication {
        function_loc: Location<'db>,
        argument_loc: Location<'db>,
    },
    TypeAnnotation {
        term_loc: Location<'db>,
        annotation_loc: Location<'db>,
    },
    PatternMatching {
        scrutinee_loc: Location<'db>,
        pattern_loc: Location<'db>,
        branch_index: usize,
    },
    UnificationDecomposition {
        parent_constraint: ConstraintId,
        rule: &'static str,  // "Pi injectivity", "pair congruence"
    },
    // ... 10+ more variants
}

#[derive(Debug, Clone)]
pub struct ConstraintEntry<'db> {
    pub id: ConstraintId,
    pub constraint: Constraint<'db>,
    pub status: ConstraintStatus,
    
    // NEW: Provenance
    pub created_at: Location<'db>,
    pub origin: ConstraintOrigin<'db>,
}
```

**Action Items:**
- [ ] Define `ConstraintOrigin<'db>` enum
- [ ] Add `created_at` and `origin` to `ConstraintEntry`
- [ ] Update `emit_eq()`, `emit_level_leq()`, etc. to accept origin
- [ ] Update all constraint creation sites

**Estimated Effort:** 16-20 hours

---

### Phase 4: Blocking Reason Tracking (Week 3 cont.)
**Goal:** Track WHY constraints are blocked

```rust
#[derive(Debug, Clone)]
pub enum BlockingReason<'db> {
    WaitingForMeta {
        meta: MetaId,
        reason: String,
    },
    NotPatternFragment {
        meta: MetaId,
        problematic_args: Vec<usize>,
    },
    RecursiveOccurrence {
        meta: MetaId,
        occurs_in: RcValue<'db>,
    },
}

pub struct ConstraintEntry<'db> {
    // ...
    pub blocking_reason: Option<BlockingReason<'db>>,
}
```

**Action Items:**
- [ ] Define `BlockingReason<'db>` enum
- [ ] Add to `ConstraintEntry`
- [ ] Set reason when calling `block_on()`
- [ ] Use in error messages

**Estimated Effort:** 8 hours

---

### Phase 5: Rich Multi-Span Diagnostics (Week 4)
**Goal:** Rust/Elm-style error rendering with multiple highlighted spans

**Add dependency:**
```toml
# crates/hwml-elab/Cargo.toml
[dependencies]
ariadne = "0.6"
```

**Create diagnostics module:**
```rust
// crates/hwml-elab/src/diagnostics.rs

use ariadne::{Label, Report, ReportKind, Source};

pub fn render_unsolved_meta_error<'db>(
    db: &'db dyn salsa::Database,
    meta_id: MetaId,
    entry: &MetaEntry<'db>,
    constraints: &[ConstraintInfo<'db>],
) -> String {
    let mut report = Report::build(ReportKind::Error, entry.created_at.file(), 0)
        .with_message(format!("unsolved metavariable ?{}", meta_id.0));
    
    // Primary label: where meta was created
    report = report.with_label(
        Label::new((entry.created_at.file(), entry.created_at.range()))
            .with_message(format!("metavariable ?{} created here", meta_id.0))
            .with_color(ariadne::Color::Red)
    );
    
    // Secondary labels: related locations
    match &entry.created_by {
        MetaOrigin::ImplicitArgument { function_loc, param_name, .. } => {
            report = report.with_label(
                Label::new((function_loc.file(), function_loc.range()))
                    .with_message(format!("implicit argument '{}' for this function", param_name))
                    .with_color(ariadne::Color::Blue)
            );
        }
        // ... other cases
    }
    
    // Constraint notes
    for c in constraints {
        report = report.with_note(format!("constraint: {}", c.kind));
    }
    
    // Render to string
    let mut output = Vec::new();
    report.finish().write(cache, &mut output).unwrap();
    String::from_utf8(output).unwrap()
}
```

**Action Items:**
- [ ] Add `ariadne` dependency
- [ ] Create `diagnostics.rs` module
- [ ] Implement rendering for each `ElabError` variant
- [ ] Update error display to use new rendering
- [ ] Add tests for error output

**Estimated Effort:** 16-24 hours

---

## Priority Order (What to Do First)

### Critical Path (Enables Actionable Errors)

1. **Phase 1: Minimal Provenance** ⭐⭐⭐⭐⭐
   - **Why first:** Immediately improves error messages
   - **Effort:** 8-12 hours
   - **Impact:** Users can see WHERE metas were created

2. **Phase 2: Typed Origins** ⭐⭐⭐⭐
   - **Why second:** Enables structured error messages
   - **Effort:** 12-16 hours
   - **Impact:** Users understand WHY metas exist

3. **Phase 5: Rich Diagnostics** ⭐⭐⭐⭐
   - **Why third:** Makes errors beautiful and actionable
   - **Effort:** 16-24 hours
   - **Impact:** Rust-quality error messages

### Secondary (Improves Constraint Solver Debugging)

4. **Phase 3: Constraint Provenance** ⭐⭐⭐
   - **Effort:** 16-20 hours
   - **Impact:** Better constraint conflict diagnosis

5. **Phase 4: Blocking Reasons** ⭐⭐
   - **Effort:** 8 hours
   - **Impact:** "Stuck on" messages

---

## Migration Strategy

### Step 1: Add Fields Without Breaking Changes

```rust
// OLD (current):
pub struct MetaEntry<'db> {
    pub id: MetaId,
    pub ty: RcTy<'db>,
    // ...
}

// NEW (backward compatible with defaults):
pub struct MetaEntry<'db> {
    pub id: MetaId,
    pub ty: RcTy<'db>,
    // ...
    pub created_at: Location<'db>,  // NEW
    pub origin: String,             // NEW
}

impl<'db> MetaEntry<'db> {
    pub fn new_legacy(id: MetaId, ty: RcTy<'db>, arity: usize, kind: MetaKind) -> Self {
        MetaEntry {
            id,
            ty,
            arity,
            solution: None,
            kind,
            created_at: Location::synthetic(/* "unknown" */),
            origin: "unknown".to_string(),
        }
    }
}
```

### Step 2: Gradual Migration of Call Sites

**Pattern:** Update one module at a time, starting with most common errors

1. Start with `elab/expr.rs` (expression elaboration)
2. Then `elab/decl.rs` (declaration elaboration)
3. Then `unify/mod.rs` (unification)
4. Finally `solver.rs` (constraint solving)

**Testing:** After each module, run test suite to ensure no regressions

---

## Success Criteria

### Phase 1 Success (Week 1)
- [ ] All `fresh_meta()` calls provide location and origin
- [ ] `ElabError::UnsolvedMeta` displays location
- [ ] Test suite passes with new fields

### Phase 2 Success (Week 2)
- [ ] All origins are typed (no more raw strings)
- [ ] Error messages show different text per origin type
- [ ] At least 5 distinct origin types used

### Phase 3-4 Success (Week 3)
- [ ] All constraints have provenance
- [ ] Blocking constraints show "stuck on" information
- [ ] Constraint errors show creation location

### Phase 5 Success (Week 4)
- [ ] Multi-span error rendering works
- [ ] Errors show 2+ related locations
- [ ] Color output in terminal
- [ ] Error quality matches Rust/Elm

---

## Long-Term Vision (Beyond 6 Weeks)

### LSP Integration (Months 2-3)

Following Lean 4's InfoTree architecture:

```rust
// InfoTree: spatial mapping of elaboration state
pub struct InfoTree<'db> {
    root: InfoNode<'db>,
    assignments: HashMap<MVarId, InfoTree<'db>>,
}

pub enum InfoNode<'db> {
    Context(PartialContextInfo<'db>, Box<InfoTree<'db>>),
    Node(Info<'db>, Vec<InfoTree<'db>>),
    Hole(MetaId),
}

pub struct Info<'db> {
    span: SourceRange<'db>,
    syntax: RcSyntax<'db>,
    expr: Option<RcValue<'db>>,
    expected_type: Option<RcTy<'db>>,
    mctx_snapshot: MetavarContextSnapshot<'db>,
}
```

**Custom LSP endpoints:**
- `$/hwml/goalState` - Get current proof state at cursor
- `$/hwml/metaInfo` - Query metavariable details
- `$/hwml/constraintInfo` - Query constraint status

**Editor support:**
- VSCode extension (primary)
- Neovim plugin (via custom RPC)
- Emacs mode (via custom RPC)

---

## Testing Strategy

### Unit Tests

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_meta_provenance_preserved() {
        let db = &mut TestDatabase::new();
        let loc = Location::synthetic(db, "test_meta");
        let origin = MetaOrigin::ImplicitArgument {
            function_loc: loc.clone(),
            param_name: "n".to_string(),
            param_index: 0,
        };

        let mut state = SolverState::new();
        let meta_id = state.fresh_meta(
            Rc::new(Ty::UniverseType),
            0,
            MetaKind::Term,
            loc.clone(),
            origin.clone(),
        );

        let entry = state.meta_entry(meta_id).unwrap();
        assert_eq!(entry.created_at, loc);
        match &entry.created_by {
            MetaOrigin::ImplicitArgument { param_name, .. } => {
                assert_eq!(param_name, "n");
            }
            _ => panic!("wrong origin type"),
        }
    }
}
```

### Integration Tests

Create example files with known errors:

```hwml
-- test/error-cases/unsolved-implicit.hwml
def replicate {n : Nat} (x : A) : Vec A n :=
  cons x (replicate x)  -- Should error: cannot infer 'n'
```

Expected error:
```
error: unsolved metavariable ?n
  ┌─ test/error-cases/unsolved-implicit.hwml:2:11
  │
1 │ def replicate {n : Nat} (x : A) : Vec A n :=
  │                ─────── implicit parameter 'n'
2 │   cons x (replicate x)
  │           ^^^^^^^^^^^ metavariable ?n created here
  │                       (implicit argument for 'replicate')
  │
  = help: add explicit argument: replicate {n = ?} x
```

---

## Resources and References

### Must-Read Papers

1. **Gundry (2013):** "Type Inference, Haskell and Dependent Types" - Dynamic pattern unification
2. **Sterling & Harper (2018):** "Algebraic Foundations of Proof Refinement" - Provenance as derivation

### Implementation References

- **Lean 4:** `src/Lean/MetavarContext.lean`, `src/Lean/Elab/InfoTree/`
- **Agda:** `src/full/Agda/TypeChecking/MetaVars.hs`
- **GHC:** `compiler/GHC/Tc/Zonk/`, `compiler/GHC/Tc/Types/Constraint.hs`

### Tools

- **ariadne:** https://docs.rs/ariadne/ (error rendering)
- **miette:** https://docs.rs/miette/ (alternative to ariadne)
- **codespan-reporting:** https://docs.rs/codespan-reporting/ (LSP diagnostics)

---

## Conclusion

Provenance tracking is **not optional**—it's the foundation of usable error messages in dependently typed languages.

**Total Estimated Effort:** 4-6 weeks for full implementation

**Immediate Next Step:** Start Phase 1 (Minimal Provenance) TODAY

**Expected Impact:**
- Error message quality: ⭐ → ⭐⭐⭐⭐
- User debugging time: -70%
- Issue reports about "confusing errors": -90%

---

**Action:** Begin implementation with Phase 1 (add `created_at` and `origin` to `MetaEntry`)

