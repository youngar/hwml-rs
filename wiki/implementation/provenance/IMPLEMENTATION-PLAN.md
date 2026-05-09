# Provenance Tracking Implementation Plan

**Date**: 2026-05-07  
**Target**: Transform `error: unsolved metavariable ?42` into actionable diagnostics  
**Based on**: [RedPRL research](../../research/redprl-provenance.md), [Provenance Action Plan](../../research/provenance-action-plan.md)

---

## Executive Summary

This plan implements provenance tracking for HWML's elaborator to produce high-quality error messages. The implementation is phased to maintain stability while progressively improving error diagnostics.

**Current State**:
- `MetaEntry` has: `id`, `ty`, `arity`, `solution`, `kind`
- `ConstraintEntry` has: `id`, `constraint`, `status`
- Errors show: `error: unsolved metavariable ?42 (span: None)`

**Target State (Phase 5)**:
```
error: unsolved metavariable ?0
  ┌─ src/example.hwml:12:15
  │
12│     let result = compute _ in
  │                          ^ type cannot be inferred
  │
  = note: metavariable created for underscore type placeholder
  = help: provide an explicit type annotation
  = constrained by:
    • function application at src/example.hwml:15:8
    • return type must match 'Nat' at src/example.hwml:3:25
```

---

## Architecture Overview

### Core Principle (from RedPRL research)

Provenance is **essential error infrastructure**, not optional debug info. Every metavariable must track:
1. **WHERE** it was created (`created_at: SourceRange`)
2. **WHY** it exists (`origin: MetaOrigin`)
3. **WHICH** constraints involve it (track in `SolverState.wake_on` or add `constrained_by`)

---

## Phase 1: Minimal Provenance (Week 1)

**Goal**: Add basic location and string origin to `MetaEntry`  
**Effort**: 8-12 hours  
**Deliverable**: Errors show creation location

### 1.1 Update `MetaEntry` Structure

**File**: `crates/hwml-elab/src/meta.rs`

```rust
use hwml_core::SourceRange;

#[derive(Debug, Clone)]
pub struct MetaEntry<'db> {
    pub id: MetaId,
    pub ty: RcTy<'db>,
    pub arity: usize,
    pub solution: Option<MetaSolution<'db>>,
    pub kind: MetaKind,
    
    // ===== PHASE 1: Minimal Provenance =====
    pub created_at: Option<SourceRange<'db>>,  // Optional for backward compat
    pub origin: String,                         // Simple description
}

impl<'db> MetaEntry<'db> {
    pub fn new(
        id: MetaId,
        ty: RcTy<'db>,
        arity: usize,
        kind: MetaKind,
    ) -> Self {
        MetaEntry {
            id,
            ty,
            arity,
            solution: None,
            kind,
            created_at: None,
            origin: "unknown".to_string(),
        }
    }
    
    pub fn with_provenance(
        id: MetaId,
        ty: RcTy<'db>,
        arity: usize,
        kind: MetaKind,
        created_at: SourceRange<'db>,
        origin: String,
    ) -> Self {
        MetaEntry {
            id,
            ty,
            arity,
            solution: None,
            kind,
            created_at: Some(created_at),
            origin,
        }
    }
}
```

**Backward compatibility**: `new()` still works, uses defaults.

### 1.2 Update `fresh_meta` Signature

**File**: `crates/hwml-elab/src/state.rs`

```rust
impl<'db> SolverState<'db> {
    // Keep old signature for internal use (e.g., tests)
    pub fn fresh_meta(&mut self, ty: RcTy<'db>, arity: usize, kind: MetaKind) -> MetaId {
        self.fresh_meta_with_provenance(
            ty,
            arity,
            kind,
            None,
            "unknown".to_string(),
        )
    }
    
    // New signature with provenance
    pub fn fresh_meta_with_provenance(
        &mut self,
        ty: RcTy<'db>,
        arity: usize,
        kind: MetaKind,
        created_at: Option<SourceRange<'db>>,
        origin: String,
    ) -> MetaId {
        let id = MetaId(self.next_meta);
        self.next_meta += 1;
        let entry = if let Some(loc) = created_at {
            MetaEntry::with_provenance(id, ty, arity, kind, loc, origin)
        } else {
            MetaEntry::new(id, ty, arity, kind)
        };
        self.metas.insert(id, entry);
        id
    }
}
```

### 1.3 Thread `SourceRange` Through Elaborator

**Current**: Elaboration functions don't have access to source ranges  
**Solution**: Add `span: Option<SourceRange<'db>>` parameter to key functions

**File**: `crates/hwml-elab/src/elab/expr.rs`

Update signature of `synth_underscore`:
```rust
fn synth_underscore<'a, 'db>(
    elab: &mut Elaborator<'a, 'db>,
    span: Option<SourceRange<'db>>,  // NEW
) -> Result<Checked<(RcSyntax<'db>, RcTy<'db>)>, ElabError<'db>> {
    let depth = elab.kernel.ctx.depth();
    
    // Create universe level meta with provenance
    let level_id = elab.kernel.state.fresh_meta_with_provenance(
        Rc::new(Ty::UniverseType),
        depth,
        MetaKind::UniverseLevel,
        span.clone(),  // NEW
        "underscore type placeholder (universe level)".to_string(),  // NEW
    );
    
    // ...
    
    // Create term meta with provenance
    let term_id = elab.kernel.state.fresh_meta_with_provenance(
        term_ty.clone(),
        depth,
        MetaKind::Term,
        span,  // NEW
        "underscore expression placeholder".to_string(),  // NEW
    );
    
    // ...
}
```

### 1.4 Update Call Sites (10-15 locations)

Find all calls to `fresh_meta` and update:

**Locations** (from codebase retrieval):
1. `crates/hwml-elab/src/elab/expr.rs:33-35` (ResolveDot - type meta)
2. `crates/hwml-elab/src/elab/expr.rs:40-43` (ResolveDot - value meta)
3. `crates/hwml-elab/src/elab/expr.rs:231-234` (Underscore - level meta)
4. `crates/hwml-elab/src/elab/expr.rs:241-244` (Underscore - term meta)
5. `crates/hwml-elab/src/state.rs:130` (Eq constraint - witness meta)
6. `crates/hwml-elab/src/unify/pattern.rs:291` (Intersection - new meta)
7. `crates/hwml-elab/src/unify/pattern.rs:480` (Intersection - new meta)
8. `crates/hwml-elab/src/unify/mod.rs:235` (Same-meta intersection)

**Strategy**:
- Start with `synth_underscore` (most important for user experience)
- Then `resolve_dot` (second most common)
- Finally unification internals (use `None` + descriptive origin strings)

---

## Phase 1 Deliverables

**Tests**:
- Unit test: Create meta with provenance, verify fields
- Integration test: Elaborate `_` with span, check error message

**Error message improvement**:
```
Before:  error: unsolved metavariable ?0
After:   error: unsolved metavariable ?0
           created at: src/example.hwml:12:15
           reason: underscore expression placeholder
```

---

## Next File: Phase 2-5 Details

This file is at 150 lines. Continue in `IMPLEMENTATION-PLAN-PHASES.md`.
