# Provenance Tracking Implementation

**Status**: Ready for implementation  
**Research Date**: 2026-05-07  
**Estimated Effort**: 4-6 weeks  

---

## Overview

This directory contains the complete implementation plan for adding **provenance tracking** to HWML's elaborator. Provenance tracking transforms cryptic metavariable errors into actionable, user-friendly diagnostics.

### Current Error Messages
```
error: unsolved metavariable ?42
```

### Target Error Messages (Phase 5)
```
error: unsolved metavariable ?0
  ┌─ src/example.hwml:12:15
  │
12│     let result = compute _ in
  │                          ^ type cannot be inferred
  │
  = note: created for underscore type placeholder
  = help: provide an explicit type annotation
  = constrained by:
    • function application at src/example.hwml:15:8
      must unify: Nat ~ ?0
    • return type must match 'Bool' at src/example.hwml:3:25
```

---

## Documents

### Core Implementation Plan
- **[IMPLEMENTATION-PLAN.md](./IMPLEMENTATION-PLAN.md)**: Executive summary + Phase 1 details
- **[IMPLEMENTATION-PLAN-PHASES.md](./IMPLEMENTATION-PLAN-PHASES.md)**: Phases 2-3 (typed origins, constraints)
- **[IMPLEMENTATION-PLAN-PHASES-4-5.md](./IMPLEMENTATION-PLAN-PHASES-4-5.md)**: Phases 4-5 (dependencies, diagnostics)
- **[IMPLEMENTATION-PLAN-MIGRATION.md](./IMPLEMENTATION-PLAN-MIGRATION.md)**: Migration strategy + testing

### Background Research
- **[../../research/redprl-provenance.md](../../research/redprl-provenance.md)**: RedPRL's telescope approach
- **[../../research/provenance-deep-dive.md](../../research/provenance-deep-dive.md)**: Cross-system analysis
- **[../../research/provenance-action-plan.md](../../research/provenance-action-plan.md)**: Original action plan

---

## Quick Start: Phase 1 (Week 1)

**Goal**: Add basic provenance to `MetaEntry`

### Step 1: Update `MetaEntry`

**File**: `crates/hwml-elab/src/meta.rs`

```rust
#[derive(Debug, Clone)]
pub struct MetaEntry<'db> {
    // Existing fields
    pub id: MetaId,
    pub ty: RcTy<'db>,
    pub arity: usize,
    pub solution: Option<MetaSolution<'db>>,
    pub kind: MetaKind,
    
    // NEW: Provenance
    pub created_at: Option<SourceRange<'db>>,
    pub origin: String,
}
```

### Step 2: Update `SolverState::fresh_meta`

**File**: `crates/hwml-elab/src/state.rs`

```rust
impl<'db> SolverState<'db> {
    pub fn fresh_meta_with_provenance(
        &mut self,
        ty: RcTy<'db>,
        arity: usize,
        kind: MetaKind,
        created_at: Option<SourceRange<'db>>,
        origin: String,
    ) -> MetaId {
        // Create meta with provenance...
    }
}
```

### Step 3: Migrate Call Sites

Start with `synth_underscore` in `crates/hwml-elab/src/elab/expr.rs`:

```rust
// Before:
let meta = state.fresh_meta(ty, arity, kind);

// After:
let meta = state.fresh_meta_with_provenance(
    ty,
    arity,
    kind,
    Some(span),
    "underscore placeholder".to_string(),
);
```

### Step 4: Test

```bash
cargo test -p hwml-elab
```

---

## Phase Summary

| Phase | Effort | Key Deliverable |
|-------|--------|-----------------|
| **1. Minimal** | 8-12h | `created_at: Option<SourceRange>`, `origin: String` |
| **2. Typed Origins** | 12-16h | `origin: MetaOrigin<'db>` enum |
| **3. Constraint Provenance** | 16-20h | `ConstraintOrigin<'db>` + tracking |
| **4. Dependencies** | 12-16h | Dependency graph, `depends_on`/`blocks` fields |
| **5. Rich Errors** | 16-20h | Ariadne-based beautiful diagnostics |

**Total**: 64-84 hours (4-6 weeks part-time)

---

## Architecture Decisions

### Why This Design?

1. **Provenance is Essential Infrastructure** (not debug info)
   - From Lean 4, Agda, GHC research: provenance is ALWAYS present
   - Errors are unusable without it
   
2. **Phased Implementation** (inspired by RedPRL)
   - Start minimal, grow incrementally
   - Never break the build
   - Each phase delivers value
   
3. **Rich Typed Origins** (from GHC's `CtOrigin`)
   - Enum with context-specific fields
   - Enables contextual help messages
   - Better than strings for structured analysis

4. **Location-First** (from MLIR)
   - `SourceRange` already interned via Salsa
   - 1-based line:column (compatible with LSP, MLIR)
   - Cheap to store, copy, compare

### Key Insights from Research

**RedPRL**: Provenance can be *architectural* (telescope position = creation order)  
**Lean 4**: Origin tracking enables rich suggestions ("did you mean...?")  
**Agda**: Constraint provenance shows *why* a meta was created (not just where)  
**GHC**: 50+ origin variants cover all elaboration scenarios

---

## Files Modified by Phase

### Phase 1: Minimal Provenance
- `crates/hwml-elab/src/meta.rs` (add fields)
- `crates/hwml-elab/src/state.rs` (update `fresh_meta`)
- `crates/hwml-elab/src/elab/expr.rs` (thread spans)
- `crates/hwml-elab/src/error.rs` (display provenance)

### Phase 2: Typed Origins
- `crates/hwml-elab/src/meta.rs` (add `MetaOrigin` enum)
- All Phase 1 files (migrate to typed origins)

### Phase 3: Constraint Provenance
- `crates/hwml-elab/src/constraint.rs` (add `ConstraintOrigin`)
- `crates/hwml-elab/src/state.rs` (track constraint origins)

### Phase 4: Dependencies
- `crates/hwml-elab/src/meta.rs` (add `depends_on`, `blocks`)
- `crates/hwml-elab/src/state.rs` (maintain dep graph)
- `crates/hwml-elab/src/diagnostics.rs` (NEW - compute deps)

### Phase 5: Rich Errors
- `crates/hwml-elab/src/diagnostics.rs` (ariadne rendering)
- `crates/hwml-elab/src/error.rs` (use diagnostics)
- `crates/hwml/src/main.rs` (CLI integration)
- `Cargo.toml` (add `ariadne` dependency)

---

## Next Actions

1. ✅ **Research complete** - RedPRL, Lean 4, Agda analyzed
2. ✅ **Implementation plan complete** - All phases detailed
3. ⏩ **Start Phase 1** - Update `MetaEntry` struct
4. ⏳ **Migrate call sites** - Begin with `synth_underscore`
5. ⏳ **Write tests** - Unit + integration tests for provenance
6. ⏳ **Gather feedback** - Show improved errors to users

---

## Questions?

- **Why not store full elaboration context?** Too expensive. Location + origin enum is sufficient.
- **Why not use DWARF-style debug info?** Provenance is runtime infrastructure for error messages, not post-hoc debugging.
- **Why phased instead of all-at-once?** Safety. Each phase delivers value and can be tested independently.

See implementation plan documents for detailed answers.
