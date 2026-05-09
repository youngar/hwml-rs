# Provenance Tracking: Design Summary

**Date:** 2026-05-08  
**Audience:** Implementation team  
**Goal:** Quick reference for implementing provenance tracking

---

## What Problem Are We Solving?

**Current error message:**
```
error: unsolved metavariable ?42
```

**User reaction:** *"What is ?42? Where did it come from? How do I fix this?"*

**Target error message:**
```
error: unsolved metavariable ?0
  ┌─ src/example.hwml:12:15
  │
12│     let result = compute _ in
  │                          ^ type cannot be inferred here
  │
  = note: created for underscore placeholder
  = help: provide an explicit type annotation
  = constrained by:
    • function application at line 15
    • return type must match 'Nat' at line 3
```

**User reaction:** *"Ah! I need to annotate the underscore. Got it."*

---

## The Solution: Provenance Tracking

**Provenance** = The "birth certificate" of a metavariable

Every metavariable tracks:
- **WHERE** it was created (source location)
- **WHY** it was created (implicit arg, underscore, dot resolution, etc.)
- **WHICH** constraints involve it
- **WHAT** other metavariables it depends on

---

## Architecture Decision: Side-Table Approach

Instead of bloating `MetaEntry`, use a separate **provenance side-table**:

```rust
pub struct SolverState<'db> {
    // Core solver (always present)
    metas: HashMap<MetaId, MetaEntry<'db>>,
    constraints: HashMap<ConstraintId, ConstraintEntry<'db>>,
    
    // Provenance tracking (side-table)
    meta_provenance: HashMap<MetaId, MetaProvenance<'db>>,  // ← NEW
}
```

**Benefits:**
- ✅ Zero overhead if meta solves (provenance GC'd)
- ✅ `MetaEntry` stays minimal (40 bytes)
- ✅ Full context available for errors
- ✅ Backward compatible (old `fresh_meta()` still works)

---

## Key Types

### MetaProvenance (Side-table Entry)

```rust
#[derive(Debug, Clone)]
pub struct MetaProvenance<'db> {
    pub created_at: SourceRange<'db>,
    pub origin: MetaOrigin<'db>,
    pub timestamp: usize,
    pub parent: Option<MetaId>,
}
```

### MetaOrigin (Phase 1: Simple)

```rust
#[derive(Debug, Clone)]
pub enum MetaOrigin<'db> {
    UnderscoreExpr { expr_span: SourceRange<'db> },
    UnderscoreType { type_span: SourceRange<'db> },
    ImplicitArgument { function_span: SourceRange<'db> },
    DotResolution { field_span: SourceRange<'db> },
    UnificationVariable { reason: String },
    Other { description: String },
}
```

### MetaOrigin (Phase 3: Rich)

```rust
#[derive(Debug, Clone)]
pub enum MetaOrigin<'db> {
    ImplicitArgument {
        function_name: String,
        function_span: SourceRange<'db>,
        param_index: usize,
        param_name: Option<String>,
    },
    // ... other rich variants
}
```

---

## API: How to Create Metas with Provenance

### Before

```rust
let meta_id = elab.kernel.state.fresh_meta(
    ty,
    arity,
    MetaKind::Term,
);
```

### After

```rust
let meta_id = elab.kernel.state.fresh_meta_with_trace(
    ty,
    arity,
    MetaKind::Term,
    MetaOrigin::UnderscoreExpr { expr_span: span },
    span,
    None,  // parent
);
```

---

## Implementation Phases

### Phase 1: Side-Table Foundation (Week 1)
- Add `MetaProvenance` struct
- Add `meta_provenance: HashMap` to `SolverState`
- Implement `fresh_meta_with_trace()`
- Update error display to show location

**Deliverable:** Errors show "created at line X"

### Phase 2: Trace Constraints (Week 2)
- Add `TraceEntry` type
- Emit trace constraints on meta creation
- Store as Solved constraints

**Deliverable:** Full elaboration trace available

### Phase 3: Typed Origins (Week 3)
- Expand `MetaOrigin` enum with rich variants
- Add helper methods (`.describe()`, `.primary_location()`)
- Update call sites to use typed origins

**Deliverable:** Contextual error messages

### Phase 4: Constraint Provenance (Week 4)
- Add `ConstraintOrigin` enum
- Add `created_at` and `origin` to `ConstraintEntry`
- Update `emit_eq()` and other constraint emission

**Deliverable:** Errors show constraint chains

### Phase 5: Rich Diagnostics (Week 5-6)
- Add `ariadne` dependency
- Create `diagnostics.rs` module
- Implement multi-span error rendering
- Update CLI to use rich errors

**Deliverable:** Rust-quality error messages

---

## Files to Modify

```
crates/hwml-elab/src/
  ├─ meta.rs         ← Add MetaProvenance, MetaOrigin, TraceEntry
  ├─ state.rs        ← Add meta_provenance HashMap, fresh_meta_with_trace()
  ├─ constraint.rs   ← Add ConstraintOrigin, Trace variant
  ├─ error.rs        ← Add render() method
  ├─ diagnostics.rs  ← NEW: Ariadne rendering
  └─ elab/
      ├─ expr.rs     ← Update synth_underscore call site
      └─ decl.rs     ← Update other call sites

Cargo.toml           ← Add ariadne = "0.6"
```

---

## Testing Strategy

### Unit Test (Phase 1)

```rust
#[test]
fn test_provenance_tracked() {
    let db = TestDatabase::default();
    let mut state = SolverState::new();
    
    let range = dummy_source_range(&db);
    let origin = MetaOrigin::UnderscoreExpr { expr_span: range };
    
    let id = state.fresh_meta_with_trace(ty, 0, MetaKind::Term, origin, range, None);
    
    let prov = state.provenance(id).unwrap();
    assert!(matches!(prov.origin, MetaOrigin::UnderscoreExpr { .. }));
}
```

### Integration Test (Phase 5)

```rust
#[test]
fn test_underscore_error() {
    let db = TestDatabase::default();
    let result = elab_library(&db, "def x = _;");
    
    assert!(result.errors.len() > 0);
    let rendered = result.errors[0].render(&db, &result.state);
    assert!(rendered.contains("underscore"));
    assert!(rendered.contains("12:15"));
}
```

---

## Success Metrics

- [ ] All metas have provenance
- [ ] Errors show WHERE metas were created
- [ ] Errors show WHY metas were created
- [ ] Errors show constraint chains
- [ ] Multi-span rendering works
- [ ] User debugging time reduced by 70%

---

## Next Steps

1. **Review this design** with team
2. **Start Phase 1** by adding `MetaProvenance` struct to `meta.rs`
3. **Test incrementally** after each phase
4. **Migrate call sites** starting with `synth_underscore`
5. **Gather user feedback** on error quality

---

## References

- **Full Design:** [provenance-tracking-design.md](./provenance-tracking-design.md)
- **Architecture Diagram:** [provenance-tracking-architecture-diagram.md](./provenance-tracking-architecture-diagram.md)
- **Research:** [../wiki/research/PROVENANCE-SUMMARY.md](../wiki/research/PROVENANCE-SUMMARY.md)
- **Implementation Plan:** [../wiki/implementation/provenance/IMPLEMENTATION-PLAN.md](../wiki/implementation/provenance/IMPLEMENTATION-PLAN.md)
