# Provenance via Trace Constraints: Alternative Design

**Date**: 2026-05-07  
**Status**: Exploratory alternative to [IMPLEMENTATION-PLAN.md](./IMPLEMENTATION-PLAN.md)

---

## The Idea

> "What if provenance is represented as constraints that hold only debug information, used only under duress (when errors occur)?"

Instead of adding `created_at` and `origin` fields to `MetaEntry`, emit **trace constraints** that:
1. Carry no computational content (don't affect solving)
2. Are marked `Solved` immediately
3. Accumulate provenance information as the elaborator traverses terms
4. Are queried only when errors need to be reported

---

## Motivation

### Current Approach (from IMPLEMENTATION-PLAN.md)
```rust
pub struct MetaEntry<'db> {
    pub id: MetaId,
    pub ty: RcTy<'db>,
    pub arity: usize,
    pub solution: Option<MetaSolution<'db>>,
    pub kind: MetaKind,
    
    // NEW: Provenance metadata
    pub created_at: SourceRange<'db>,
    pub origin: MetaOrigin<'db>,
    pub depends_on: Vec<MetaId>,    // Phase 4
    pub blocks: Vec<MetaId>,        // Phase 4
}
```

**Problem**: Metadata stored on every metavariable, whether or not errors occur.

### Trace Constraints Approach
```rust
pub enum Constraint<'db> {
    // Computational constraints (existing)
    Eq { lhs, rhs, ty, witness, depth },
    LevelLeq { smaller, larger },
    ResolveDot { ... },
    
    // NEW: Trace constraints (non-computational)
    Trace(TraceEntry<'db>),
}

pub struct TraceEntry<'db> {
    pub kind: TraceKind<'db>,
    pub location: SourceRange<'db>,
}

pub enum TraceKind<'db> {
    MetaCreated { meta: MetaId, origin: MetaOrigin<'db> },
    ConstraintEmitted { constraint_id: ConstraintId, reason: String },
    ElabEntered { term_span: SourceRange<'db>, expected_type: Option<RcTy<'db>> },
    ElabExited { result_type: RcTy<'db> },
}
```

**Benefit**: Provenance only stored if errors occur. Zero overhead in success case (trace constraints discarded).

---

## Design

### 1. Emit Trace Constraints During Elaboration

Whenever elaborator crosses a "provenance boundary" (creates meta, enters term, etc.), emit a trace:

```rust
// In synth_underscore
fn synth_underscore<'a, 'db>(
    elab: &mut Elaborator<'a, 'db>,
    span: SourceRange<'db>,
) -> Result<Checked<(RcSyntax<'db>, RcTy<'db>)>, ElabError<'db>> {
    let depth = elab.kernel.ctx.depth();
    
    // Create metavariable
    let level_id = elab.kernel.state.fresh_meta(
        Rc::new(Ty::UniverseType),
        depth,
        MetaKind::UniverseLevel,
    );
    
    // EMIT TRACE (no computational content)
    elab.kernel.state.emit_trace(TraceEntry {
        kind: TraceKind::MetaCreated {
            meta: level_id,
            origin: MetaOrigin::UnderscoreType { type_span: span },
        },
        location: span,
    });
    
    // Continue elaboration...
}
```

### 2. Solver Immediately Marks Traces as Solved

```rust
impl<'db> SolverState<'db> {
    pub fn emit_trace(&mut self, trace: TraceEntry<'db>) -> ConstraintId {
        let cid = ConstraintId(self.next_constraint);
        self.next_constraint += 1;
        
        let constraint = Constraint::Trace(trace);
        let mut entry = ConstraintEntry::new(cid, constraint);
        
        // KEY: Mark as solved immediately (no computation needed)
        entry.status = ConstraintStatus::Solved;
        
        self.constraints.insert(cid, entry);
        // Don't add to active_queue!
        cid
    }
}
```

### 3. On Error: Reconstruct Provenance from Traces

```rust
// In diagnostics.rs
pub fn explain_unsolved_meta<'db>(
    state: &SolverState<'db>,
    meta_id: MetaId,
) -> MetaProvenance<'db> {
    // Query trace constraints for this meta
    let creation_trace = state
        .iter_constraints()
        .filter_map(|(_, entry)| match &entry.constraint {
            Constraint::Trace(trace) => match &trace.kind {
                TraceKind::MetaCreated { meta, origin } if *meta == meta_id => {
                    Some((trace.location, origin.clone()))
                }
                _ => None,
            },
            _ => None,
        })
        .next();
    
    creation_trace
        .map(|(loc, origin)| MetaProvenance { created_at: loc, origin })
        .unwrap_or_else(|| MetaProvenance::unknown())
}
```

---

## Advantages

### ✅ Zero Overhead in Success Case
- Trace constraints never enter `active_queue`
- Solver skips them (already `Solved`)
- Can be garbage-collected after successful elaboration
- No metadata stored on `MetaEntry` unless error occurs

### ✅ Unified Infrastructure
- Reuses existing constraint machinery
- No new data structures on `MetaEntry` or `SolverState`
- Traces participate in constraint graph (can show dependencies)

### ✅ Flexible Granularity
- Emit traces only where needed (under certain terms, in certain modes)
- Can enable/disable trace emission with a flag
- Easy to add new trace kinds without changing core data structures

### ✅ Natural Accumulation
- As elaborator descends into terms, traces accumulate in constraint store
- Captures elaboration "stack" naturally
- Can reconstruct full elaboration context on error

---

## Disadvantages

### ❌ Query Cost on Error
- Must scan all constraints to find traces for a specific meta
- Could be slow if many constraints exist
- **Mitigation**: Index traces by `MetaId` in a separate map

### ❌ Memory Usage During Elaboration
- Traces stored until elaboration completes
- Every meta creation = 1 constraint entry
- **Mitigation**: Can discard traces after elaboration succeeds

### ❌ Indirection
- Provenance not directly on `MetaEntry`, must query
- More complex than direct field access
- **Mitigation**: Cache results of provenance queries

---

## Hybrid Approach (Best of Both Worlds?)

### Idea: Trace Constraints + Lightweight Metadata

1. **During elaboration**: Emit trace constraints (as above)
2. **On success**: Discard traces, no overhead
3. **On error**: Reconstruct provenance from traces, cache in `MetaEntry`

```rust
pub struct MetaEntry<'db> {
    pub id: MetaId,
    pub ty: RcTy<'db>,
    pub arity: usize,
    pub solution: Option<MetaSolution<'db>>,
    pub kind: MetaKind,
    
    // LAZY: Only populated on error
    pub provenance_cache: Option<MetaProvenance<'db>>,
}

pub struct MetaProvenance<'db> {
    pub created_at: SourceRange<'db>,
    pub origin: MetaOrigin<'db>,
    // Reconstructed from traces
}
```

**On unsolved meta error**:
```rust
fn report_unsolved_meta(state: &mut SolverState, meta_id: MetaId) {
    let entry = state.metas.get_mut(&meta_id).unwrap();
    
    // Check cache
    if entry.provenance_cache.is_none() {
        // Reconstruct from traces
        entry.provenance_cache = Some(explain_unsolved_meta(state, meta_id));
    }
    
    // Use cached provenance for error message
    let prov = entry.provenance_cache.as_ref().unwrap();
    // ...
}
```

---

## Comparison with Direct Metadata

| Aspect | Direct Metadata (Plan A) | Trace Constraints (Plan B) | Hybrid |
|--------|--------------------------|----------------------------|--------|
| **Memory (success)** | ~80 bytes/meta | ~120 bytes/constraint (discarded) | 0 bytes |
| **Memory (error)** | ~80 bytes/meta | ~120 bytes/constraint (retained) | ~80 bytes/meta |
| **Query speed** | O(1) field access | O(N) scan constraints | O(1) cached |
| **Implementation** | Modify `MetaEntry` | Reuse `Constraint` | Both |
| **Complexity** | Medium | Medium | High |

---

## Recommendation

### For HWML: **Hybrid Approach**

**Rationale**:
1. **Success case (common)**: Zero overhead, traces discarded
2. **Error case (rare)**: Reconstruct provenance once, cache in `MetaEntry`
3. **Implementation**: Start with trace constraints, add cache lazily

**Implementation Path**:
1. **Phase 1**: Add `Constraint::Trace` variant
2. **Phase 2**: Emit traces in key locations (underscore, dot notation)
3. **Phase 3**: Add provenance reconstruction in error handling
4. **Phase 4**: Add lazy cache to `MetaEntry` if query cost too high

---

## Open Questions

1. **Trace granularity**: How many traces to emit? Every term? Only at metavar creation?
2. **Trace indexing**: Build `HashMap<MetaId, Vec<TraceEntry>>` for fast lookup?
3. **Trace lifecycle**: When to discard? After elaboration? After zonking?
4. **Trace merging**: If Phase 4 adds direct metadata, do we keep traces?

---

## Next Steps

- [ ] Prototype `Constraint::Trace` variant
- [ ] Implement `emit_trace` in `SolverState`
- [ ] Add trace reconstruction in error handling
- [ ] Benchmark memory usage vs direct metadata approach

See [TRACE-CONSTRAINTS-PROTOTYPE.md](./TRACE-CONSTRAINTS-PROTOTYPE.md) for implementation.
