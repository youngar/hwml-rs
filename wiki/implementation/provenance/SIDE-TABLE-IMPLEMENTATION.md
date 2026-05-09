# Side-Table Provenance Implementation

**Status**: ✅ Implemented and tested  
**Date**: 2026-05-08  
**Architecture**: Zero-overhead side-table with parent-pointer provenance tree  

---

## 🎯 Design Decisions

### **1. Side-Table Architecture (Avoiding the "Zero Overhead" Myth)**

**Problem**: Unconditionally allocating `SourceRange` + `MetaOrigin` in every `MetaEntry` would thrash the allocator during complex elaboration (thousands of metavariables per second).

**Solution**: Store provenance in a **separate `HashMap<MetaId, MetaProvenance>`** in `SolverState`.

```rust
pub struct SolverState<'db> {
    // Core solver state (unchanged)
    metas: HashMap<MetaId, MetaEntry<'db>>,
    constraints: HashMap<ConstraintId, ConstraintEntry<'db>>,
    
    // NEW: Side-table for provenance (lazy allocation)
    meta_provenance: HashMap<MetaId, MetaProvenance<'db>>,
}
```

**Benefits**:
- ✅ Zero memory overhead when provenance is not tracked
- ✅ Easy to add `--no-provenance` flag later
- ✅ Mirrors Lean 4's design
- ✅ No allocator thrashing in the hot path

---

### **2. Parent-Pointer Tree (Avoiding the Bidirectional Graph Trap)**

**Problem**: Maintaining `blocked_on: Vec<MetaId>` and `blocks: Vec<MetaId>` creates borrow-checking nightmares and state synchronization issues during unification.

**Solution**: Use a **simple parent pointer** to build a provenance tree.

```rust
pub struct MetaProvenance<'db> {
    pub created_at: SourceRange<'db>,
    pub origin: MetaOrigin<'db>,
    pub timestamp: usize,
    pub parent: Option<MetaId>,  // Simple tree, NOT bidirectional graph
}
```

**Benefits**:
- ✅ Directed tree (sufficient for error traces)
- ✅ No manual graph edge maintenance
- ✅ Works with existing `wake_on` map
- ✅ Simple traversal: `chain()` method reconstructs provenance path

**Example Provenance Chain**:
```
?M3 (implicit arg 'x') 
  └─ parent: ?M2 (function result)
     └─ parent: ?M1 (underscore expr)
        └─ parent: None (root)
```

---

### **3. Timestamp Counter in SolverState**

**Decision**: Keep `elaboration_step: usize` in `SolverState`, NOT in `ElabContext`.

**Reasoning**:
- `ElabContext` is typically immutable or functionally pushed/popped
- `SolverState` is the centralized mutable tracking hub
- Avoids threading mutable counter through every AST synthesis rule

**Usage**:
- Incremented on every `fresh_meta_with_trace` call
- Used for chronological ordering and tie-breaking
- Not the primary ordering mechanism (parent tree is)

---

## 🏗️ Implementation Details

### **New API: `fresh_meta_with_trace`**

```rust
pub fn fresh_meta_with_trace(
    &mut self,
    ty: RcTy<'db>,
    arity: usize,
    kind: MetaKind,
    origin: MetaOrigin<'db>,
    location: SourceRange<'db>,
    parent: Option<MetaId>,
) -> MetaId {
    let id = self.fresh_meta(ty, arity, kind);  // Reuse existing logic
    
    // Store provenance in side-table
    self.meta_provenance.insert(id, MetaProvenance::new(
        location.clone(),
        origin.clone(),
        self.elaboration_step,
        parent,
    ));
    self.elaboration_step += 1;
    
    // Emit trace constraint
    self.emit_trace(TraceEntry::new(
        TraceKind::MetaCreated { meta: id, origin },
        location,
        self.elaboration_step,
    ));
    
    id
}
```

### **Provenance Access Methods**

```rust
// Query single meta's provenance
pub fn provenance(&self, id: MetaId) -> Option<&MetaProvenance<'db>>

// Extract all provenance (for error reporting)
pub fn extract_provenance(&self) -> HashMap<MetaId, MetaProvenance<'db>>

// Get unsolved metas with provenance
pub fn unsolved_metas_with_provenance(&self) 
    -> Vec<(MetaId, &MetaEntry<'db>, Option<&MetaProvenance<'db>>)>
```

### **Lifecycle Management**

```rust
// Clear provenance after successful SCC elaboration
pub fn clear_provenance(&mut self)
```

**Per-SCC Clearing**:
- Called after successful elaboration of each SCC
- Ensures zero memory overhead across SCCs
- Can be extended for global LSP caching later (Phase 6-7)

---

## ✅ Test Coverage

**7 tests passing**:

1. `test_emit_trace_creates_solved_constraint` - Basic trace emission
2. `test_emit_trace_not_in_active_queue` - Zero solver overhead
3. `test_multiple_traces_independence` - Multiple traces don't interfere
4. `test_trace_vs_regular_constraint` - Traces vs regular constraints
5. `test_fresh_meta_with_trace` - New API works correctly
6. `test_provenance_parent_chain` - Parent-child relationships work
7. `test_clear_provenance` - Lifecycle management works

---

## 📊 Files Modified

1. **`crates/hwml-elab/src/meta.rs`**:
   - Added `MetaProvenance` struct
   - Added `chain()` method for provenance reconstruction

2. **`crates/hwml-elab/src/state.rs`**:
   - Added `meta_provenance` side-table
   - Added `elaboration_step` counter
   - Added `fresh_meta_with_trace` API
   - Added provenance access/management methods
   - Added 3 new tests

---

## 🚀 Next Steps

Ready to proceed to **Phase 2: Trace Emission Sites**:
- Instrument `synth_underscore` to use `fresh_meta_with_trace`
- Thread `SourceRange` through elaboration functions
- Add trace emission for all metavariable creation points
