# Provenance via Trace Constraints: Complete Task List

**Total Tasks**: 48 tasks across 7 phases  
**Estimated Effort**: 6-8 weeks full-time (120-160 hours)  
**Architecture**: Zero-overhead trace constraints with lazy caching  

---

## 📊 Task Breakdown by Phase

| Phase | Tasks | Effort | Deliverable |
|-------|-------|--------|-------------|
| **1. Core Infrastructure** | 5 | 12-16h | Trace types + solver integration |
| **2. Trace Emission Sites** | 8 | 20-24h | All metavar creation instrumented |
| **3. Provenance Reconstruction** | 7 | 16-20h | Query engine + lazy cache |
| **4. Rich Error Diagnostics** | 8 | 24-32h | Beautiful ariadne output |
| **5. Performance Optimization** | 8 | 16-24h | Zero overhead verified |
| **6. Research Validation** | 4 | 8-12h | Lean/Agda/GHC comparison |
| **7. Documentation & Polish** | 5 | 12-16h | README + examples |
| **Total** | **48** | **108-144h** | **Production-ready** |

---

## 🎯 Critical Path (Must Complete in Order)

### Week 1: Foundation
1. ✅ Phase 1: Core Infrastructure (all 5 tasks)
2. ✅ Phase 2: Thread SourceRange through elaboration

### Week 2-3: Instrumentation  
3. ✅ Phase 2: Emit traces in all key locations (6 tasks)

### Week 4: Query Engine
4. ✅ Phase 3: Provenance reconstruction (7 tasks)

### Week 5-6: Polish
5. ✅ Phase 4: Rich diagnostics (8 tasks)
6. ✅ Phase 5: Performance optimization (8 tasks)

### Week 7-8: Validation
7. ✅ Phase 6: Research validation (4 tasks)
8. ✅ Phase 7: Documentation (5 tasks)

---

## 🚀 Quick Start (First 3 Tasks)

### Task 1: Define TraceEntry and TraceKind types
**File**: `crates/hwml-elab/src/meta.rs`  
**Effort**: 2-3 hours  
**Deliverable**: Complete type definitions with 10+ MetaOrigin variants

```rust
pub struct TraceEntry<'db> {
    pub kind: TraceKind<'db>,
    pub location: SourceRange<'db>,
    pub timestamp: usize,
}

pub enum TraceKind<'db> {
    MetaCreated { meta, origin },
    ElabEntered { term_description, expected_type },
    ElabExited { result_type },
    ConstraintEmitted { constraint_id, reason },
    // ... 5+ more variants
}

pub enum MetaOrigin<'db> {
    UnderscoreExpr { expr_span },
    ImplicitArgument { function_name, function_span, param_index, param_name },
    DotResolution { receiver_span, field_name, field_span },
    // ... 10+ more variants (compare with GHC's 50+)
}
```

### Task 2: Add Constraint::Trace variant
**File**: `crates/hwml-elab/src/constraint.rs`  
**Effort**: 30 minutes  
**Deliverable**: New constraint variant compiles

```rust
pub enum Constraint<'db> {
    Eq { lhs, rhs, ty, witness, depth },
    LevelLeq { smaller, larger },
    ResolveDot { /* ... */ },
    
    // NEW: Non-computational trace constraint
    Trace(TraceEntry<'db>),
}
```

### Task 3: Implement SolverState::emit_trace
**File**: `crates/hwml-elab/src/state.rs`  
**Effort**: 1 hour  
**Deliverable**: Traces are created and immediately marked Solved

```rust
impl<'db> SolverState<'db> {
    pub fn emit_trace(&mut self, trace: TraceEntry<'db>) -> ConstraintId {
        let cid = ConstraintId(self.next_constraint);
        self.next_constraint += 1;
        
        let constraint = Constraint::Trace(trace);
        let mut entry = ConstraintEntry::new(cid, constraint);
        
        // KEY: Mark as Solved immediately (no computation)
        entry.status = ConstraintStatus::Solved;
        
        self.constraints.insert(cid, entry);
        // Don't add to active_queue!
        cid
    }
}
```

**Test**: Verify traces don't enter solver queue, have zero overhead.

---

## 🎨 Design Principles (The "Best of the Best")

### 1. Zero Overhead in Success Case
- Traces discarded after successful elaboration
- No metadata stored on `MetaEntry` unless error occurs
- Memory profiling confirms zero overhead

### 2. World-Class Error Messages
- Multi-span diagnostics (creation + constraints)
- Contextual suggestions based on origin
- Constraint chain visualization
- Elaboration stack display
- Beautiful terminal output (ariadne)

### 3. Research-Backed Design
- Matches Lean 4's InfoTree capabilities
- Exceeds Agda's error quality
- Covers all GHC's 50+ origin cases
- Aligns with language-integrated provenance papers

### 4. Production-Ready Performance
- Sub-millisecond provenance reconstruction
- Lazy caching for O(1) repeated queries
- Trace indexing for fast lookup
- Optional --no-provenance flag for absolute zero overhead

### 5. Future-Proof Architecture
- Enables LSP hover/code actions
- Supports incremental compilation
- Compatible with MLIR location tracking
- Extensible trace kinds

---

## 📈 Success Metrics

### Must-Have (Blocking Ship)
- [ ] Zero memory overhead after success (memory profiling)
- [ ] < 1ms provenance reconstruction (benchmarks)
- [ ] No elaboration speed regression (< 2% acceptable)
- [ ] Multi-span errors with suggestions (user testing)
- [ ] All 48 tasks complete

### Nice-to-Have (Can Ship Without)
- [ ] Matches Lean 4 error quality (subjective)
- [ ] Covers 50+ origin variants (can start with 10+)
- [ ] LSP integration (future work)
- [ ] Trace visualization tool (future work)

---

## 🔄 Iterative Implementation Strategy

### Vertical Slice Approach (Recommended)

**Week 1**: Complete vertical slice for `synth_underscore`
- Task 1.1: Define types
- Task 1.2-1.5: Core infrastructure
- Task 2.1: Emit trace in synth_underscore
- Task 3.1-3.3: Basic reconstruction
- Task 4.1-4.2: Basic ariadne error

**Result**: One error type (underscore) has world-class diagnostics

**Week 2-3**: Expand to all error types
- Tasks 2.2-2.8: All emission sites
- Tasks 3.4-3.7: Complete reconstruction

**Week 4-6**: Polish and optimize
- Phase 4: Rich diagnostics
- Phase 5: Performance

**Week 7-8**: Validate and document
- Phase 6: Research comparison
- Phase 7: Documentation

---

## 📚 Documentation Deliverables

1. **README.md** - Architecture overview, quick start
2. **IMPLEMENTATION-GUIDE.md** - Detailed implementation steps
3. **ERROR-EXAMPLES.md** - Before/after error message gallery
4. **MIGRATION-GUIDE.md** - User-facing changes
5. **LSP-INTEGRATION.md** - Future work roadmap
6. **Inline rustdoc** - All public types/functions documented

---

## 🎯 Next Actions

1. **Review this task list** - Validate completeness
2. **Start Task 1.1** - Define TraceEntry types
3. **Set up tests** - Unit tests for each phase
4. **Track progress** - Mark tasks [/] → [x] as you go
5. **Iterate quickly** - Vertical slices, frequent feedback

---

## 📞 Questions & Support

- **Architecture questions**: See [ALTERNATIVE-TRACE-CONSTRAINTS.md](./ALTERNATIVE-TRACE-CONSTRAINTS.md)
- **Implementation details**: See [TRACE-CONSTRAINTS-IMPLEMENTATION-GUIDE.md](./TRACE-CONSTRAINTS-IMPLEMENTATION-GUIDE.md)
- **Research background**: See [../../research/provenance-deep-dive.md](../../research/provenance-deep-dive.md)
- **RedPRL comparison**: See [../../research/redprl-provenance.md](../../research/redprl-provenance.md)

Ready to build the best-in-class provenance tracking system! 🚀
