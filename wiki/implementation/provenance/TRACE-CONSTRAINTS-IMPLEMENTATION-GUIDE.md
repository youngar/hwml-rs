# Trace Constraints: Best-in-Class Implementation Guide

**Status**: Production-ready design  
**Goal**: Zero-overhead provenance tracking with world-class error diagnostics  
**Architecture**: Trace constraints + lazy caching  

---

## 📋 Complete Task List

See task list in conversation for 48 detailed tasks across 7 phases.

### Phase Overview

1. **Core Infrastructure** (5 tasks) - Trace types, constraint variant, solver integration
2. **Trace Emission** (8 tasks) - Instrument all metavar creation sites
3. **Provenance Reconstruction** (7 tasks) - Query engine + lazy caching
4. **Rich Diagnostics** (8 tasks) - Ariadne integration, beautiful errors
5. **Performance** (8 tasks) - Zero overhead verification, optimization
6. **Research Validation** (4 tasks) - Compare with Lean/Agda/GHC
7. **Documentation** (5 tasks) - README, examples, migration guide

---

## 🎯 Success Criteria

### Performance Targets (Must-Have)

- ✅ **Zero memory overhead** after successful elaboration (traces discarded)
- ✅ **Sub-millisecond provenance reconstruction** on error
- ✅ **No regression** in elaboration speed (< 2% slowdown acceptable)
- ✅ **Lazy caching** ensures repeated queries are O(1)

### Error Quality Targets (Must-Have)

- ✅ **Multi-span errors** showing creation point + constraints
- ✅ **Contextual suggestions** based on origin type
- ✅ **Constraint chains** showing why meta exists
- ✅ **Elaboration stack** showing term traversal path
- ✅ **Beautiful terminal output** using ariadne (colors, arrows, etc.)

### Comparison Benchmarks (Aspirational)

- ✅ **Matches Lean 4** error quality for common cases
- ✅ **Exceeds Agda** in constraint chain visualization
- ✅ **Covers all GHC origin cases** (50+ variants)

---

## 🏗️ Architecture Diagram

```
┌─────────────────────────────────────────────────────────────┐
│ Elaborator (elab/expr.rs, elab/decl.rs)                    │
│                                                             │
│  synth_underscore()    resolve_dot()    check_lambda()     │
│         │                    │                  │           │
│         └────────────────────┴──────────────────┘           │
│                              │                              │
│                    emit_trace(TraceEntry)                   │
│                              │                              │
└──────────────────────────────┼──────────────────────────────┘
                               ▼
┌─────────────────────────────────────────────────────────────┐
│ SolverState (state.rs)                                      │
│                                                             │
│  constraints: HashMap<ConstraintId, ConstraintEntry>        │
│    ├─ Constraint::Eq { ... }                               │
│    ├─ Constraint::ResolveDot { ... }                       │
│    └─ Constraint::Trace(TraceEntry)  ← NEW                 │
│                                                             │
│  trace_index: HashMap<MetaId, Vec<TraceEntry>>  ← Phase 5  │
└─────────────────────────────────────────────────────────────┘
                               │
                    ┌──────────┴──────────┐
                    ▼                     ▼
         ┌────────────────────┐   ┌────────────────┐
         │ Success Path       │   │ Error Path     │
         │                    │   │                │
         │ 1. Discard traces  │   │ 1. Query traces│
         │ 2. Zero overhead   │   │ 2. Reconstruct │
         │                    │   │ 3. Cache       │
         │                    │   │ 4. Render      │
         └────────────────────┘   └────────────────┘
                                           │
                                           ▼
                                  ┌─────────────────┐
                                  │ Diagnostics     │
                                  │ (diagnostics.rs)│
                                  │                 │
                                  │ - Ariadne       │
                                  │ - Multi-span    │
                                  │ - Suggestions   │
                                  └─────────────────┘
```

---

## 📦 Phase 1: Core Infrastructure

### Task 1.1: Define TraceEntry and TraceKind

**File**: `crates/hwml-elab/src/meta.rs`

```rust
use hwml_core::SourceRange;

/// A trace entry recording a provenance-relevant event during elaboration
#[derive(Debug, Clone)]
pub struct TraceEntry<'db> {
    pub kind: TraceKind<'db>,
    pub location: SourceRange<'db>,
    pub timestamp: usize,  // Elaboration step counter for ordering
}

/// All provenance-relevant events that can be traced
#[derive(Debug, Clone)]
pub enum TraceKind<'db> {
    // === Metavariable Creation ===
    
    MetaCreated {
        meta: MetaId,
        origin: MetaOrigin<'db>,
    },
    
    // === Elaboration Traversal ===
    
    ElabEntered {
        term_description: String,  // "lambda", "application", etc.
        expected_type: Option<RcTy<'db>>,
    },
    
    ElabExited {
        result_type: RcTy<'db>,
    },
    
    // === Constraint Events ===
    
    ConstraintEmitted {
        constraint_id: ConstraintId,
        reason: String,
    },
    
    ConstraintBlocked {
        constraint_id: ConstraintId,
        blocking_metas: Vec<MetaId>,
    },
    
    // === Solving Events ===
    
    MetaSolved {
        meta: MetaId,
        solution_preview: String,  // First 50 chars of solution
    },
}

/// Rich origin information for metavariable creation
#[derive(Debug, Clone)]
pub enum MetaOrigin<'db> {
    UnderscoreExpr {
        expr_span: SourceRange<'db>,
    },
    
    UnderscoreType {
        type_span: SourceRange<'db>,
    },
    
    ImplicitArgument {
        function_name: String,
        function_span: SourceRange<'db>,
        param_index: usize,
        param_name: Option<String>,
    },
    
    DotResolution {
        receiver_span: SourceRange<'db>,
        field_name: String,
        field_span: SourceRange<'db>,
    },
    
    UnificationVariable {
        constraint_id: ConstraintId,
        reason: String,  // "Pi injectivity", "intersection", etc.
    },
    
    EqualityWitness {
        lhs_span: Option<SourceRange<'db>>,
        rhs_span: Option<SourceRange<'db>>,
    },
    
    // Add 10+ more as needed (compare with GHC's 50+ variants)
}

impl<'db> MetaOrigin<'db> {
    pub fn description(&self) -> String {
        match self {
            MetaOrigin::UnderscoreExpr { .. } => 
                "underscore placeholder in expression".into(),
            MetaOrigin::ImplicitArgument { function_name, param_name, .. } => {
                if let Some(name) = param_name {
                    format!("implicit argument '{}' for '{}'", name, function_name)
                } else {
                    format!("implicit argument for '{}'", function_name)
                }
            }
            // ... all variants
        }
    }
    
    pub fn primary_location(&self) -> Option<SourceRange<'db>> {
        match self {
            MetaOrigin::UnderscoreExpr { expr_span } => Some(*expr_span),
            MetaOrigin::ImplicitArgument { function_span, .. } => Some(*function_span),
            // ... all variants
        }
    }
}
```

**Deliverable**: Types compile, unit tests pass

---

## Continuation

See [TRACE-CONSTRAINTS-PHASE-2.md](./TRACE-CONSTRAINTS-PHASE-2.md) for remaining phases.
