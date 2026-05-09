# Provenance Tracking Design for HWML

**Date:** 2026-05-08
**Status:** Design Sketch
**Goal:** Transform `error: unsolved metavariable ?42` into actionable Rust-quality diagnostics

---

## Executive Summary

This design implements provenance tracking using a **hybrid side-table approach** that balances memory efficiency with error quality. The core `MetaEntry` remains minimal for the success path, while a separate `MetaProvenance` table captures rich context for error reporting.

### Key Design Decisions

1. **Side-table architecture** - Zero overhead in success case
2. **Trace constraints** - Provenance events stored as immediately-solved constraints
3. **Lazy reconstruction** - Build provenance graph only on error
4. **Three-tier origins** - Simple → Typed → Rich with dependencies
5. **Phased migration** - Each phase delivers value independently

---

## Current State

<augment_code_snippet path="crates/hwml-elab/src/meta.rs" mode="EXCERPT">
````rust
#[derive(Debug, Clone)]
pub struct MetaEntry<'db> {
    pub id: MetaId,
    pub ty: RcTy<'db>,
    pub arity: usize,
    pub solution: Option<MetaSolution<'db>>,
    pub kind: MetaKind,
}
````
</augment_code_snippet>

**Problems:**
- ❌ No `created_at` location
- ❌ No `origin` explanation
- ❌ No constraint tracking
- ❌ Errors show `?42` with no context

---

## Phase 1: Side-Table Foundation (Week 1)

### Architecture: Provenance Side-Table

**Key Insight:** Don't bloat `MetaEntry`. Use a separate table queried only on error.

<augment_code_snippet path="crates/hwml-elab/src/state.rs" mode="EXCERPT">
````rust
pub struct SolverState<'db> {
    // Core solver data (always present)
    pub(crate) metas: HashMap<MetaId, MetaEntry<'db>>,
    pub(crate) constraints: HashMap<ConstraintId, ConstraintEntry<'db>>,

    // Provenance tracking (side-table, lazy allocation)
    meta_provenance: HashMap<MetaId, MetaProvenance<'db>>,
}
````
</augment_code_snippet>

### New Types

```rust
// crates/hwml-elab/src/meta.rs

/// Provenance information stored in side-table
#[derive(Debug, Clone)]
pub struct MetaProvenance<'db> {
    /// Source location where meta was created
    pub created_at: SourceRange<'db>,

    /// Semantic origin (why it exists)
    pub origin: MetaOrigin<'db>,

    /// Chronological creation order
    pub timestamp: usize,

    /// Parent meta (for dependency tracking)
    pub parent: Option<MetaId>,
}

/// Phase 1: Simple string origins
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

### Updated API

```rust
impl<'db> SolverState<'db> {
    /// OLD: No provenance (for tests/internal use)
    pub fn fresh_meta(&mut self, ty: RcTy<'db>, arity: usize, kind: MetaKind) -> MetaId {
        let id = MetaId(self.next_meta);
        self.next_meta += 1;
        self.metas.insert(id, MetaEntry::new(id, ty, arity, kind));
        id
    }

    /// NEW: With provenance tracking
    pub fn fresh_meta_with_trace(
        &mut self,
        ty: RcTy<'db>,
        arity: usize,
        kind: MetaKind,
        origin: MetaOrigin<'db>,
        location: SourceRange<'db>,
        parent: Option<MetaId>,
    ) -> MetaId {
        let id = self.fresh_meta(ty, arity, kind);

        // Store provenance in side-table
        let provenance = MetaProvenance {
            created_at: location.clone(),
            origin: origin.clone(),
            timestamp: self.elaboration_step,
            parent,
        };
        self.meta_provenance.insert(id, provenance);
        self.elaboration_step += 1;

        // Emit trace constraint for reconstruction (Phase 2+)
        self.emit_trace(TraceEntry::new(
            TraceKind::MetaCreated { meta: id, origin },
            location,
            self.elaboration_step,
        ));

        id
    }

    /// Query provenance (for error reporting)
    pub fn provenance(&self, id: MetaId) -> Option<&MetaProvenance<'db>> {
        self.meta_provenance.get(&id)
    }
}
```

---

## Phase 2: Trace Constraints (Week 2)

### Architecture: Provenance as Constraints

**Key Insight:** Store provenance events as immediately-solved constraints. This enables reconstruction of the full elaboration trace.

```rust
// crates/hwml-elab/src/meta.rs

#[derive(Debug, Clone)]
pub struct TraceEntry<'db> {
    pub kind: TraceKind<'db>,
    pub location: SourceRange<'db>,
    pub timestamp: usize,
}

#[derive(Debug, Clone)]
pub enum TraceKind<'db> {
    MetaCreated { meta: MetaId, origin: MetaOrigin<'db> },
    ConstraintEmitted { constraint_id: ConstraintId, lhs: RcValue<'db>, rhs: RcValue<'db> },
    MetaSolved { meta: MetaId, solution: RcValue<'db> },
}
```

**Trace constraints are stored in the constraint table with `status: Solved`:**

```rust
// crates/hwml-elab/src/constraint.rs

#[derive(Debug, Clone)]
pub enum Constraint<'db> {
    Eq { ... },
    LevelLeq { ... },
    ResolveDot { ... },

    /// Trace constraint: immediately marked Solved, used for error reporting only
    Trace(TraceEntry<'db>),
}
```

**Benefits:**
- ✅ Provenance survives solver passes
- ✅ Can reconstruct full elaboration history
- ✅ No separate storage needed (reuse constraint infrastructure)

---

## Phase 3: Typed Origins (Week 3)

### Richer MetaOrigin Variants

```rust
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
        reason: String,  // "Pi injectivity", "intersection"
    },

    EqualityWitness {
        lhs_span: Option<SourceRange<'db>>,
        rhs_span: Option<SourceRange<'db>>,
    },

    PatternIntersection {
        parent_meta: MetaId,
        reason: String,
    },
}

impl<'db> MetaOrigin<'db> {
    /// Human-readable description
    pub fn describe(&self) -> String {
        match self {
            MetaOrigin::UnderscoreExpr { .. } =>
                "underscore placeholder in expression".into(),
            MetaOrigin::ImplicitArgument { function_name, param_name, .. } => {
                if let Some(name) = param_name {
                    format!("implicit argument '{}' for function '{}'", name, function_name)
                } else {
                    format!("implicit argument for function '{}'", function_name)
                }
            }
            MetaOrigin::DotResolution { field_name, .. } =>
                format!("dot notation field access '.{}'", field_name),
            // ... other variants
        }
    }

    /// Primary location for this origin
    pub fn primary_location(&self) -> Option<SourceRange<'db>> {
        match self {
            MetaOrigin::UnderscoreExpr { expr_span } => Some(*expr_span),
            MetaOrigin::UnderscoreType { type_span } => Some(*type_span),
            MetaOrigin::ImplicitArgument { function_span, .. } => Some(*function_span),
            MetaOrigin::DotResolution { field_span, .. } => Some(*field_span),
            MetaOrigin::EqualityWitness { lhs_span, rhs_span } => lhs_span.or(*rhs_span),
            _ => None,
        }
    }
}
```

---

## Phase 4: Constraint Provenance (Week 4)

### ConstraintOrigin

```rust
// crates/hwml-elab/src/constraint.rs

#[derive(Debug, Clone)]
pub enum ConstraintOrigin<'db> {
    FunctionApplication {
        function_span: SourceRange<'db>,
        argument_span: SourceRange<'db>,
        param_index: usize,
    },

    TypeAnnotation {
        term_span: SourceRange<'db>,
        annotation_span: SourceRange<'db>,
    },

    PatternMatch {
        scrutinee_span: SourceRange<'db>,
        pattern_span: SourceRange<'db>,
        constructor: String,
    },

    Decomposition {
        parent_id: ConstraintId,
        rule: &'static str,  // "Pi injectivity", "Sigma congruence"
    },

    DotResolution {
        receiver_span: SourceRange<'db>,
        field_name: String,
    },
}

#[derive(Debug, Clone)]
pub struct ConstraintEntry<'db> {
    pub id: ConstraintId,
    pub constraint: Constraint<'db>,
    pub status: ConstraintStatus,

    // NEW: Provenance
    pub created_at: Option<SourceRange<'db>>,
    pub origin: Option<ConstraintOrigin<'db>>,
}
```

### Updated emit_* APIs

```rust
impl<'db> SolverState<'db> {
    pub fn emit_eq_with_origin(
        &mut self,
        lhs: RcValue<'db>,
        rhs: RcValue<'db>,
        origin: ConstraintOrigin<'db>,
        location: SourceRange<'db>,
    ) -> ConstraintId {
        let id = self.emit_eq(lhs, rhs);

        // Add provenance to existing entry
        if let Some(entry) = self.constraints.get_mut(&id) {
            entry.created_at = Some(location.clone());
            entry.origin = Some(origin.clone());
        }

        // Emit trace
        self.emit_trace(TraceEntry::new(
            TraceKind::ConstraintEmitted { constraint_id: id, lhs, rhs },
            location,
            self.elaboration_step,
        ));

        id
    }
}
```


---

## Phase 5: Rich Diagnostics with Ariadne (Week 5-6)

### Error Rendering Infrastructure

```rust
// crates/hwml-elab/src/diagnostics.rs (NEW FILE)

use ariadne::{Color, Label, Report, ReportKind, Source};
use crate::{meta::MetaId, state::SolverState};

pub fn render_unsolved_meta_error<'db>(
    db: &'db dyn salsa::Database,
    state: &SolverState<'db>,
    meta_id: MetaId,
) -> String {
    let entry = state.meta(meta_id).expect("meta should exist");
    let provenance = state.provenance(meta_id);

    // Build Ariadne report
    let mut report = Report::build(ReportKind::Error, (), 0)
        .with_message(format!("unsolved metavariable ?{}", meta_id.0));

    // Primary label: where meta was created
    if let Some(prov) = provenance {
        let range = prov.created_at.range.clone();
        let source_title = prov.created_at.source.title(db);

        report = report.with_label(
            Label::new((source_title, range))
                .with_message(format!("metavariable ?{} created here", meta_id.0))
                .with_color(Color::Red)
        );

        // Secondary label: origin context
        if let Some(origin_loc) = prov.origin.primary_location() {
            let origin_range = origin_loc.range.clone();
            let origin_source = origin_loc.source.title(db);

            report = report.with_label(
                Label::new((origin_source, origin_range))
                    .with_message(prov.origin.describe())
                    .with_color(Color::Blue)
            );
        }

        // Note: origin description
        report = report.with_note(format!("created for: {}", prov.origin.describe()));
    }

    // Find constraints involving this meta
    let involving_constraints = state.constraints_involving(meta_id);
    if !involving_constraints.is_empty() {
        report = report.with_note(format!(
            "constrained by {} constraint(s)",
            involving_constraints.len()
        ));

        for (cid, entry) in involving_constraints.iter().take(3) {
            if let Some(origin) = &entry.origin {
                let desc = format!("  • constraint #{}: {:?}", cid.0, origin);
                report = report.with_note(desc);
            }
        }
    }

    // Render to string
    let mut output = Vec::new();
    // TODO: Need source cache for Ariadne
    report.finish().write((), &mut output).unwrap();
    String::from_utf8(output).unwrap()
}
```

### Enhanced ElabError

```rust
// crates/hwml-elab/src/error.rs

impl<'db> ElabError<'db> {
    /// Render error with full provenance context
    pub fn render(
        &self,
        db: &'db dyn salsa::Database,
        state: &SolverState<'db>,
    ) -> String {
        match self {
            ElabError::UnsolvedMeta { meta, .. } => {
                render_unsolved_meta_error(db, state, *meta)
            }

            ElabError::UnificationFailure { lhs, rhs, span } => {
                // TODO: Multi-span showing flow from lhs to rhs
                format!("unification failure: {:?} ≠ {:?}", lhs, rhs)
            }

            ElabError::OccursCheck { meta, span } => {
                if let Some(prov) = state.provenance(*meta) {
                    format!(
                        "occurs check failed for ?{}\n  created at: {:?}\n  reason: {}",
                        meta.0,
                        prov.created_at,
                        prov.origin.describe()
                    )
                } else {
                    format!("occurs check failed for ?{}", meta.0)
                }
            }

            // Fallback for other error types
            _ => format!("{:?}", self),
        }
    }
}
```

---

## Migration Strategy

### Call Site Updates

**Priority order:**

1. **`synth_underscore`** (highest user impact)
   ```rust
   // Before:
   let term_id = elab.kernel.state.fresh_meta(term_ty.clone(), depth, MetaKind::Term);

   // After:
   let term_id = elab.kernel.state.fresh_meta_with_trace(
       term_ty.clone(),
       depth,
       MetaKind::Term,
       MetaOrigin::UnderscoreExpr { expr_span: /* TODO: get from AST */ },
       /* location */,
       None,
   );
   ```

2. **`resolve_dot`** (second most common)
3. **Implicit arguments** (when implemented)
4. **Unification internals** (lowest priority - use generic origins)

### Backward Compatibility

Keep `fresh_meta()` for tests and internal use. New code should use `fresh_meta_with_trace()`.

---

## Example: Before vs After

### Before (Current)

```
error: unsolved metavariable ?0
```

### After Phase 1 (Side-table)

```
error: unsolved metavariable ?0
  created at: src/example.hwml:12:15
  reason: underscore placeholder in expression
```

### After Phase 5 (Rich Diagnostics)

```
error: unsolved metavariable ?0
  ┌─ src/example.hwml:12:15
  │
12│     let result = compute _ in
  │                          ^ type cannot be inferred here
  │
  = note: created for: underscore placeholder in expression
  = help: provide an explicit type annotation
  = constrained by 2 constraint(s):
    • constraint #5: function application at src/example.hwml:15:8
    • constraint #7: return type at src/example.hwml:3:25
```

---

## Memory Overhead Analysis

### Success Case (No Errors)

- `MetaEntry`: **40 bytes** (unchanged)
- `MetaProvenance`: **0 bytes** (not allocated if meta solves)
- `TraceEntry`: **~64 bytes** per trace, stored as Solved constraint

**Overhead per meta:** ~64 bytes for trace (acceptable)

### Error Case

- Full provenance tree constructed on-demand
- Queries side-table + trace constraints
- Only for unsolved metas (typically <10 in error case)

**Overhead:** ~500 bytes per unsolved meta (negligible)

---

## Testing Strategy

### Unit Tests

```rust
#[test]
fn test_fresh_meta_with_trace() {
    let db = hwml_core::TestDatabase::default();
    let mut state = SolverState::new();

    let range = dummy_source_range(&db);
    let origin = MetaOrigin::UnderscoreExpr { expr_span: range.clone() };

    let meta_id = state.fresh_meta_with_trace(
        Rc::new(Ty::UniverseType),
        0,
        MetaKind::Term,
        origin,
        range,
        None,
    );

    let prov = state.provenance(meta_id).expect("provenance should exist");
    assert_eq!(prov.timestamp, 0);
    assert!(matches!(prov.origin, MetaOrigin::UnderscoreExpr { .. }));
}
```

### Integration Tests

```rust
#[test]
fn test_underscore_error_message() {
    let db = TestDatabase::default();
    let source = "def x = _;";

    let result = elab_library(&db, source);
    assert!(result.errors.len() > 0);

    let rendered = result.errors[0].render(&db, &result.state);
    assert!(rendered.contains("underscore"));
    assert!(rendered.contains("?0"));
}
```

---

## Implementation Timeline

| Phase | Duration | Deliverable | Impact |
|-------|----------|-------------|--------|
| **1. Side-table** | 1 week | `MetaProvenance` in side-table | Basic location tracking |
| **2. Trace constraints** | 1 week | Full elaboration trace | Reconstruction capability |
| **3. Typed origins** | 1 week | Rich `MetaOrigin` enum | Contextual descriptions |
| **4. Constraint provenance** | 1 week | `ConstraintOrigin` tracking | Constraint chains |
| **5. Rich diagnostics** | 2 weeks | Ariadne integration | Rust-quality errors |

**Total:** 6 weeks for full implementation

---

## Success Metrics

### Phase 1
- ✅ All metas have location
- ✅ Errors show creation location
- ✅ Test suite passes

### Phase 3
- ✅ Origins are typed (no raw strings)
- ✅ Different messages per origin type
- ✅ At least 5 origin variants in use

### Phase 5
- ✅ Multi-span error rendering
- ✅ Errors show 2+ locations
- ✅ Color terminal output
- ✅ User debugging time: -70%
- ✅ "Confusing error" reports: -90%

---

## Key Files to Modify

```
crates/hwml-elab/src/
  meta.rs           ← Add MetaProvenance, MetaOrigin, TraceEntry
  state.rs          ← Add meta_provenance HashMap, fresh_meta_with_trace
  constraint.rs     ← Add ConstraintOrigin, Trace variant
  error.rs          ← Add render() method
  diagnostics.rs    ← NEW: Ariadne rendering
  elab/expr.rs      ← Update synth_underscore call sites
  elab/decl.rs      ← Update call sites (if needed)

Cargo.toml          ← Add ariadne = "0.6" dependency
```

---

## References

- [PROVENANCE-SUMMARY.md](../wiki/research/PROVENANCE-SUMMARY.md) - Research overview
- [provenance-deep-dive.md](../wiki/research/provenance-deep-dive.md) - Comprehensive analysis
- [redprl-provenance.md](../wiki/research/redprl-provenance.md) - RedPRL's telescope approach
- [IMPLEMENTATION-PLAN.md](../wiki/implementation/provenance/IMPLEMENTATION-PLAN.md) - Original plan

---

**Next Action:** Start Phase 1 by adding `MetaProvenance` struct and `fresh_meta_with_trace()` method.


