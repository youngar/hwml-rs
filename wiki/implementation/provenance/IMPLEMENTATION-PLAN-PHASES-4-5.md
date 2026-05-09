# Provenance Tracking: Phases 4-5

**Continuation of**: [IMPLEMENTATION-PLAN-PHASES.md](./IMPLEMENTATION-PLAN-PHASES.md)

---

## Phase 4: Dependency Tracking (Week 4)

**Goal**: Track which metavariables depend on which others  
**Effort**: 12-16 hours  
**Deliverable**: Errors show dependency chains

### 4.1 Extend `MetaEntry` with Dependencies

**File**: `crates/hwml-elab/src/meta.rs`

```rust
#[derive(Debug, Clone)]
pub struct MetaEntry<'db> {
    pub id: MetaId,
    pub ty: RcTy<'db>,
    pub arity: usize,
    pub solution: Option<MetaSolution<'db>>,
    pub kind: MetaKind,
    pub created_at: SourceRange<'db>,
    pub origin: MetaOrigin<'db>,
    
    // ===== PHASE 4: Dependency Tracking =====
    /// Metavariables that this one depends on (blocks on)
    pub depends_on: Vec<MetaId>,
    
    /// Metavariables that depend on this one (blocked by)
    pub blocks: Vec<MetaId>,
    
    /// Constraints that mention this metavariable
    pub mentioned_in: Vec<ConstraintId>,
}
```

### 4.2 Track Dependencies During Unification

When a constraint is blocked on a metavariable, record the dependency:

**File**: `crates/hwml-elab/src/state.rs`

```rust
impl<'db> SolverState<'db> {
    pub fn block_on(&mut self, cid: ConstraintId, blocking_metas: &[MetaId]) {
        let entry = self.constraints.get_mut(&cid).unwrap();
        entry.status = ConstraintStatus::Blocked(blocking_metas.to_vec());
        
        // NEW: Record dependency
        for &blocking_meta in blocking_metas {
            if let Some(meta_entry) = self.metas.get_mut(&blocking_meta) {
                if !meta_entry.mentioned_in.contains(&cid) {
                    meta_entry.mentioned_in.push(cid);
                }
            }
            
            self.wake_on
                .entry(blocking_meta)
                .or_insert_with(Vec::new)
                .push(cid);
        }
    }
}
```

### 4.3 Compute Dependency Graph

**File**: `crates/hwml-elab/src/diagnostics.rs` (new file)

```rust
use std::collections::{HashMap, HashSet};
use crate::meta::MetaId;
use crate::state::SolverState;

/// Build dependency graph: which metas depend on which
pub fn compute_meta_dependencies<'db>(
    state: &SolverState<'db>,
) -> HashMap<MetaId, HashSet<MetaId>> {
    let mut deps: HashMap<MetaId, HashSet<MetaId>> = HashMap::new();
    
    // For each constraint, record dependencies between involved metas
    for (_, entry) in state.iter_constraints() {
        if let ConstraintStatus::Blocked(blocking) = &entry.status {
            // This constraint is blocked on `blocking` metas
            let involved = extract_metas_from_constraint(&entry.constraint);
            
            for &meta in &involved {
                for &blocking_meta in blocking {
                    deps.entry(meta)
                        .or_insert_with(HashSet::new)
                        .insert(blocking_meta);
                }
            }
        }
    }
    
    deps
}

/// Extract all metavariables mentioned in a constraint
fn extract_metas_from_constraint<'db>(
    constraint: &Constraint<'db>,
) -> Vec<MetaId> {
    // Walk constraint terms and collect all Flex heads
    // Implementation details omitted for brevity
    vec![]
}
```

---

## Phase 5: Rich Error Messages (Week 5)

**Goal**: Generate beautiful diagnostic output  
**Effort**: 16-20 hours  
**Deliverable**: Production-quality error messages

### 5.1 Enhanced Error Rendering

**File**: `crates/hwml-elab/src/diagnostics.rs` (continued)

```rust
use ariadne::{Color, Label, Report, ReportKind};
use crate::error::ElabError;

/// Render an unsolved metavariable error with full provenance
pub fn render_unsolved_meta_error<'db, Db: salsa::Database>(
    db: &'db Db,
    state: &SolverState<'db>,
    meta_id: MetaId,
) -> String {
    let entry = state.meta(meta_id).unwrap();
    
    // Build ariadne report
    let mut report = Report::build(ReportKind::Error, /* file */, 0)
        .with_message(format!("unsolved metavariable ?{}", meta_id.0));
    
    // Primary label: where meta was created
    if let Some(span) = entry.created_at {
        report = report.with_label(
            Label::new((span.source.title(db), span.range.clone()))
                .with_message(format!("metavariable ?{} created here", meta_id.0))
                .with_color(Color::Red)
        );
    }
    
    // Add origin explanation
    let origin_desc = entry.origin.description();
    report = report.with_note(format!("created for: {}", origin_desc));
    
    // Add help text based on origin
    if let Some(help) = suggest_fix_for_origin(&entry.origin) {
        report = report.with_help(help);
    }
    
    // Add constraint context
    if !entry.mentioned_in.is_empty() {
        let constraint_msgs = entry.mentioned_in.iter()
            .take(3)  // Limit to first 3 constraints
            .filter_map(|&cid| {
                let c_entry = state.constraint(cid)?;
                Some(format_constraint_origin(db, &c_entry))
            })
            .collect::<Vec<_>>();
        
        if !constraint_msgs.is_empty() {
            report = report.with_note(format!(
                "constrained by:\n{}",
                constraint_msgs.join("\n")
            ));
        }
    }
    
    // Render to string
    let mut buffer = Vec::new();
    report.finish().write(/* cache */, &mut buffer).unwrap();
    String::from_utf8(buffer).unwrap()
}

fn suggest_fix_for_origin<'db>(origin: &MetaOrigin<'db>) -> Option<String> {
    match origin {
        MetaOrigin::UnderscoreExpr { .. } => 
            Some("provide an explicit type annotation".to_string()),
        MetaOrigin::UnderscoreType { .. } => 
            Some("replace '_' with a concrete type".to_string()),
        MetaOrigin::ImplicitArgument { .. } => 
            Some("make the implicit argument explicit or provide more type information".to_string()),
        _ => None,
    }
}

fn format_constraint_origin<'db, Db: salsa::Database>(
    db: &Db,
    entry: &ConstraintEntry<'db>,
) -> String {
    match &entry.constraint {
        Constraint::Eq { lhs, rhs, .. } => {
            format!("  • must unify: {} ~ {}", 
                pretty_print_value(db, lhs), 
                pretty_print_value(db, rhs))
        }
        Constraint::ResolveDot { field_name, .. } => {
            format!("  • must resolve field access '.{}'", 
                field_name.to_string(db))
        }
        _ => format!("  • constraint {:?}", entry.id),
    }
}
```

### 5.2 Update `ElabError` Display

**File**: `crates/hwml-elab/src/error.rs`

```rust
use crate::diagnostics::render_unsolved_meta_error;

impl<'db> ElabError<'db> {
    /// Render error with full context (requires database + solver state)
    pub fn render<Db: salsa::Database>(
        &self,
        db: &'db Db,
        state: &SolverState<'db>,
    ) -> String {
        match self {
            ElabError::UnsolvedMeta { meta, .. } => {
                render_unsolved_meta_error(db, state, *meta)
            }
            // Other error types can be enhanced similarly
            _ => format!("{:?}", self),
        }
    }
}
```

### 5.3 Update CLI to Use Rich Errors

**File**: `crates/hwml/src/main.rs`

```rust
// In print_elab_result or similar
for err in &result.errors {
    let rendered = err.render(&db, &result.solver_state);
    eprintln!("{}", rendered);
}
```

---

## Success Metrics

### Phase 1 Success Criteria
- [ ] All `fresh_meta` call sites have access to provenance API
- [ ] At least 3 call sites provide real provenance data
- [ ] Error messages show creation location for underscore placeholders

### Phase 5 Success Criteria
- [ ] Errors use ariadne for beautiful terminal output
- [ ] Errors show: WHERE, WHY, WHICH constraints, and HOW TO FIX
- [ ] User testing confirms improved error quality

---

## Timeline Summary

| Phase | Duration | Deliverable |
|-------|----------|-------------|
| 1. Minimal | Week 1 (8-12h) | Location + string origin |
| 2. Typed | Week 2 (12-16h) | `MetaOrigin` enum |
| 3. Constraints | Week 3 (16-20h) | `ConstraintOrigin` |
| 4. Dependencies | Week 4 (12-16h) | Dependency graph |
| 5. Rich Errors | Week 5 (16-20h) | Beautiful diagnostics |
| **Total** | **4-6 weeks** | **Production-ready provenance** |

---

## Next Steps

1. **Review this plan** with team/users
2. **Start Phase 1**: Add `created_at` and `origin` to `MetaEntry`
3. **Migrate incrementally**: One call site at a time
4. **Test continuously**: Add tests for each phase
5. **Gather feedback**: Show improved errors to users early

See [IMPLEMENTATION-PLAN.md](./IMPLEMENTATION-PLAN.md) for overview.
