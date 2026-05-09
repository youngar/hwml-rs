# Provenance Tracking Implementation Cheat Sheet

Quick reference for implementing provenance tracking in HWML.

---

## Quick Start: Add Provenance to a Meta

### Step 1: Import types
```rust
use crate::meta::{MetaOrigin, MetaProvenance};
use hwml_core::SourceRange;
```

### Step 2: Get source location
```rust
// From AST node with span
let span = expr.span;

// From current context (if no span available)
let span = elab.current_span();

// Synthetic location (last resort)
let span = SourceRange::synthetic(db, "compiler-generated");
```

### Step 3: Choose origin variant
```rust
// For underscore in expression: let x = _
let origin = MetaOrigin::UnderscoreExpr { expr_span: span };

// For underscore in type: let x : _ = 5
let origin = MetaOrigin::UnderscoreType { type_span: span };

// For dot resolution: receiver.field
let origin = MetaOrigin::DotResolution {
    receiver_span: receiver.span,
    field_name: "field".to_string(),
    field_span: field.span,
};

// For implicit argument
let origin = MetaOrigin::ImplicitArgument {
    function_name: "foo".to_string(),
    function_span: fn_span,
    param_index: 0,
    param_name: Some("x".to_string()),
};

// Fallback for other cases
let origin = MetaOrigin::Other {
    description: "internal unification variable".to_string(),
};
```

### Step 4: Create meta with provenance
```rust
// OLD WAY (deprecated for user-facing code)
let meta_id = state.fresh_meta(ty, arity, MetaKind::Term);

// NEW WAY (always use this)
let meta_id = state.fresh_meta_with_trace(
    ty,                // Type of the metavariable
    arity,            // Number of local variables in scope
    MetaKind::Term,   // Term or UniverseLevel
    origin,           // MetaOrigin (why it was created)
    span,             // SourceRange (where it was created)
    None,             // Optional parent MetaId
);
```

---

## Common Patterns

### Pattern 1: Underscore Expression
```rust
fn synth_underscore(elab: &mut Elaborator, span: SourceRange) -> Result<...> {
    let depth = elab.kernel.ctx.depth();
    
    // Universe level meta
    let level_origin = MetaOrigin::UnderscoreType { type_span: span };
    let level_id = elab.kernel.state.fresh_meta_with_trace(
        Rc::new(Ty::UniverseType),
        depth,
        MetaKind::UniverseLevel,
        level_origin,
        span,
        None,
    );
    
    // Term meta (depends on level meta)
    let term_origin = MetaOrigin::UnderscoreExpr { expr_span: span };
    let term_id = elab.kernel.state.fresh_meta_with_trace(
        term_ty,
        depth,
        MetaKind::Term,
        term_origin,
        span,
        Some(level_id),  // parent = level_id
    );
}
```

### Pattern 2: Dot Resolution
```rust
fn resolve_dot(
    elab: &mut Elaborator,
    receiver: Expr,
    field: Ident,
) -> Result<...> {
    let depth = elab.kernel.ctx.depth();
    
    let origin = MetaOrigin::DotResolution {
        receiver_span: receiver.span,
        field_name: field.name.clone(),
        field_span: field.span,
    };
    
    let meta_id = elab.kernel.state.fresh_meta_with_trace(
        result_ty,
        depth,
        MetaKind::Term,
        origin,
        field.span,  // Use field span as primary location
        None,
    );
}
```

### Pattern 3: Internal Unification Variable
```rust
fn pattern_intersection(
    state: &mut SolverState,
    parent_meta: MetaId,
) -> MetaId {
    let origin = MetaOrigin::PatternIntersection {
        parent_meta,
        reason: "argument scope restriction".to_string(),
    };
    
    state.fresh_meta_with_trace(
        ty,
        arity,
        MetaKind::Term,
        origin,
        SourceRange::synthetic(db, "pattern-intersection"),
        Some(parent_meta),
    )
}
```

---

## Querying Provenance (Error Reporting)

### Get provenance for a meta
```rust
if let Some(prov) = state.provenance(meta_id) {
    println!("Created at: {:?}", prov.created_at);
    println!("Origin: {}", prov.origin.describe());
    println!("Timestamp: {}", prov.timestamp);
}
```

### Get all unsolved metas with provenance
```rust
let unsolved = state.unsolved_metas_with_provenance();
for (meta_id, entry, provenance) in unsolved {
    if let Some(prov) = provenance {
        eprintln!("Unsolved ?{}: {}", meta_id.0, prov.origin.describe());
    }
}
```

---

## Error Message Patterns

### Basic (Phase 1)
```rust
impl Display for ElabError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            ElabError::UnsolvedMeta { meta, .. } => {
                if let Some(prov) = state.provenance(*meta) {
                    write!(f, "error: unsolved metavariable ?{}\n", meta.0)?;
                    write!(f, "  created at: {:?}\n", prov.created_at)?;
                    write!(f, "  reason: {}", prov.origin.describe())?;
                } else {
                    write!(f, "error: unsolved metavariable ?{}", meta.0)?;
                }
                Ok(())
            }
        }
    }
}
```

### Rich (Phase 5)
```rust
pub fn render_unsolved_meta(
    db: &dyn Database,
    state: &SolverState,
    meta_id: MetaId,
) -> String {
    use ariadne::{Report, Label, Color};
    
    let prov = state.provenance(meta_id).unwrap();
    
    Report::build(ReportKind::Error, (), 0)
        .with_message(format!("unsolved metavariable ?{}", meta_id.0))
        .with_label(
            Label::new(prov.created_at.clone())
                .with_message("created here")
                .with_color(Color::Red)
        )
        .with_note(format!("reason: {}", prov.origin.describe()))
        .finish()
        .to_string()
}
```

---

## Debugging Tips

### Print provenance during elaboration
```rust
eprintln!("[DEBUG] Created ?{} at {:?}: {}",
    meta_id.0,
    span,
    origin.describe()
);
```

### Dump all provenance
```rust
pub fn dump_provenance(state: &SolverState) {
    for (meta_id, prov) in &state.meta_provenance {
        eprintln!("?{}: {} (timestamp {})",
            meta_id.0,
            prov.origin.describe(),
            prov.timestamp
        );
    }
}
```

---

## Common Mistakes to Avoid

❌ **Don't use `fresh_meta()` for user-facing code**
```rust
// BAD
let id = state.fresh_meta(ty, arity, kind);
```

✅ **Always use `fresh_meta_with_trace()`**
```rust
// GOOD
let id = state.fresh_meta_with_trace(ty, arity, kind, origin, span, parent);
```

---

❌ **Don't use generic string descriptions**
```rust
// BAD
let origin = MetaOrigin::Other { description: "some meta".to_string() };
```

✅ **Use specific origin variants**
```rust
// GOOD
let origin = MetaOrigin::UnderscoreExpr { expr_span: span };
```

---

❌ **Don't forget to pass the span**
```rust
// BAD
let origin = MetaOrigin::UnderscoreExpr { expr_span: dummy_span() };
```

✅ **Get the real span from AST**
```rust
// GOOD
let origin = MetaOrigin::UnderscoreExpr { expr_span: expr.span };
```

---

## Phase Checklist

### Phase 1 Complete When:
- [ ] `MetaProvenance` struct added to `meta.rs`
- [ ] `meta_provenance` HashMap added to `SolverState`
- [ ] `fresh_meta_with_trace()` implemented
- [ ] At least one call site updated (e.g., `synth_underscore`)
- [ ] Error display shows location

### Phase 2 Complete When:
- [ ] `TraceEntry` and `TraceKind` defined
- [ ] Trace constraints emitted on meta creation
- [ ] Traces stored as Solved constraints

### Phase 3 Complete When:
- [ ] All `MetaOrigin` variants defined
- [ ] `.describe()` and `.primary_location()` methods work
- [ ] All call sites use typed origins (no strings)

### Phase 4 Complete When:
- [ ] `ConstraintOrigin` enum defined
- [ ] `created_at` and `origin` added to `ConstraintEntry`
- [ ] Constraint emission updated

### Phase 5 Complete When:
- [ ] `ariadne` dependency added
- [ ] `diagnostics.rs` module created
- [ ] Multi-span rendering works
- [ ] CLI uses rich errors
