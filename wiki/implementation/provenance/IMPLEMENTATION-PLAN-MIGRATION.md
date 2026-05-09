# Provenance Implementation: Migration Guide

**Part of**: [IMPLEMENTATION-PLAN.md](./IMPLEMENTATION-PLAN.md)

---

## Migration Strategy

The implementation uses a **progressive migration** approach to avoid breaking the build:

### Stage 1: Dual API (Week 1)

Keep both old and new APIs simultaneously:

```rust
// crates/hwml-elab/src/state.rs

impl<'db> SolverState<'db> {
    /// OLD API - deprecated but still works
    #[deprecated(note = "Use fresh_meta_with_provenance instead")]
    pub fn fresh_meta(&mut self, ty: RcTy<'db>, arity: usize, kind: MetaKind) -> MetaId {
        self.fresh_meta_with_provenance(ty, arity, kind, None, "legacy".to_string())
    }
    
    /// NEW API - Phase 1
    pub fn fresh_meta_with_provenance(
        &mut self,
        ty: RcTy<'db>,
        arity: usize,
        kind: MetaKind,
        created_at: Option<SourceRange<'db>>,
        origin: String,
    ) -> MetaId {
        // Implementation...
    }
}
```

**Benefits**:
- Build never breaks
- Can migrate call sites incrementally
- Tests keep passing
- Easy to revert if needed

### Stage 2: Incremental Migration (Weeks 1-2)

Migrate call sites one at a time, prioritized by user impact:

**Priority 1** (user-facing errors):
1. `synth_underscore` - users type `_` frequently
2. `resolve_dot` - common in HWML code
3. Implicit arguments (when implemented)

**Priority 2** (internal but visible):
4. Equality constraint witnesses
5. Type inference metas

**Priority 3** (internal only):
6. Unification intersection metas
7. Pattern unification helpers

### Stage 3: Remove Old API (Week 3)

Once all call sites migrated:
1. Remove `#[deprecated]` attribute
2. Make old `fresh_meta` call the new API
3. Or remove entirely if no longer needed

---

## Detailed Call Site Migration

### Example 1: `synth_underscore`

**Before** (`crates/hwml-elab/src/elab/expr.rs:227-246`):
```rust
fn synth_underscore<'a, 'db>(
    elab: &mut Elaborator<'a, 'db>,
) -> Result<Checked<(RcSyntax<'db>, RcTy<'db>)>, ElabError<'db>> {
    let depth = elab.kernel.ctx.depth();
    let level_id = elab.kernel.state.fresh_meta(
        Rc::new(Ty::UniverseType),
        depth,
        MetaKind::UniverseLevel,
    );
    // ...
    let term_id = elab.kernel.state.fresh_meta(
        term_ty.clone(),
        depth,
        MetaKind::Term,
    );
    // ...
}
```

**After (Phase 1)**:
```rust
fn synth_underscore<'a, 'db>(
    elab: &mut Elaborator<'a, 'db>,
    span: Option<SourceRange<'db>>,  // NEW parameter
) -> Result<Checked<(RcSyntax<'db>, RcTy<'db>)>, ElabError<'db>> {
    let depth = elab.kernel.ctx.depth();
    
    let level_id = elab.kernel.state.fresh_meta_with_provenance(
        Rc::new(Ty::UniverseType),
        depth,
        MetaKind::UniverseLevel,
        span.clone(),
        "underscore type placeholder".to_string(),
    );
    
    // ...
    
    let term_id = elab.kernel.state.fresh_meta_with_provenance(
        term_ty.clone(),
        depth,
        MetaKind::Term,
        span,
        "underscore expression placeholder".to_string(),
    );
    // ...
}
```

**Call site update** (`crates/hwml-elab/src/elab/expr.rs:~190`):
```rust
// Before:
Expression::Underscore(_) => synth_underscore(elab),

// After:
Expression::Underscore(und) => {
    // Assume surface syntax has span info
    let span = Some(SourceRange::new(/* extract from und */));
    synth_underscore(elab, span)
}
```

### Example 2: `resolve_dot`

**Before** (`crates/hwml-elab/src/elab/expr.rs:30-44`):
```rust
// Create fresh metavariables for the result
let result_ty_code_meta = elab.kernel.state.fresh_meta(
    Rc::new(Ty::UniverseType),
    depth,
    MetaKind::UniverseLevel,
);
// ...
let result_val_meta = elab.kernel.state.fresh_meta(
    result_ty.clone(),
    depth,
    MetaKind::Term,
);
```

**After (Phase 2 - with typed origins)**:
```rust
use crate::meta::MetaOrigin;

// Create fresh metavariables for the result
let result_ty_code_meta = elab.kernel.state.fresh_meta_with_origin(
    Rc::new(Ty::UniverseType),
    depth,
    MetaKind::UniverseLevel,
    MetaOrigin::DotResolution {
        receiver_span: receiver_span.clone(),  // Get from surface syntax
        field_name: field_name.to_string(db),
        field_span: field_span.clone(),        // Get from surface syntax
    },
);

let result_val_meta = elab.kernel.state.fresh_meta_with_origin(
    result_ty.clone(),
    depth,
    MetaKind::Term,
    MetaOrigin::DotResolution {
        receiver_span,
        field_name: field_name.to_string(db),
        field_span,
    },
);
```

---

## Accessing Surface Syntax Spans

**Challenge**: Elaborator currently doesn't preserve `SourceRange` from surface syntax.

**Solution**: Thread spans through elaboration functions.

### Update Surface AST (if needed)

Check if `hwml_surface::Expression` has span information:

```rust
// Check in crates/hwml-surface/src/lib.rs or similar

pub enum Expression {
    Id(Identifier),           // Identifier likely has span
    Underscore(/* ??? */),    // Check what's here
    // ...
}
```

**If spans exist**: Extract and pass through  
**If spans don't exist**: Add them to surface AST first (separate task)

### Temporary Workaround (Phase 1)

If surface spans aren't available yet, use `None`:

```rust
let level_id = elab.kernel.state.fresh_meta_with_provenance(
    Rc::new(Ty::UniverseType),
    depth,
    MetaKind::UniverseLevel,
    None,  // TODO: Thread span from surface syntax
    "underscore type placeholder".to_string(),
);
```

This still improves error messages (shows origin description), and can be enhanced later.

---

## Testing Strategy

### Unit Tests

**File**: `crates/hwml-elab/tests/provenance_tests.rs` (new file)

```rust
use hwml_core::{SourceRange, Source, SourceInfo, Word};
use hwml_elab::{meta::*, state::SolverState};
use std::rc::Rc;

#[test]
fn test_meta_provenance_stored() {
    let mut state = SolverState::new();
    
    // Create a synthetic source range for testing
    let db = /* test database */;
    let label = Word::new(db, "test");
    let source = Source::new(db, SourceInfo::Synthetic(label));
    let span = SourceRange::new(source, 0..10);
    
    let ty = Rc::new(hwml_core::ty::Ty::UniverseType);
    let id = state.fresh_meta_with_provenance(
        ty,
        0,
        MetaKind::Term,
        Some(span.clone()),
        "test metavariable".to_string(),
    );
    
    let entry = state.meta(id).unwrap();
    assert_eq!(entry.created_at, Some(span));
    assert_eq!(entry.origin, "test metavariable");
}
```

---

## File Continues

See `IMPLEMENTATION-PLAN-PHASES-4-5.md` for Phases 4-5 details.
