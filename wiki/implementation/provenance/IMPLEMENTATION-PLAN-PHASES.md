# Provenance Tracking: Detailed Phases 2-5

**Continuation of**: [IMPLEMENTATION-PLAN.md](./IMPLEMENTATION-PLAN.md)

---

## Phase 2: Typed Origins (Week 2)

**Goal**: Replace `String` with rich `MetaOrigin` enum  
**Effort**: 12-16 hours  
**Deliverable**: Structured error messages with context

### 2.1 Define `MetaOrigin` Enum

**File**: `crates/hwml-elab/src/meta.rs`

```rust
#[derive(Debug, Clone)]
pub enum MetaOrigin<'db> {
    /// Created for underscore placeholder in expression position
    UnderscoreExpr {
        expr_span: SourceRange<'db>,
    },
    
    /// Created for underscore placeholder in type position
    UnderscoreType {
        type_span: SourceRange<'db>,
    },
    
    /// Created for implicit argument to function
    ImplicitArgument {
        function_name: String,
        function_span: SourceRange<'db>,
        param_index: usize,
        param_name: Option<String>,
    },
    
    /// Created during dot notation resolution (`.field`)
    DotResolution {
        receiver_span: SourceRange<'db>,
        field_name: String,
        field_span: SourceRange<'db>,
    },
    
    /// Created as unification variable during constraint solving
    UnificationVariable {
        constraint_id: ConstraintId,
        reason: String,  // "Pi injectivity", "pair congruence", etc.
    },
    
    /// Created for witness metavariable in equality constraint
    EqualityWitness {
        lhs_span: Option<SourceRange<'db>>,
        rhs_span: Option<SourceRange<'db>>,
    },
    
    /// Created during pattern intersection (internal to unifier)
    PatternIntersection {
        parent_meta: MetaId,
        reason: String,
    },
    
    /// Fallback for cases not yet categorized
    Other {
        description: String,
        span: Option<SourceRange<'db>>,
    },
}

impl<'db> MetaOrigin<'db> {
    /// Human-readable description for error messages
    pub fn description(&self) -> String {
        match self {
            MetaOrigin::UnderscoreExpr { .. } => 
                "underscore placeholder in expression".to_string(),
            MetaOrigin::UnderscoreType { .. } => 
                "underscore placeholder in type annotation".to_string(),
            MetaOrigin::ImplicitArgument { function_name, param_name, .. } => {
                if let Some(name) = param_name {
                    format!("implicit argument '{}' for function '{}'", name, function_name)
                } else {
                    format!("implicit argument for function '{}'", function_name)
                }
            }
            MetaOrigin::DotResolution { field_name, .. } => 
                format!("dot notation field access '.{}'", field_name),
            MetaOrigin::UnificationVariable { reason, .. } => 
                format!("unification variable ({})", reason),
            MetaOrigin::EqualityWitness { .. } => 
                "equality constraint witness".to_string(),
            MetaOrigin::PatternIntersection { parent_meta, reason } => 
                format!("intersection of ?{} ({})", parent_meta.0, reason),
            MetaOrigin::Other { description, .. } => description.clone(),
        }
    }
    
    /// Primary source location for this metavariable
    pub fn primary_location(&self) -> Option<SourceRange<'db>> {
        match self {
            MetaOrigin::UnderscoreExpr { expr_span } => Some(*expr_span),
            MetaOrigin::UnderscoreType { type_span } => Some(*type_span),
            MetaOrigin::ImplicitArgument { function_span, .. } => Some(*function_span),
            MetaOrigin::DotResolution { field_span, .. } => Some(*field_span),
            MetaOrigin::EqualityWitness { lhs_span, rhs_span } => 
                lhs_span.or(*rhs_span),
            MetaOrigin::Other { span, .. } => *span,
            _ => None,
        }
    }
}
```

### 2.2 Update `MetaEntry` to Use `MetaOrigin`

```rust
#[derive(Debug, Clone)]
pub struct MetaEntry<'db> {
    pub id: MetaId,
    pub ty: RcTy<'db>,
    pub arity: usize,
    pub solution: Option<MetaSolution<'db>>,
    pub kind: MetaKind,
    
    // PHASE 2: Rich provenance
    pub created_at: SourceRange<'db>,       // Now required!
    pub origin: MetaOrigin<'db>,            // Typed origin
}

impl<'db> MetaEntry<'db> {
    pub fn new_with_origin(
        id: MetaId,
        ty: RcTy<'db>,
        arity: usize,
        kind: MetaKind,
        created_at: SourceRange<'db>,
        origin: MetaOrigin<'db>,
    ) -> Self {
        MetaEntry {
            id,
            ty,
            arity,
            solution: None,
            kind,
            created_at,
            origin,
        }
    }
}
```

### 2.3 Update `fresh_meta` Signature (Phase 2)

**File**: `crates/hwml-elab/src/state.rs`

```rust
impl<'db> SolverState<'db> {
    pub fn fresh_meta_with_origin(
        &mut self,
        ty: RcTy<'db>,
        arity: usize,
        kind: MetaKind,
        origin: MetaOrigin<'db>,
    ) -> MetaId {
        let created_at = origin.primary_location()
            .unwrap_or_else(|| /* synthetic location */);
        
        let id = MetaId(self.next_meta);
        self.next_meta += 1;
        let entry = MetaEntry::new_with_origin(
            id, ty, arity, kind, created_at, origin
        );
        self.metas.insert(id, entry);
        id
    }
}
```

---

## Phase 3: Constraint Provenance (Week 3)

**Goal**: Track WHERE and WHY constraints are created  
**Effort**: 16-20 hours  
**Deliverable**: Errors show constraint chains

### 3.1 Define `ConstraintOrigin` Enum

**File**: `crates/hwml-elab/src/constraint.rs`

```rust
#[derive(Debug, Clone)]
pub enum ConstraintOrigin<'db> {
    /// Function application: must unify argument type with parameter type
    FunctionApplication {
        function_span: SourceRange<'db>,
        argument_span: SourceRange<'db>,
        param_index: usize,
    },
    
    /// Type annotation: must check term against annotated type
    TypeAnnotation {
        term_span: SourceRange<'db>,
        annotation_span: SourceRange<'db>,
    },
    
    /// Pattern matching: scrutinee type must match pattern type
    PatternMatch {
        scrutinee_span: SourceRange<'db>,
        pattern_span: SourceRange<'db>,
        constructor: String,
    },
    
    /// Decomposition of parent constraint by inference rule
    Decomposition {
        parent_id: ConstraintId,
        rule: &'static str,  // "Pi injectivity", "Sigma congruence"
    },
    
    /// Return type checking
    ReturnType {
        body_span: SourceRange<'db>,
        declared_type_span: SourceRange<'db>,
    },
}
```

---

## Continuation in Next File

This file approaches 150 lines. See `IMPLEMENTATION-PLAN-MIGRATION.md` for migration guide.
