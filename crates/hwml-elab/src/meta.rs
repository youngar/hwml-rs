use hwml_core::{RcSyntax, RcValue, ty::RcTy, SourceRange};

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct MetaId(pub u32);

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MetaKind {
    Term,
    UniverseLevel,
}

/// A solved metavariable stores both representations:
/// - `syntax`: closed term (abstracted over meta's arity) for zonking
/// - `value`: evaluated form for fast `force_flex` during unification
#[derive(Debug, Clone)]
pub struct MetaSolution<'db> {
    pub syntax: RcSyntax<'db>,
    pub value: RcValue<'db>,
}

#[derive(Debug, Clone)]
pub struct MetaEntry<'db> {
    pub id: MetaId,
    pub ty: RcTy<'db>,
    pub arity: usize,
    pub solution: Option<MetaSolution<'db>>,
    pub kind: MetaKind,

    // Provenance tracking (Phase 1 - optional for backward compatibility)
    pub created_at: Option<SourceRange<'db>>,
    pub origin: String,
}

impl<'db> MetaEntry<'db> {
    pub fn new(id: MetaId, ty: RcTy<'db>, arity: usize, kind: MetaKind) -> Self {
        MetaEntry {
            id,
            ty,
            arity,
            solution: None,
            kind,
            created_at: None,
            origin: "unknown".to_string(),
        }
    }

    pub fn with_provenance(
        id: MetaId,
        ty: RcTy<'db>,
        arity: usize,
        kind: MetaKind,
        created_at: SourceRange<'db>,
        origin: String,
    ) -> Self {
        MetaEntry {
            id,
            ty,
            arity,
            solution: None,
            kind,
            created_at: Some(created_at),
            origin,
        }
    }

    pub fn is_solved(&self) -> bool {
        self.solution.is_some()
    }
}
