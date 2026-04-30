use hwml_core::{RcSyntax, RcValue, ty::RcTy};

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
}

impl<'db> MetaEntry<'db> {
    pub fn new(id: MetaId, ty: RcTy<'db>, arity: usize, kind: MetaKind) -> Self {
        MetaEntry { id, ty, arity, solution: None, kind }
    }

    pub fn is_solved(&self) -> bool {
        self.solution.is_some()
    }
}
