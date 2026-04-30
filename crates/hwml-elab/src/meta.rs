use hwml_core::{RcValue, ty::RcTy};

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct MetaId(pub u32);

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MetaKind {
    Term,
    UniverseLevel,
}

#[derive(Debug, Clone)]
pub struct MetaEntry<'db> {
    pub id: MetaId,
    pub ty: RcTy<'db>,
    pub arity: usize,
    pub solution: Option<RcValue<'db>>,
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
