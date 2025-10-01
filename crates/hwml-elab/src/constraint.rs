use hwml_core::syn::*;

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone, Hash)]
pub struct Constraint {
    pub data: ConstraintData,
}

impl Constraint {
    pub fn new(data: ConstraintData) -> Self {
        Self { data }
    }

    pub fn empty() -> Self {
        Self::new(ConstraintData::EmptyConstraint)
    }

    pub fn equality(lhs: RcSyntax, rhs: RcSyntax, ty: RcSyntax, meta: MetavariableId) -> Self {
        Self::new(ConstraintData::EqualityConstraint(EqualityConstraint {
            lhs,
            rhs,
            ty,
            meta,
        }))
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub enum ConstraintData {
    EmptyConstraint,
    EqualityConstraint(EqualityConstraint),
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct EqualityConstraint {
    pub lhs: RcSyntax,
    pub rhs: RcSyntax,
    pub ty: RcSyntax,
    pub meta: MetavariableId,
}
