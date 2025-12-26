use hwml_core::common::MetaVariableId;
use hwml_core::syn::*;

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone, Hash)]
pub struct Constraint<'db> {
    pub data: ConstraintData<'db>,
}

impl<'db> Constraint<'db> {
    pub fn new(data: ConstraintData<'db>) -> Self {
        Self { data }
    }

    pub fn empty() -> Self {
        Self::new(ConstraintData::EmptyConstraint)
    }

    pub fn equality(
        lhs: RcSyntax<'db>,
        rhs: RcSyntax<'db>,
        ty: RcSyntax<'db>,
        meta: MetaVariableId,
    ) -> Self {
        Self::new(ConstraintData::EqualityConstraint(EqualityConstraint {
            lhs,
            rhs,
            ty,
            meta,
        }))
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub enum ConstraintData<'db> {
    EmptyConstraint,
    EqualityConstraint(EqualityConstraint<'db>),
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct EqualityConstraint<'db> {
    pub lhs: RcSyntax<'db>,
    pub rhs: RcSyntax<'db>,
    pub ty: RcSyntax<'db>,
    pub meta: MetaVariableId,
}
