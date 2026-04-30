use hwml_core::{RcValue, ty::RcTy};

use crate::meta::MetaId;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct ConstraintId(pub u32);

/// Constraint kinds. Every equality constraint carries an ExEl-style witness
/// meta: the "anti-unification meta" that gets solved to the common solution,
/// preventing commitment to a specific direction before the solver is ready.
#[derive(Debug, Clone)]
pub enum Constraint<'db> {
    /// Heterogeneous equality (tog JmEq): `lhs : lhs_ty ≡ rhs : rhs_ty`.
    /// When `lhs_ty = rhs_ty` this reduces to standard homogeneous equality.
    /// `witness` is the ExEl anti-unification meta — solved alongside `lhs`.
    HetEq {
        lhs: RcValue<'db>,
        lhs_ty: RcTy<'db>,
        rhs: RcValue<'db>,
        rhs_ty: RcTy<'db>,
        witness: MetaId,
        depth: usize,
    },
    /// Universe level inequality for McBride/Sterling shunting.
    LevelLeq {
        smaller: RcValue<'db>,
        larger: RcValue<'db>,
    },
}

#[derive(Debug, Clone)]
pub enum ConstraintStatus {
    Active,
    /// Blocked waiting for these metas to be solved before retrying.
    Blocked(Vec<MetaId>),
    Solved,
}

#[derive(Debug, Clone)]
pub struct ConstraintEntry<'db> {
    pub id: ConstraintId,
    pub constraint: Constraint<'db>,
    pub status: ConstraintStatus,
}

impl<'db> ConstraintEntry<'db> {
    pub fn new(id: ConstraintId, constraint: Constraint<'db>) -> Self {
        ConstraintEntry { id, constraint, status: ConstraintStatus::Active }
    }
}
