use hwml_core::{ty::RcTy, Name, RcSyntax, RcValue};

use crate::meta::MetaId;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct ConstraintId(pub u32);

/// Constraint kinds. Every equality constraint carries a witness meta that gets
/// solved to the common solution when both sides are found to be equal.
#[derive(Debug, Clone)]
pub enum Constraint<'db> {
    /// Homogeneous equality: `lhs = rhs : ty`.
    /// Both sides must have the same type `ty`.
    /// The `witness` meta is the anti-unification variable — when the
    /// constraint is solved (lhs = rhs), the witness gets solved to the common value.
    Eq {
        lhs: RcValue<'db>,
        rhs: RcValue<'db>,
        ty: RcTy<'db>,
        witness: MetaId,
        depth: usize,
    },
    /// Universe level inequality for McBride/Sterling shunting.
    LevelLeq {
        smaller: RcValue<'db>,
        larger: RcValue<'db>,
    },
    /// Type-directed dot resolution: `receiver.field_name`
    /// Suspended when receiver type is an unsolved metavariable.
    /// When the receiver type is solved to a concrete type constructor `T`,
    /// this resolves to `T/field_name` applied to the receiver.
    ResolveDot {
        /// The elaborated receiver value (e.g., `x`)
        receiver_val: RcSyntax<'db>,
        /// The receiver's type (may contain an unsolved metavariable)
        receiver_ty: RcTy<'db>,
        /// The field/method name to resolve (e.g., "foo")
        field_name: Name<'db>,
        /// Fresh metavariable for the resulting elaborated expression
        result_val_meta: MetaId,
        /// Fresh metavariable for the resulting type
        result_ty_meta: MetaId,
        /// Elaboration depth for proper context
        depth: usize,
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
        ConstraintEntry {
            id,
            constraint,
            status: ConstraintStatus::Active,
        }
    }
}
