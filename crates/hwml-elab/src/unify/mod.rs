pub mod pattern;

use hwml_core::{RcValue, ty::RcTy, val::GlobalEnv};

use crate::{error::ElabError, state::SolverState};

pub enum UnifyResult {
    Solved,
    Stuck,
}

pub struct Unifier<'a, 'db> {
    pub global: &'db GlobalEnv<'db>,
    pub state: &'a mut SolverState<'db>,
    pub depth: usize,
}

impl<'a, 'db> Unifier<'a, 'db> {
    pub fn new(
        global: &'db GlobalEnv<'db>,
        state: &'a mut SolverState<'db>,
        depth: usize,
    ) -> Self {
        Unifier { global, state, depth }
    }

    /// Typed, eta-aware unification.
    /// For heterogeneous case: first unify types, then values.
    pub fn unify(
        &mut self,
        lhs: RcValue<'db>,
        lhs_ty: RcTy<'db>,
        rhs: RcValue<'db>,
        rhs_ty: RcTy<'db>,
    ) -> Result<UnifyResult, ElabError<'db>> {
        todo!("unify: Phase 2")
    }

    /// Homogeneous unification at a known type.
    pub fn unify_at(
        &mut self,
        lhs: RcValue<'db>,
        rhs: RcValue<'db>,
        ty: RcTy<'db>,
    ) -> Result<UnifyResult, ElabError<'db>> {
        todo!("unify_at: Phase 2")
    }

    /// Structural unification of type codes (no eta at UniverseType).
    pub fn unify_type_codes(
        &mut self,
        lhs: RcValue<'db>,
        rhs: RcValue<'db>,
    ) -> Result<UnifyResult, ElabError<'db>> {
        todo!("unify_type_codes: Phase 2")
    }
}
