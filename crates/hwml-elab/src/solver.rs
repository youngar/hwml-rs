use std::rc::Rc;

use hwml_core::{RcValue, Value, ty::Ty, val::GlobalEnv};

use crate::{
    constraint::{Constraint, ConstraintId, ConstraintStatus},
    error::ElabError,
    meta::{MetaId, MetaKind},
    state::SolverState,
    unify::{UnifyResult, Unifier},
};

pub struct Solver<'a, 'db> {
    pub state: &'a mut SolverState<'db>,
    pub global: &'db GlobalEnv<'db>,
}

#[derive(Debug)]
pub enum SolveError<'db> {
    Elab(ElabError<'db>),
    NoProgress,
}

impl<'db> From<ElabError<'db>> for SolveError<'db> {
    fn from(e: ElabError<'db>) -> Self {
        SolveError::Elab(e)
    }
}

impl<'a, 'db> Solver<'a, 'db> {
    pub fn new(state: &'a mut SolverState<'db>, global: &'db GlobalEnv<'db>) -> Self {
        Solver { state, global }
    }

    /// Run flat constraint solver until queue empty or no progress.
    pub fn run(&mut self) -> Result<(), SolveError<'db>> {
        loop {
            let cid = match self.state.pop_active() {
                Some(c) => c,
                None => break,
            };
            let entry = match self.state.constraint(cid) {
                Some(e) => e.clone(),
                None => continue,
            };
            if matches!(entry.status, ConstraintStatus::Solved) {
                continue;
            }
            self.step_constraint(cid, &entry.constraint)?;
        }
        Ok(())
    }

    fn step_constraint(
        &mut self,
        cid: ConstraintId,
        constraint: &Constraint<'db>,
    ) -> Result<(), SolveError<'db>> {
        match constraint.clone() {
            Constraint::HetEq { lhs, lhs_ty, rhs, rhs_ty, depth, .. } => {
                self.step_het_eq(cid, lhs, lhs_ty, rhs, rhs_ty, depth)
            }
            Constraint::LevelLeq { smaller, larger } => {
                self.step_level_leq(cid, smaller, larger)
            }
        }
    }

    fn step_het_eq(
        &mut self,
        cid: ConstraintId,
        lhs: RcValue<'db>,
        lhs_ty: hwml_core::ty::RcTy<'db>,
        rhs: RcValue<'db>,
        rhs_ty: hwml_core::ty::RcTy<'db>,
        depth: usize,
    ) -> Result<(), SolveError<'db>> {
        let result = {
            let mut unifier = Unifier::new(self.global, self.state, depth);
            unifier.unify(lhs.clone(), lhs_ty, rhs.clone(), rhs_ty)
        };
        match result? {
            UnifyResult::Solved => {
                self.state.mark_solved(cid);
            }
            UnifyResult::Stuck => {
                // Pi injectivity: decompose PiCode(A,B)=PiCode(A',B') into two sub-constraints.
                if self.try_pi_injectivity(cid, &lhs, &rhs, depth) {
                    return Ok(());
                }
                let mut blocking = Vec::new();
                collect_flex_heads(self.state, &lhs, &mut blocking);
                collect_flex_heads(self.state, &rhs, &mut blocking);
                blocking.dedup();
                if !blocking.is_empty() {
                    self.state.block_on(cid, &blocking);
                }
            }
        }
        Ok(())
    }

    /// Pi injectivity: if both sides are PiCode, split into dom + cod sub-constraints.
    /// Returns true if decomposition was applied (original constraint marked solved).
    fn try_pi_injectivity(
        &mut self,
        cid: ConstraintId,
        lhs: &RcValue<'db>,
        rhs: &RcValue<'db>,
        depth: usize,
    ) -> bool {
        let lhs = force_value(self.state, self.global, lhs.clone());
        let rhs = force_value(self.state, self.global, rhs.clone());

        if let (Value::PiCode(d1, c1), Value::PiCode(d2, c2)) = (lhs.as_ref(), rhs.as_ref()) {
            let universe_ty: Rc<Ty<'db>> = Rc::new(Ty::UniverseType);

            let w1 = self.state.fresh_meta(universe_ty.clone(), depth, MetaKind::Term);
            self.state.emit_het_eq(
                d1.clone(), universe_ty.clone(),
                d2.clone(), universe_ty.clone(),
                depth, w1,
            );

            let var: RcValue<'db> = Rc::new(Value::variable(hwml_core::Level::new(depth), d1.clone()));
            let cod1 = c1.apply(self.global, &var);
            let cod2 = c2.apply(self.global, &var);
            let w2 = self.state.fresh_meta(universe_ty.clone(), depth + 1, MetaKind::Term);
            self.state.emit_het_eq(
                cod1, universe_ty.clone(),
                cod2, universe_ty,
                depth + 1, w2,
            );

            self.state.mark_solved(cid);
            true
        } else {
            false
        }
    }

    fn step_level_leq(
        &mut self,
        cid: ConstraintId,
        smaller: RcValue<'db>,
        larger: RcValue<'db>,
    ) -> Result<(), SolveError<'db>> {
        let smaller = force_value(self.state, self.global, smaller);
        let larger = force_value(self.state, self.global, larger);

        match (smaller.as_ref(), larger.as_ref()) {
            (Value::UniverseCode(n), Value::UniverseCode(m)) => {
                if n <= m {
                    self.state.mark_solved(cid);
                }
                // If n > m, the constraint is inconsistent — leave blocked (zonk will fail).
            }
            (Value::UniverseCode(_), Value::Flex(flex)) => {
                let id = MetaId(flex.head.id.local_index as u32);
                // Block on the Flex meta until zonk resolves it.
                self.state.block_on(cid, &[id]);
            }
            (Value::Flex(flex), _) => {
                let id = MetaId(flex.head.id.local_index as u32);
                self.state.block_on(cid, &[id]);
            }
            _ => {
                // Unknown shape: leave active for now.
            }
        }
        Ok(())
    }
}

/// Force the top-level Flex (one step) if solved.
fn force_value<'db>(
    state: &SolverState<'db>,
    global: &GlobalEnv<'db>,
    val: RcValue<'db>,
) -> RcValue<'db> {
    if let Value::Flex(flex) = val.as_ref() {
        if let Some(forced) = state.force_flex(global, flex) {
            return forced;
        }
    }
    val
}

/// Collect unsolved Flex meta IDs from the top-level of a value (one level deep).
fn collect_flex_heads<'db>(
    state: &SolverState<'db>,
    val: &Value<'db>,
    out: &mut Vec<MetaId>,
) {
    if let Value::Flex(flex) = val {
        let id = MetaId(flex.head.id.local_index as u32);
        if state.meta_solution(id).is_none() {
            out.push(id);
        }
    }
}

