use std::collections::{HashMap, VecDeque};

use hwml_core::{RcValue, ty::RcTy, val::GlobalEnv};

use crate::{
    constraint::{Constraint, ConstraintEntry, ConstraintId, ConstraintStatus},
    error::ElabError,
    meta::{MetaEntry, MetaId, MetaKind},
};

pub struct SolverState<'db> {
    next_meta: u32,
    next_constraint: u32,
    pub(crate) metas: HashMap<MetaId, MetaEntry<'db>>,
    pub(crate) constraints: HashMap<ConstraintId, ConstraintEntry<'db>>,
    pub(crate) active_queue: VecDeque<ConstraintId>,
    /// Which constraints to wake when a meta is solved.
    pub(crate) wake_on: HashMap<MetaId, Vec<ConstraintId>>,
}

impl<'db> SolverState<'db> {
    pub fn new() -> Self {
        SolverState {
            next_meta: 0,
            next_constraint: 0,
            metas: HashMap::new(),
            constraints: HashMap::new(),
            active_queue: VecDeque::new(),
            wake_on: HashMap::new(),
        }
    }

    pub fn fresh_meta(&mut self, ty: RcTy<'db>, arity: usize, kind: MetaKind) -> MetaId {
        let id = MetaId(self.next_meta);
        self.next_meta += 1;
        self.metas.insert(id, MetaEntry::new(id, ty, arity, kind));
        id
    }

    pub fn meta(&self, id: MetaId) -> Option<&MetaEntry<'db>> {
        self.metas.get(&id)
    }

    pub fn meta_solution(&self, id: MetaId) -> Option<&RcValue<'db>> {
        self.metas.get(&id)?.solution.as_ref()
    }

    pub fn solve_meta(
        &mut self,
        id: MetaId,
        val: RcValue<'db>,
    ) -> Result<(), ElabError<'db>> {
        let entry = self.metas.get_mut(&id).ok_or(ElabError::UnsolvedMeta { meta: id, span: None })?;
        if entry.solution.is_some() {
            return Err(ElabError::MetaAlreadySolved { meta: id });
        }
        entry.solution = Some(val);
        self.wake(id);
        Ok(())
    }

    /// Attempt to reduce a Flex to its value if its meta is solved.
    /// Returns `None` when unsolved; full evaluation deferred to Phase 2.
    pub fn force_flex(
        &self,
        _global: &GlobalEnv<'db>,
        flex: &hwml_core::val::Flex<'db>,
    ) -> Option<RcValue<'db>> {
        let id = MetaId(flex.head.id.local_index as u32);
        let _solution = self.metas.get(&id)?.solution.as_ref()?;
        // Full substitution + spine-reduction implemented in Phase 2.
        todo!("force_flex: Phase 2")
    }

    /// Create a HetEq constraint together with its witness meta atomically.
    pub fn emit_het_eq(
        &mut self,
        lhs: RcValue<'db>,
        lhs_ty: RcTy<'db>,
        rhs: RcValue<'db>,
        rhs_ty: RcTy<'db>,
        depth: usize,
    ) -> ConstraintId {
        let witness = self.fresh_meta(lhs_ty.clone(), depth, MetaKind::Term);
        let cid = ConstraintId(self.next_constraint);
        self.next_constraint += 1;
        let constraint = Constraint::HetEq { lhs, lhs_ty, rhs, rhs_ty, witness, depth };
        self.constraints.insert(cid, ConstraintEntry::new(cid, constraint));
        self.active_queue.push_back(cid);
        cid
    }

    pub fn emit_level_leq(
        &mut self,
        smaller: RcValue<'db>,
        larger: RcValue<'db>,
    ) -> ConstraintId {
        let cid = ConstraintId(self.next_constraint);
        self.next_constraint += 1;
        let constraint = Constraint::LevelLeq { smaller, larger };
        self.constraints.insert(cid, ConstraintEntry::new(cid, constraint));
        self.active_queue.push_back(cid);
        cid
    }

    pub fn pop_active(&mut self) -> Option<ConstraintId> {
        self.active_queue.pop_front()
    }

    pub fn mark_solved(&mut self, cid: ConstraintId) {
        if let Some(entry) = self.constraints.get_mut(&cid) {
            entry.status = ConstraintStatus::Solved;
        }
    }

    pub fn block_on(&mut self, cid: ConstraintId, metas: &[MetaId]) {
        if let Some(entry) = self.constraints.get_mut(&cid) {
            entry.status = ConstraintStatus::Blocked(metas.to_vec());
        }
        for &m in metas {
            self.wake_on.entry(m).or_default().push(cid);
        }
    }

    pub fn re_queue(&mut self, cid: ConstraintId) {
        if let Some(entry) = self.constraints.get_mut(&cid) {
            entry.status = ConstraintStatus::Active;
        }
        self.active_queue.push_back(cid);
    }

    pub fn constraint(&self, id: ConstraintId) -> Option<&ConstraintEntry<'db>> {
        self.constraints.get(&id)
    }

    pub fn constraint_mut(&mut self, id: ConstraintId) -> Option<&mut ConstraintEntry<'db>> {
        self.constraints.get_mut(&id)
    }

    pub fn iter_metas(&self) -> impl Iterator<Item = (&MetaId, &MetaEntry<'db>)> {
        self.metas.iter()
    }

    pub fn iter_constraints(&self) -> impl Iterator<Item = (&ConstraintId, &ConstraintEntry<'db>)> {
        self.constraints.iter()
    }

    pub fn active_count(&self) -> usize {
        self.active_queue.len()
    }

    fn wake(&mut self, meta: MetaId) {
        if let Some(blocked) = self.wake_on.remove(&meta) {
            for cid in blocked {
                self.re_queue(cid);
            }
        }
    }
}

impl<'db> Default for SolverState<'db> {
    fn default() -> Self {
        Self::new()
    }
}
