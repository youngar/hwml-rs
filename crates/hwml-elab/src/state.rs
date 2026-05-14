use std::{
    collections::{HashMap, VecDeque},
    rc::Rc,
};

use hwml_core::{
    eval,
    ty::{RcTy, Ty},
    val::GlobalEnv,
    RcSyntax, RcValue, Value,
};

use crate::{
    constraint::{Constraint, ConstraintEntry, ConstraintId, ConstraintStatus},
    error::ElabError,
    meta::{MetaEntry, MetaId, MetaKind, MetaSolution},
    subst,
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

    /// Create a fresh metavariable without provenance information (for backward compatibility)
    pub fn fresh_meta(&mut self, ty: RcTy<'db>, arity: usize, kind: MetaKind) -> MetaId {
        let id = MetaId(self.next_meta);
        self.next_meta += 1;
        self.metas.insert(id, MetaEntry::new(id, ty, arity, kind));
        id
    }

    /// Create a fresh metavariable with provenance information
    pub fn fresh_meta_with_provenance(
        &mut self,
        ty: RcTy<'db>,
        arity: usize,
        kind: MetaKind,
        created_at: hwml_core::SourceRange<'db>,
        origin: String,
    ) -> MetaId {
        let id = MetaId(self.next_meta);
        self.next_meta += 1;
        self.metas.insert(
            id,
            MetaEntry::with_provenance(id, ty, arity, kind, created_at, origin),
        );
        id
    }

    pub fn meta(&self, id: MetaId) -> Option<&MetaEntry<'db>> {
        self.metas.get(&id)
    }

    /// Returns the cached value of a solved meta (for unification / force_flex).
    pub fn meta_solution(&self, id: MetaId) -> Option<&RcValue<'db>> {
        self.metas.get(&id)?.solution.as_ref().map(|s| &s.value)
    }

    /// Returns the syntax of a solved meta (for zonking / post-hoc verification).
    pub fn meta_solution_syntax(&self, id: MetaId) -> Option<&RcSyntax<'db>> {
        self.metas.get(&id)?.solution.as_ref().map(|s| &s.syntax)
    }

    pub fn solve_meta(
        &mut self,
        id: MetaId,
        syn: RcSyntax<'db>,
        val: RcValue<'db>,
    ) -> Result<(), ElabError<'db>> {
        let entry = self.metas.get_mut(&id).ok_or(ElabError::UnsolvedMeta {
            meta: id,
            span: None,
            elab_backtrace: Vec::new(),
        })?;
        if entry.solution.is_some() {
            return Err(ElabError::MetaAlreadySolved {
                meta: id,
                elab_backtrace: Vec::new(),
            });
        }
        // Kind consistency: UniverseLevel metas must resolve to a universe code or flex.
        if matches!(entry.kind, MetaKind::UniverseLevel) {
            match val.as_ref() {
                Value::UniverseCode(_) | Value::Flex(_) => {}
                _ => {
                    return Err(ElabError::TypeMismatch {
                        expected: Rc::new(Ty::UniverseType),
                        actual: entry.ty.clone(),
                        span: None,
                        elab_backtrace: Vec::new(),
                    });
                }
            }
        }
        entry.solution = Some(MetaSolution {
            syntax: syn,
            value: val,
        });
        self.wake(id);
        Ok(())
    }

    /// Reduce a Flex to its value if the meta is solved.
    ///
    /// Applies the solution (in meta's scope, levels 0..arity-1) to the actual
    /// local env in the Flex, then runs the remaining spine.
    pub fn force_flex(
        &self,
        global: &GlobalEnv<'db>,
        flex: &hwml_core::val::Flex<'db>,
    ) -> Option<RcValue<'db>> {
        let id = MetaId(flex.head.id.local_index as u32);
        let solution = self.metas.get(&id)?.solution.as_ref()?.value.clone();
        // Substitute meta parameters (levels 0..arity-1) with actual local env values.
        let substituted = subst::subst_value(global, &solution, &flex.head.local).ok()?;
        // Run remaining spine eliminations.
        eval::run_spine(global, substituted, &flex.spine).ok()
    }

    /// Create a homogeneous equality constraint.
    ///
    /// Emits constraint: `lhs = rhs : ty`.
    /// The witness meta is created internally and will be solved to the common value
    /// when `lhs = rhs` is determined to be definitionally equal.
    ///
    /// This is the only way to create equality constraints. The witness meta is an
    /// internal implementation detail and is not returned to the caller.
    pub fn emit_eq(
        &mut self,
        lhs: RcValue<'db>,
        rhs: RcValue<'db>,
        ty: RcTy<'db>,
        depth: usize,
    ) -> ConstraintId {
        self.emit_eq_with_loc(lhs, rhs, ty, depth, None)
    }

    /// Create a homogeneous equality constraint with optional location information.
    ///
    /// This is the same as `emit_eq` but accepts an optional location for the witness metavariable.
    pub fn emit_eq_with_loc(
        &mut self,
        lhs: RcValue<'db>,
        rhs: RcValue<'db>,
        ty: RcTy<'db>,
        depth: usize,
        loc: Option<hwml_core::SourceRange<'db>>,
    ) -> ConstraintId {
        // Create witness meta internally for anti-unification.
        let witness = if let Some(loc) = loc {
            self.fresh_meta_with_provenance(
                ty.clone(),
                depth,
                MetaKind::Term,
                loc.clone(),
                format!("witness for equality constraint at {:?}", loc),
            )
        } else {
            self.fresh_meta(ty.clone(), depth, MetaKind::Term)
        };

        let cid = ConstraintId(self.next_constraint);
        self.next_constraint += 1;
        let constraint = Constraint::Eq {
            lhs,
            rhs,
            ty,
            witness,
            depth,
        };
        self.constraints
            .insert(cid, ConstraintEntry::new(cid, constraint));
        self.active_queue.push_back(cid);
        cid
    }

    pub fn emit_level_leq(&mut self, smaller: RcValue<'db>, larger: RcValue<'db>) -> ConstraintId {
        let cid = ConstraintId(self.next_constraint);
        self.next_constraint += 1;
        let constraint = Constraint::LevelLeq { smaller, larger };
        self.constraints
            .insert(cid, ConstraintEntry::new(cid, constraint));
        self.active_queue.push_back(cid);
        cid
    }

    pub fn emit_resolve_dot(
        &mut self,
        receiver_val: hwml_core::RcSyntax<'db>,
        receiver_ty: RcTy<'db>,
        field_name: hwml_core::Name<'db>,
        result_val_meta: crate::meta::MetaId,
        result_ty_meta: crate::meta::MetaId,
        depth: usize,
    ) -> ConstraintId {
        let cid = ConstraintId(self.next_constraint);
        self.next_constraint += 1;
        let constraint = Constraint::ResolveDot {
            receiver_val,
            receiver_ty,
            field_name,
            result_val_meta,
            result_ty_meta,
            depth,
        };
        self.constraints
            .insert(cid, ConstraintEntry::new(cid, constraint));
        self.active_queue.push_back(cid);
        cid
    }

    /// Emit a postponed check constraint (DOE).
    ///
    /// This is used when checking an expression against a meta-headed type.
    /// The check is postponed until the meta is solved.
    pub fn emit_postponed_check(
        &mut self,
        expr: Box<hwml_surface::Expression>,
        expected_ty: RcTy<'db>,
        ctx: crate::ctx::ElabCtx<'db>,
        placeholder: crate::meta::MetaId,
        depth: usize,
    ) -> ConstraintId {
        let cid = ConstraintId(self.next_constraint);
        self.next_constraint += 1;
        let constraint = Constraint::PostponedCheck {
            expr,
            expected_ty,
            ctx,
            placeholder,
            depth,
        };
        self.constraints
            .insert(cid, ConstraintEntry::new(cid, constraint));
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
