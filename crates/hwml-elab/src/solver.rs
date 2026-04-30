use std::rc::Rc;

use hwml_core::{
    Level, RcValue, Value,
    equal,
    eval,
    ty::{RcTy, Ty},
    val::{GlobalEnv, TransparentEnv},
};

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
        lhs_ty: RcTy<'db>,
        rhs: RcValue<'db>,
        rhs_ty: RcTy<'db>,
        depth: usize,
    ) -> Result<(), SolveError<'db>> {
        // Step 1: force both sides.
        let lhs_f = force_deep(self.state, self.global, lhs.clone());
        let rhs_f = force_deep(self.state, self.global, rhs.clone());

        // Step 2: identity — definitional equality check (no delta-reduction, no let env).
        if try_identity(self.global, depth, &lhs_f, &rhs_f, &lhs_ty) {
            self.state.mark_solved(cid);
            return Ok(());
        }

        // Step 3: run the unifier (handles eta, pattern unification, flex-rigid).
        let result = {
            let mut unifier = Unifier::new(self.global, self.state, depth);
            unifier.unify(lhs_f.clone(), lhs_ty.clone(), rhs_f.clone(), rhs_ty.clone())
        };
        match result? {
            UnifyResult::Solved => {
                self.state.mark_solved(cid);
                return Ok(());
            }
            UnifyResult::Stuck => {}
        }

        // Step 4: structural decomposition rules.

        // Pi injectivity: PiCode(A,B) = PiCode(A',B').
        if self.try_pi_injectivity(cid, &lhs_f, &rhs_f, depth) {
            return Ok(());
        }

        // Constructor injectivity: DataConstructor / TypeConstructor.
        if self.try_constructor_injectivity(cid, &lhs_f, &rhs_f, depth)? {
            return Ok(());
        }

        // Step 5: block on unsolved metas.
        let mut blocking = Vec::new();
        collect_flex_heads(self.state, &lhs_f, &mut blocking);
        collect_flex_heads(self.state, &rhs_f, &mut blocking);
        blocking.dedup();
        if !blocking.is_empty() {
            self.state.block_on(cid, &blocking);
        }
        Ok(())
    }

    // ─── Pi injectivity ───────────────────────────────────────────────────────

    fn try_pi_injectivity(
        &mut self,
        cid: ConstraintId,
        lhs: &RcValue<'db>,
        rhs: &RcValue<'db>,
        depth: usize,
    ) -> bool {
        if let (Value::PiCode(d1, c1), Value::PiCode(d2, c2)) = (lhs.as_ref(), rhs.as_ref()) {
            let universe_ty: RcTy<'db> = Rc::new(Ty::UniverseType);

            let w1 = self.state.fresh_meta(universe_ty.clone(), depth, MetaKind::Term);
            self.state.emit_het_eq(
                d1.clone(), universe_ty.clone(),
                d2.clone(), universe_ty.clone(),
                depth, w1,
            );

            let var: RcValue<'db> = Rc::new(Value::variable(Level::new(depth), d1.clone()));
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

    // ─── Constructor injectivity ──────────────────────────────────────────────

    /// Decompose `DataConstructor(c, args1) = DataConstructor(c, args2)` and
    /// `TypeConstructor(c, args1) = TypeConstructor(c, args2)` into per-argument constraints.
    /// Returns true if decomposition was applied; Err on hard mismatch.
    fn try_constructor_injectivity(
        &mut self,
        cid: ConstraintId,
        lhs: &RcValue<'db>,
        rhs: &RcValue<'db>,
        depth: usize,
    ) -> Result<bool, SolveError<'db>> {
        match (lhs.as_ref(), rhs.as_ref()) {
            (Value::DataConstructor(dc1), Value::DataConstructor(dc2)) => {
                if dc1.constructor != dc2.constructor {
                    return Err(SolveError::Elab(ElabError::UnificationFailure {
                        lhs: lhs.clone(),
                        rhs: rhs.clone(),
                        span: None,
                    }));
                }
                let args1: Vec<_> = dc1.iter().cloned().collect();
                let args2: Vec<_> = dc2.iter().cloned().collect();
                if args1.len() != args2.len() {
                    return Err(SolveError::Elab(ElabError::UnificationFailure {
                        lhs: lhs.clone(),
                        rhs: rhs.clone(),
                        span: None,
                    }));
                }

                // Look up constructor telescope for argument types.
                let arg_types = self.eval_dcon_telescope(dc1.constructor, &args1);

                self.emit_arg_constraints(&args1, &args2, &arg_types, depth);
                self.state.mark_solved(cid);
                Ok(true)
            }

            (Value::TypeConstructor(tc1), Value::TypeConstructor(tc2)) => {
                if tc1.constructor != tc2.constructor {
                    return Err(SolveError::Elab(ElabError::UnificationFailure {
                        lhs: lhs.clone(),
                        rhs: rhs.clone(),
                        span: None,
                    }));
                }
                let args1: Vec<_> = tc1.iter().cloned().collect();
                let args2: Vec<_> = tc2.iter().cloned().collect();
                if args1.len() != args2.len() {
                    return Err(SolveError::Elab(ElabError::UnificationFailure {
                        lhs: lhs.clone(),
                        rhs: rhs.clone(),
                        span: None,
                    }));
                }

                let arg_types = self.eval_tcon_telescope(tc1.constructor, &args1);

                self.emit_arg_constraints(&args1, &args2, &arg_types, depth);
                self.state.mark_solved(cid);
                Ok(true)
            }

            _ => Ok(false),
        }
    }

    /// Evaluate the telescope for a data constructor, yielding the type of each argument.
    /// Falls back to `Ty::UniverseType` for any args whose type can't be evaluated.
    fn eval_dcon_telescope(
        &self,
        constructor: hwml_core::QualifiedName<'db>,
        args: &[RcValue<'db>],
    ) -> Vec<RcTy<'db>> {
        let dummy: RcTy<'db> = Rc::new(Ty::UniverseType);
        let info = match self.global.data_constructor(constructor) {
            Ok(info) => info,
            Err(_) => return vec![dummy; args.len()],
        };
        eval_telescope_types(self.global, &info.arguments, args, dummy)
    }

    /// Evaluate the telescope for a type constructor.
    fn eval_tcon_telescope(
        &self,
        constructor: hwml_core::QualifiedName<'db>,
        args: &[RcValue<'db>],
    ) -> Vec<RcTy<'db>> {
        let dummy: RcTy<'db> = Rc::new(Ty::UniverseType);
        let info = match self.global.type_constructor(constructor) {
            Ok(info) => info,
            Err(_) => return vec![dummy; args.len()],
        };
        eval_telescope_types(self.global, &info.arguments, args, dummy)
    }

    /// Emit HetEq constraints for parallel argument lists.
    fn emit_arg_constraints(
        &mut self,
        args1: &[RcValue<'db>],
        args2: &[RcValue<'db>],
        arg_types: &[RcTy<'db>],
        depth: usize,
    ) {
        for i in 0..args1.len() {
            let ty = arg_types.get(i).cloned().unwrap_or_else(|| Rc::new(Ty::UniverseType));
            let w = self.state.fresh_meta(ty.clone(), depth, MetaKind::Term);
            self.state.emit_het_eq(
                args1[i].clone(), ty.clone(),
                args2[i].clone(), ty,
                depth, w,
            );
        }
    }

    // ─── LevelLeq ─────────────────────────────────────────────────────────────

    fn step_level_leq(
        &mut self,
        cid: ConstraintId,
        smaller: RcValue<'db>,
        larger: RcValue<'db>,
    ) -> Result<(), SolveError<'db>> {
        let smaller = force_deep(self.state, self.global, smaller);
        let larger = force_deep(self.state, self.global, larger);

        match (smaller.as_ref(), larger.as_ref()) {
            (Value::UniverseCode(n), Value::UniverseCode(m)) => {
                if n <= m {
                    self.state.mark_solved(cid);
                }
                // n > m: inconsistent — leave blocked, zonk will report error.
            }
            (Value::UniverseCode(_), Value::Flex(flex)) => {
                let id = MetaId(flex.head.id.local_index as u32);
                self.state.block_on(cid, &[id]);
            }
            (Value::Flex(flex), _) => {
                let id = MetaId(flex.head.id.local_index as u32);
                self.state.block_on(cid, &[id]);
            }
            _ => {}
        }
        Ok(())
    }
}

// ─── Helpers ──────────────────────────────────────────────────────────────────

/// Force top-level Flex recursively.
fn force_deep<'db>(
    state: &SolverState<'db>,
    global: &GlobalEnv<'db>,
    val: RcValue<'db>,
) -> RcValue<'db> {
    if let Value::Flex(flex) = val.as_ref() {
        if let Some(forced) = state.force_flex(global, flex) {
            return force_deep(state, global, forced);
        }
    }
    val
}

/// Attempt a definitional equality check via hwml_core::equal::equate.
/// Uses an empty TransparentEnv (no let-binding unfolding in solver scope).
/// Returns true if both sides are definitionally equal.
fn try_identity<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    lhs: &Value<'db>,
    rhs: &Value<'db>,
    lhs_ty: &Ty<'db>,
) -> bool {
    // Convert Ty to Value for equate's type argument.
    let ty_val: RcValue<'db> = match lhs_ty {
        Ty::El(code) => code.clone(),
        Ty::UniverseType => Rc::new(Value::UniverseCode(0)),
        _ => return false,
    };
    let transparent = TransparentEnv::new();
    equal::equate(global, &transparent, depth, lhs, rhs, &ty_val).is_ok()
}

/// Collect unsolved Flex meta IDs from the top-level of a value.
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

/// Evaluate telescope bindings against preceding argument values.
/// Returns `Ty::El(T_i)` for each position where evaluation succeeds,
/// falling back to `dummy` otherwise.
fn eval_telescope_types<'db>(
    global: &GlobalEnv<'db>,
    telescope: &hwml_core::syn::Telescope<'db>,
    preceding_args: &[RcValue<'db>],
    dummy: RcTy<'db>,
) -> Vec<RcTy<'db>> {
    // eval_telescope starts with an empty LocalEnv, pushes params first, then evaluates.
    // We only want the types up to preceding_args.len() positions.
    let n = telescope.len().min(preceding_args.len());
    match eval::eval_telescope(global, preceding_args[..n].iter().cloned(), telescope) {
        Ok(sem) => sem
            .types
            .into_iter()
            .map(|ty_val| Rc::new(Ty::El(ty_val)))
            .collect(),
        Err(_) => vec![dummy; preceding_args.len()],
    }
}
