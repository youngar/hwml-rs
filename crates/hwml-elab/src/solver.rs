use std::rc::Rc;

use hwml_core::{
    common::Icit,
    equal, eval,
    quote::type_quote,
    ty::{RcTy, Ty},
    val::{GlobalEnv, TransparentEnv},
    Level, RcValue, Value,
};

use crate::{
    constraint::{Constraint, ConstraintId, ConstraintStatus},
    ctx::ElabCtx,
    error::ElabError,
    meta::MetaId,
    state::SolverState,
    unify::{Unifier, UnifyResult},
};

/// A postponed check that is ready to be elaborated.
///
/// The solver identifies postponed checks whose expected type is no longer
/// meta-headed, packages them into this struct, and returns them to the caller.
/// The caller then creates an Elaborator and runs the check.
///
/// This pattern avoids the borrowing conflict where both Solver and Elaborator
/// need `&mut SolverState`.
#[derive(Debug, Clone)]
pub struct ReadyCheck<'db> {
    /// The surface expression to check
    pub expr: Box<hwml_surface::Expression>,
    /// The concrete expected type (no longer meta-headed)
    pub expected_ty: RcTy<'db>,
    /// Captured elaboration context (local variables)
    pub ctx: ElabCtx<'db>,
    /// Placeholder meta to solve with the result
    pub placeholder: MetaId,
    /// Elaboration depth for proper scoping
    pub depth: usize,
}

pub struct Solver<'a, 'db> {
    pub state: &'a mut SolverState<'db>,
    pub global: &'a GlobalEnv<'db>,
    pub db: &'db dyn salsa::Database,
    /// Postponed checks that are ready to elaborate
    ready_checks: Vec<ReadyCheck<'db>>,
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
    pub fn new(
        state: &'a mut SolverState<'db>,
        global: &'a GlobalEnv<'db>,
        db: &'db dyn salsa::Database,
    ) -> Self {
        Solver {
            state,
            global,
            db,
            ready_checks: Vec::new(),
        }
    }

    /// Run flat constraint solver until queue empty or no progress.
    ///
    /// Returns a list of postponed checks that are ready to elaborate.
    /// The caller should process these by creating an Elaborator and running
    /// the checks, then calling `run()` again to process any new constraints.
    pub fn run(&mut self) -> Result<Vec<ReadyCheck<'db>>, SolveError<'db>> {
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

        // Return collected ready checks
        Ok(std::mem::take(&mut self.ready_checks))
    }

    fn step_constraint(
        &mut self,
        cid: ConstraintId,
        constraint: &Constraint<'db>,
    ) -> Result<(), SolveError<'db>> {
        match constraint.clone() {
            Constraint::Eq {
                lhs,
                rhs,
                ty,
                witness,
                depth,
            } => self.step_eq(cid, lhs, rhs, ty, witness, depth),
            Constraint::LevelLeq { smaller, larger } => self.step_level_leq(cid, smaller, larger),
            Constraint::ResolveDot {
                receiver_val,
                receiver_ty,
                field_name,
                result_val_meta,
                result_ty_meta,
                depth,
            } => self.step_resolve_dot(
                cid,
                receiver_val,
                receiver_ty,
                field_name,
                result_val_meta,
                result_ty_meta,
                depth,
            ),
            Constraint::PostponedCheck {
                expr,
                expected_ty,
                ctx,
                placeholder,
                depth,
            } => self.step_postponed_check(cid, expr, expected_ty, ctx, placeholder, depth),
        }
    }

    /// Solve homogeneous equality constraint: `lhs = rhs : ty`.
    ///
    /// When lhs and rhs are definitionally equal, we solve the witness meta to
    /// the common value (anti-unification).
    fn step_eq(
        &mut self,
        cid: ConstraintId,
        lhs: RcValue<'db>,
        rhs: RcValue<'db>,
        ty: RcTy<'db>,
        witness: MetaId,
        depth: usize,
    ) -> Result<(), SolveError<'db>> {
        // Step 1: force both sides
        let lhs_f = force_deep(self.state, self.global, lhs.clone());
        let rhs_f = force_deep(self.state, self.global, rhs.clone());
        let ty_f = force_ty(self.state, self.global, ty.clone());

        // Step 2: identity check — if definitionally equal, solve witness and mark solved
        if try_identity(self.global, depth, &lhs_f, &rhs_f, &ty_f) {
            // Solve the witness meta to the common value (anti-unification).
            // Convert lhs_f back to syntax for the meta solution.
            if let Ok(lhs_syntax) = type_quote(self.db, self.global, depth, &lhs_f) {
                let _ = self.state.solve_meta(witness, lhs_syntax, lhs_f.clone());
            }
            self.state.mark_solved(cid);
            return Ok(());
        }

        // Step 3: run the unifier (handles eta, pattern unification, flex-rigid)
        // Note: unifier now expects homogeneous equality (same type for both sides)
        let result = {
            let mut unifier = Unifier::new(self.db, self.global, self.state, depth);
            unifier.unify(lhs_f.clone(), rhs_f.clone(), ty_f.clone())
        };
        match result? {
            UnifyResult::Solved => {
                // Unification solved metas; try identity check again
                let lhs_f2 = force_deep(self.state, self.global, lhs_f.clone());
                let rhs_f2 = force_deep(self.state, self.global, rhs_f.clone());
                if try_identity(self.global, depth, &lhs_f2, &rhs_f2, &ty_f) {
                    if let Ok(lhs_syntax) = type_quote(self.db, self.global, depth, &lhs_f2) {
                        let _ = self.state.solve_meta(witness, lhs_syntax, lhs_f2);
                    }
                    self.state.mark_solved(cid);
                }
                return Ok(());
            }
            UnifyResult::Stuck => {}
        }

        // Step 4: structural decomposition rules

        // Pi injectivity: PiCode(A,B) = PiCode(A',B').
        if self.try_pi_injectivity(cid, &lhs_f, &rhs_f, depth) {
            return Ok(());
        }

        // Constructor injectivity: DataConstructor / TypeConstructor.
        if self.try_constructor_injectivity(cid, &lhs_f, &rhs_f, depth)? {
            return Ok(());
        }

        // Step 5: block on unsolved metas
        let mut blocking = Vec::new();
        collect_flex_heads(self.state, &lhs_f, &mut blocking);
        collect_flex_heads(self.state, &rhs_f, &mut blocking);
        collect_flex_heads_ty(self.state, &ty_f, &mut blocking);
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
        if let (Value::PiCode(d1, _icit1, c1), Value::PiCode(d2, _icit2, c2)) =
            (lhs.as_ref(), rhs.as_ref())
        {
            let universe_ty: RcTy<'db> = Rc::new(Ty::UniverseType);

            // Emit: d1 = d2 : Type (domain equality)
            self.state
                .emit_eq(d1.clone(), d2.clone(), universe_ty.clone(), depth);

            // Emit: cod1 = cod2 : Type (codomain equality under fresh variable)
            let var: RcValue<'db> = Rc::new(Value::variable(Level::new(depth), d1.clone()));
            let cod1 = c1.apply(self.global, &var);
            let cod2 = c2.apply(self.global, &var);
            self.state.emit_eq(cod1, cod2, universe_ty, depth + 1);

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
                        elab_backtrace: Vec::new(),
                    }));
                }
                let args1: Vec<_> = dc1.iter().cloned().collect();
                let args2: Vec<_> = dc2.iter().cloned().collect();
                if args1.len() != args2.len() {
                    return Err(SolveError::Elab(ElabError::UnificationFailure {
                        lhs: lhs.clone(),
                        rhs: rhs.clone(),
                        span: None,
                        elab_backtrace: Vec::new(),
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
                        elab_backtrace: Vec::new(),
                    }));
                }
                let args1: Vec<_> = tc1.iter().cloned().collect();
                let args2: Vec<_> = tc2.iter().cloned().collect();
                if args1.len() != args2.len() {
                    return Err(SolveError::Elab(ElabError::UnificationFailure {
                        lhs: lhs.clone(),
                        rhs: rhs.clone(),
                        span: None,
                        elab_backtrace: Vec::new(),
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

    /// Emit homogeneous equality constraints for parallel argument lists.
    fn emit_arg_constraints(
        &mut self,
        args1: &[RcValue<'db>],
        args2: &[RcValue<'db>],
        arg_types: &[RcTy<'db>],
        depth: usize,
    ) {
        for i in 0..args1.len() {
            let ty = arg_types
                .get(i)
                .cloned()
                .unwrap_or_else(|| Rc::new(Ty::UniverseType));
            // emit_eq creates witness meta internally
            self.state
                .emit_eq(args1[i].clone(), args2[i].clone(), ty, depth);
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

    // ─── ResolveDot ───────────────────────────────────────────────────────────

    #[allow(clippy::too_many_arguments)]
    fn step_resolve_dot(
        &mut self,
        cid: ConstraintId,
        receiver_val: hwml_core::RcSyntax<'db>,
        receiver_ty: RcTy<'db>,
        field_name: hwml_core::Name<'db>,
        result_val_meta: MetaId,
        result_ty_meta: MetaId,
        depth: usize,
    ) -> Result<(), SolveError<'db>> {
        use hwml_core::QualifiedName;

        // Force the receiver type to resolve metavariables
        let forced_ty = force_ty(self.state, self.global, receiver_ty.clone());

        match forced_ty.as_ref() {
            Ty::El(code) => {
                let forced_code = force_deep(self.state, self.global, code.clone());

                match forced_code.as_ref() {
                    Value::TypeConstructor(tc) => {
                        // Concrete type! Resolve field_name in the type's namespace
                        let type_name = tc.constructor;

                        // Construct the qualified field name: TypeNamespace/field_name
                        let field_qualified =
                            QualifiedName::qualify_path(self.db, Some(type_name), &[field_name])
                                .ok_or_else(|| {
                                    SolveError::Elab(ElabError::NotInScope {
                                        name: format!(
                                            "{}.{}",
                                            type_name.to_string(self.db),
                                            field_name.to_string(self.db)
                                        ),
                                        span: None,
                                        elab_backtrace: Vec::new(),
                                    })
                                })?;

                        // Look up the field in the global environment
                        let field_info = self.global.constant(field_qualified).map_err(|_| {
                            SolveError::Elab(ElabError::NotInScope {
                                name: format!(
                                    "{}.{}",
                                    type_name.to_string(self.db),
                                    field_name.to_string(self.db)
                                ),
                                span: None,
                                elab_backtrace: Vec::new(),
                            })
                        })?;

                        // Build the result: application of field to receiver
                        let field_syn = hwml_core::Syntax::constant_rc(field_qualified);
                        let result_syn = hwml_core::Syntax::application_rc(
                            field_syn,
                            receiver_val,
                            Icit::Explicit,
                        );

                        // Evaluate the field type
                        let field_ty_val = eval::substitute(
                            self.global,
                            &field_info.ty,
                            hwml_core::val::LocalEnv::new(),
                        )
                        .unwrap_or_else(|_| Rc::new(Value::UniverseCode(0)));

                        let result_ty = Rc::new(Ty::El(field_ty_val.clone()));

                        // Solve the metavariables
                        self.state.solve_meta(
                            result_val_meta,
                            result_syn,
                            eval::substitute(
                                self.global,
                                &field_info.value,
                                hwml_core::val::LocalEnv::new(),
                            )
                            .unwrap_or_else(|_| Rc::new(Value::UniverseCode(0))),
                        )?;
                        self.state.solve_meta(
                            result_ty_meta,
                            field_info.ty.clone(),
                            field_ty_val,
                        )?;

                        // Mark constraint as solved
                        self.state.mark_solved(cid);
                        Ok(())
                    }
                    Value::Flex(flex) => {
                        // Still a metavariable - block on it
                        let meta_id = MetaId(flex.head.id.local_index as u32);
                        self.state.block_on(cid, &[meta_id]);
                        Ok(())
                    }
                    _ => {
                        // Not a type constructor - error
                        Err(SolveError::Elab(ElabError::NotInScope {
                            name: format!(
                                "Cannot resolve field '{}' on non-constructor type",
                                field_name.to_string(self.db)
                            ),
                            span: None,
                            elab_backtrace: Vec::new(),
                        }))
                    }
                }
            }
            _ => {
                // Type is not El(...) - error
                Err(SolveError::Elab(ElabError::TypeMismatch {
                    expected: Rc::new(Ty::UniverseType),
                    actual: forced_ty,
                    span: None,
                    elab_backtrace: Vec::new(),
                }))
            }
        }
    }

    // ─── PostponedCheck (DOE) ─────────────────────────────────────────────────────

    #[allow(clippy::too_many_arguments)]
    fn step_postponed_check(
        &mut self,
        cid: ConstraintId,
        expr: Box<hwml_surface::Expression>,
        expected_ty: RcTy<'db>,
        ctx: ElabCtx<'db>,
        placeholder: MetaId,
        depth: usize,
    ) -> Result<(), SolveError<'db>> {
        // Force the expected type to resolve any solved metas
        let forced_ty = force_ty(self.state, self.global, expected_ty.clone());

        // Check if the type is still meta-headed
        if let Ty::El(val) = forced_ty.as_ref() {
            if let Value::Flex(flex) = val.as_ref() {
                // Still meta-headed - reblock on the new meta
                let meta_id = MetaId(flex.head.id.local_index as u32);
                self.state.block_on(cid, &[meta_id]);
                return Ok(());
            }
        }

        // Type is no longer meta-headed! Package this check for the caller.
        // The caller will create an Elaborator and run the check outside the solver.
        self.ready_checks.push(ReadyCheck {
            expr,
            expected_ty: forced_ty,
            ctx,
            placeholder,
            depth,
        });

        // Mark the constraint as solved (the actual elaboration happens externally)
        self.state.mark_solved(cid);
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
    ty: &Ty<'db>,
) -> bool {
    // Convert Ty to Value for equate's type argument.
    let ty_val: RcValue<'db> = match ty {
        Ty::El(code) => code.clone(),
        Ty::UniverseType => Rc::new(Value::UniverseCode(0)),
        _ => return false,
    };
    let transparent = TransparentEnv::new();
    equal::equate(global, &transparent, depth, lhs, rhs, &ty_val).is_ok()
}

/// Collect unsolved Flex meta IDs from the top-level of a value.
fn collect_flex_heads<'db>(state: &SolverState<'db>, val: &Value<'db>, out: &mut Vec<MetaId>) {
    if let Value::Flex(flex) = val {
        let id = MetaId(flex.head.id.local_index as u32);
        if state.meta_solution(id).is_none() {
            out.push(id);
        }
    }
}

/// Collect unsolved Flex meta IDs from the code inside a `Ty::El`.
fn collect_flex_heads_ty<'db>(state: &SolverState<'db>, ty: &Ty<'db>, out: &mut Vec<MetaId>) {
    if let Ty::El(code) = ty {
        collect_flex_heads(state, code, out);
    }
}

/// Force the type-code inside `Ty::El` through meta substitution.
fn force_ty<'db>(state: &SolverState<'db>, global: &GlobalEnv<'db>, ty: RcTy<'db>) -> RcTy<'db> {
    if let Ty::El(code) = ty.as_ref() {
        let forced = force_deep(state, global, code.clone());
        if Rc::ptr_eq(code, &forced) {
            ty
        } else {
            Rc::new(Ty::El(forced))
        }
    } else {
        ty
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
