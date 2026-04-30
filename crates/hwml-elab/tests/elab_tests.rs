use std::rc::Rc;

use hwml_core::{
    Database, Level, Syntax, Value,
    ty::Ty,
    val::{GlobalEnv, LocalEnv, MetaVariable, Spine},
    MetaVariableId,
};
use hwml_elab::{
    ctx::ElabCtx,
    elab::{Elaborator, expr},
    error::ElabError,
    kernel::Kernel,
    meta::{MetaId, MetaKind},
    solver::Solver,
    state::SolverState,
    unify::pattern,
    zonk::zonk,
};

// ─── Helpers ─────────────────────────────────────────────────────────────────

fn empty_global<'db>() -> GlobalEnv<'db> {
    GlobalEnv::new()
}

fn make_meta_flex<'db>(
    id: MetaId,
    local: LocalEnv<'db>,
) -> hwml_core::val::Flex<'db> {
    let dummy: hwml_core::RcValue<'db> = Rc::new(Value::UniverseCode(0));
    let mv = MetaVariable::new(MetaVariableId::new(id.0 as u16), local);
    hwml_core::val::Flex::new(mv, Spine::empty(), dummy)
}

// ─── SolverState unit tests ───────────────────────────────────────────────────

#[test]
fn fresh_meta_correct_arity_and_kind() {
    let mut state = SolverState::new();
    let ty = Rc::new(Ty::UniverseType);
    let id = state.fresh_meta(ty, 3, MetaKind::Term);
    let entry = state.meta(id).expect("meta should exist");
    assert_eq!(entry.arity, 3);
    assert!(matches!(entry.kind, MetaKind::Term));
    assert!(entry.solution.is_none());
}

#[test]
fn emit_het_eq_creates_constraint_and_witness() {
    let mut state = SolverState::new();
    let ty = Rc::new(Ty::UniverseType);
    let lhs: hwml_core::RcValue = Rc::new(Value::UniverseCode(0));
    let rhs: hwml_core::RcValue = Rc::new(Value::UniverseCode(1));

    let before_metas = state.iter_metas().count();
    let before_constraints = state.iter_constraints().count();

    // Caller creates the witness meta, then passes it to emit_het_eq.
    let witness = state.fresh_meta(ty.clone(), 0, MetaKind::Term);
    state.emit_het_eq(lhs, ty.clone(), rhs, ty.clone(), 0, witness);

    assert_eq!(state.iter_metas().count(), before_metas + 1);
    assert_eq!(state.iter_constraints().count(), before_constraints + 1);
    assert_eq!(state.active_count(), 1);
}

#[test]
fn solve_meta_wakes_blocked_constraints() {
    let mut state = SolverState::new();
    let ty = Rc::new(Ty::UniverseType);
    let meta_id = state.fresh_meta(ty.clone(), 0, MetaKind::Term);

    // Emit a HetEq constraint that should be blocked on meta_id.
    let dummy_val: hwml_core::RcValue = Rc::new(Value::UniverseCode(0));
    let witness = state.fresh_meta(ty.clone(), 0, MetaKind::Term);
    let cid = state.emit_het_eq(dummy_val.clone(), ty.clone(), dummy_val.clone(), ty.clone(), 0, witness);

    // Drain the queue so we know only our re-queue comes back.
    while state.pop_active().is_some() {}
    // Manually block cid on meta_id.
    state.block_on(cid, &[meta_id]);
    assert_eq!(state.active_count(), 0, "should be blocked after draining");

    // Solve the meta — this should re-queue the constraint.
    let sol_val: hwml_core::RcValue = Rc::new(Value::UniverseCode(42));
    let sol_syn: hwml_core::RcSyntax = Rc::new(Syntax::UniverseCode(42));
    state.solve_meta(meta_id, sol_syn, sol_val).expect("solve should succeed");

    assert_eq!(state.active_count(), 1, "constraint should be re-queued after solve");
}

#[test]
fn force_flex_returns_solution_after_solve() {
    let global = empty_global();
    let mut state = SolverState::new();
    let ty = Rc::new(Ty::UniverseType);
    let meta_id = state.fresh_meta(ty.clone(), 0, MetaKind::Term);

    let flex = make_meta_flex(meta_id, LocalEnv::new());

    // Before solve: no solution.
    assert!(state.force_flex(&global, &flex).is_none());

    let sol_val: hwml_core::RcValue = Rc::new(Value::UniverseCode(7));
    let sol_syn: hwml_core::RcSyntax = Rc::new(Syntax::UniverseCode(7));
    state.solve_meta(meta_id, sol_syn, sol_val).unwrap();

    let forced = state.force_flex(&global, &flex).expect("should return solution");
    match forced.as_ref() {
        Value::UniverseCode(7) => {}
        other => panic!("expected UniverseCode(7), got {other:?}"),
    }
}

// ─── Pattern unification tests ────────────────────────────────────────────────

#[test]
fn pattern_unify_linear_solves_meta() {
    let global = empty_global();
    let mut state = SolverState::new();
    let ty: hwml_core::ty::RcTy = Rc::new(Ty::UniverseType);

    // Create meta ?m of arity 1: ?m[x] where x is at level 0.
    let meta_id = state.fresh_meta(ty.clone(), 1, MetaKind::Term);

    // Build local env: [Variable(level 0)].
    let var_ty: hwml_core::RcValue = Rc::new(Value::UniverseCode(0));
    let mut local = LocalEnv::new();
    local.push(Rc::new(Value::variable(Level::new(0), var_ty.clone())));

    let flex = make_meta_flex(meta_id, local);

    // RHS = Variable(level 0) — in meta scope, should become Variable(level 0).
    let rhs: hwml_core::RcValue = Rc::new(Value::variable(Level::new(0), var_ty.clone()));

    let solved = pattern::pattern_unify(&global, &mut state, &flex, rhs, ty).unwrap();
    assert!(solved, "pattern unification should succeed");

    let solution = state.meta_solution(meta_id).expect("meta should be solved");
    match solution.as_ref() {
        Value::Rigid(r) if r.head.level == Level::new(0) => {}
        other => panic!("expected Variable(Level(0)), got {other:?}"),
    }
}

#[test]
fn pattern_unify_scope_violation_returns_err() {
    let global = empty_global();
    let mut state = SolverState::new();
    let ty: hwml_core::ty::RcTy = Rc::new(Ty::UniverseType);

    // ?m of arity 1, parameterized over level 0.
    let meta_id = state.fresh_meta(ty.clone(), 1, MetaKind::Term);
    let var_ty: hwml_core::RcValue = Rc::new(Value::UniverseCode(0));
    let mut local = LocalEnv::new();
    local.push(Rc::new(Value::variable(Level::new(0), var_ty.clone())));

    let flex = make_meta_flex(meta_id, local);

    // RHS = Variable(level 1) — NOT in the meta's scope (only level 0 was passed).
    let rhs: hwml_core::RcValue = Rc::new(Value::variable(Level::new(1), var_ty.clone()));

    let result = pattern::pattern_unify(&global, &mut state, &flex, rhs, ty);
    match result {
        Err(ElabError::ScopeViolation { .. }) => {}
        other => panic!("expected ScopeViolation, got {other:?}"),
    }
}

// ─── Gap 1: rigid mismatch ────────────────────────────────────────────────────

#[test]
fn unify_rigid_mismatch_is_hard_failure() {
    use hwml_elab::unify::Unifier;

    let global = empty_global();
    let mut state = SolverState::new();

    let var_ty: hwml_core::RcValue = Rc::new(Value::UniverseCode(0));
    // Two distinct rigid variables at different levels.
    let x: hwml_core::RcValue = Rc::new(Value::variable(Level::new(0), var_ty.clone()));
    let y: hwml_core::RcValue = Rc::new(Value::variable(Level::new(1), var_ty.clone()));

    let ty: hwml_core::ty::RcTy = Rc::new(Ty::UniverseType);
    let mut u = Unifier::new(&global, &mut state, 2);
    let result = u.unify(x, ty.clone(), y, ty);
    match result {
        Err(ElabError::UnificationFailure { .. }) => {}
        other => panic!("expected UnificationFailure, got {other:?}"),
    }
}

// ─── Gap 2: non-linear inversion ─────────────────────────────────────────────

#[test]
fn pattern_unify_nonlinear_soft_fails_when_rhs_mentions_duplicate() {
    let global = empty_global();
    let mut state = SolverState::new();
    let ty: hwml_core::ty::RcTy = Rc::new(Ty::UniverseType);

    // ?m of arity 2, but BOTH args are the same level 0 (non-linear).
    let meta_id = state.fresh_meta(ty.clone(), 2, MetaKind::Term);
    let var_ty: hwml_core::RcValue = Rc::new(Value::UniverseCode(0));
    let x0 = Rc::new(Value::variable(Level::new(0), var_ty.clone()));
    let mut local = LocalEnv::new();
    local.push(x0.clone());
    local.push(x0.clone()); // duplicate: non-linear

    let flex = make_meta_flex(meta_id, local);

    // RHS mentions level 0 (the ambiguous variable) — should soft-fail (Ok(false)).
    let rhs: hwml_core::RcValue = Rc::new(Value::variable(Level::new(0), var_ty.clone()));
    let result = pattern::pattern_unify(&global, &mut state, &flex, rhs, ty.clone()).unwrap();
    assert!(!result, "non-linear pattern with ambiguous RHS should soft-fail");
    assert!(state.meta_solution(meta_id).is_none(), "meta should remain unsolved");
}

#[test]
fn pattern_unify_nonlinear_succeeds_when_rhs_avoids_duplicate() {
    let global = empty_global();
    let mut state = SolverState::new();
    let ty: hwml_core::ty::RcTy = Rc::new(Ty::UniverseType);

    // ?m[x, x, z]: non-linear for x (level 0), linear for z (level 1).
    let meta_id = state.fresh_meta(ty.clone(), 3, MetaKind::Term);
    let var_ty: hwml_core::RcValue = Rc::new(Value::UniverseCode(0));
    let x0 = Rc::new(Value::variable(Level::new(0), var_ty.clone()));
    let z1 = Rc::new(Value::variable(Level::new(1), var_ty.clone()));
    let mut local = LocalEnv::new();
    local.push(x0.clone()); // pos 0: level 0 — ambiguous (appears twice)
    local.push(x0.clone()); // pos 1: level 0 — ambiguous
    local.push(z1.clone()); // pos 2: level 1 — linear

    let flex = make_meta_flex(meta_id, local);

    // RHS = z (level 1) — only the linear variable. Should succeed.
    let rhs: hwml_core::RcValue = Rc::new(Value::variable(Level::new(1), var_ty.clone()));
    let result = pattern::pattern_unify(&global, &mut state, &flex, rhs, ty.clone()).unwrap();
    assert!(result, "non-linear pattern with non-ambiguous RHS should succeed");
    assert!(state.meta_solution(meta_id).is_some(), "meta should be solved");
}

// ─── Gap 5: same-meta intersection ───────────────────────────────────────────

#[test]
fn unify_same_meta_trivial_succeeds_without_solving() {
    use hwml_elab::unify::Unifier;

    let global = empty_global();
    let mut state = SolverState::new();
    let ty: hwml_core::ty::RcTy = Rc::new(Ty::UniverseType);

    let meta_id = state.fresh_meta(ty.clone(), 1, MetaKind::Term);
    let var_ty: hwml_core::RcValue = Rc::new(Value::UniverseCode(0));
    let x0 = Rc::new(Value::variable(Level::new(0), var_ty.clone()));
    let mut local = LocalEnv::new();
    local.push(x0.clone());

    // ?m[x] = ?m[x] with same local — should return Solved without solving ?m.
    let lhs = Rc::new(Value::Flex(
        hwml_core::val::Flex::new(
            hwml_core::val::MetaVariable::new(
                hwml_core::MetaVariableId::new(meta_id.0 as u16),
                local.clone(),
            ),
            hwml_core::val::Spine::empty(),
            Rc::new(Value::UniverseCode(0)),
        )
    ));
    let rhs = lhs.clone();

    let mut u = Unifier::new(&global, &mut state, 1);
    let result = u.unify(lhs, ty.clone(), rhs, ty).unwrap();
    assert!(matches!(result, hwml_elab::unify::UnifyResult::Solved));
    // Meta should NOT be solved — trivially true constraint discharged without constraining ?m.
    assert!(state.meta_solution(meta_id).is_none());
}

#[test]
fn unify_same_meta_partial_intersection_creates_new_meta() {
    use hwml_elab::unify::Unifier;

    let global = empty_global();
    let mut state = SolverState::new();
    let ty: hwml_core::ty::RcTy = Rc::new(Ty::UniverseType);

    let meta_id = state.fresh_meta(ty.clone(), 2, MetaKind::Term);
    let var_ty: hwml_core::RcValue = Rc::new(Value::UniverseCode(0));
    let x0 = Rc::new(Value::variable(Level::new(0), var_ty.clone()));
    let y1 = Rc::new(Value::variable(Level::new(1), var_ty.clone()));

    let meta_vid = hwml_core::MetaVariableId::new(meta_id.0 as u16);

    // ?m[x, y] (lhs local = [x, y])
    let mut lhs_local = LocalEnv::new();
    lhs_local.push(x0.clone());
    lhs_local.push(y1.clone());
    let lhs = Rc::new(Value::Flex(hwml_core::val::Flex::new(
        hwml_core::val::MetaVariable::new(meta_vid, lhs_local),
        hwml_core::val::Spine::empty(),
        Rc::new(Value::UniverseCode(0)),
    )));

    // ?m[y, x] (rhs local = [y, x]) — positions differ
    let mut rhs_local = LocalEnv::new();
    rhs_local.push(y1.clone());
    rhs_local.push(x0.clone());
    let rhs = Rc::new(Value::Flex(hwml_core::val::Flex::new(
        hwml_core::val::MetaVariable::new(meta_vid, rhs_local),
        hwml_core::val::Spine::empty(),
        Rc::new(Value::UniverseCode(0)),
    )));

    let metas_before = state.iter_metas().count();
    let mut u = Unifier::new(&global, &mut state, 2);
    let result = u.unify(lhs, ty.clone(), rhs, ty).unwrap();
    assert!(matches!(result, hwml_elab::unify::UnifyResult::Solved));

    // ?m should now be solved.
    assert!(state.meta_solution(meta_id).is_some(), "?m should be solved after intersection");
    // A new meta ?m' should have been created.
    assert_eq!(state.iter_metas().count(), metas_before + 1, "intersection should create one new meta");
}

// ─── Kernel expect tests ──────────────────────────────────────────────────────

/// `expect` fast path: same Ty::UniverseType on both sides → no new meta.
#[test]
fn expect_fast_path_equal_types_no_meta() {
    let global = empty_global();
    let mut state = SolverState::new();
    let ctx = ElabCtx::empty();
    let mut kernel = Kernel::new(&global, ctx, &mut state);

    // synth_universe(Some(0)) returns (UniverseCode(0), Ty::UniverseType).
    let checked = kernel.synth_universe(Some(0)).unwrap();
    let meta_count_before = kernel.state.iter_metas().count();

    // expect with the same Ty::UniverseType → fast path, no new meta.
    let _ = kernel.expect(Rc::new(Ty::UniverseType), checked).into_inner();

    assert_eq!(kernel.state.iter_metas().count(), meta_count_before);
}

/// `expect` slow path: different types → new witness meta + HetEq constraint emitted.
#[test]
fn expect_slow_path_emits_het_eq() {
    let global = empty_global();
    let mut state = SolverState::new();
    let ctx = ElabCtx::empty();
    let mut kernel = Kernel::new(&global, ctx, &mut state);

    // synth_universe(Some(0)) returns (UniverseCode(0), Ty::UniverseType).
    let checked = kernel.synth_universe(Some(0)).unwrap();

    // Expect at Ty::El(UniverseCode(0)) — different from Ty::UniverseType → slow path.
    let different_ty: hwml_core::ty::RcTy =
        Rc::new(Ty::El(Rc::new(Value::UniverseCode(0))));
    let constraint_before = kernel.state.iter_constraints().count();

    let _ = kernel.expect(different_ty, checked).into_inner();

    assert!(
        kernel.state.iter_constraints().count() > constraint_before,
        "expect slow path should emit a HetEq constraint"
    );
}

// ─── Integration test: identity function ─────────────────────────────────────

#[test]
fn elaborate_identity_function() {
    use hwml_surface::Expression;

    let global = empty_global();
    let mut state = SolverState::new();
    let ctx = ElabCtx::empty();

    // Type: (A : Type) -> A -> A
    // In surface AST:
    //   Pi { bindings: [(A : Universe)], target: Arrow { A, A } }
    let pi_ty = build_id_type();
    // Value: fun A a => a
    let fun_val = build_id_fun();

    // Synth the type first.
    let mut elab = Elaborator { kernel: Kernel::new(&global, ctx.clone(), &mut state) };
    let (ty_syn, ty_kind) = expr::synth(&mut elab, &pi_ty)
        .expect("type synthesis should succeed")
        .into_inner();
    assert!(
        matches!(ty_kind.as_ref(), Ty::UniverseType),
        "Pi type should have kind UniverseType"
    );

    // Check the fun against the synthesized type.
    // We need the type as El(code). Evaluate ty_syn to get the code.
    let ty_code = elab.kernel.eval_syn_flex(&ty_syn);
    let ty_as_el: hwml_core::ty::RcTy = Rc::new(Ty::El(ty_code));
    let _val_syn = expr::check(&mut elab, &fun_val, ty_as_el)
        .expect("identity function should type-check")
        .into_inner();

    // Run solver.
    {
        let mut solver = Solver::new(&mut state, &global);
        solver.run().expect("solver should not error");
    }

    // Zonk: resolve universe metas (should default to 0).
    zonk(&mut state).expect("zonk should succeed");

    // All metas should be solved.
    for (_, entry) in state.iter_metas() {
        assert!(entry.solution.is_some(), "all metas should be solved after zonk");
    }
}

// ─── Constructor injectivity ──────────────────────────────────────────────────

fn make_qn<'db>(db: &'db Database, name: &str) -> hwml_core::QualifiedName<'db> {
    use hwml_core::{name::{Atom, Fixity, Name}, word::Word};
    let word = Word::new(db, name);
    let atom = Atom::new(word);
    let n = Name::new(db, Fixity::Closed, Box::from([atom]));
    hwml_core::QualifiedName::new(db, None, n)
}

/// `DataConstructor(c, [a1, b1]) = DataConstructor(c, [m_a, m_b])`
/// should decompose into two sub-constraints and mark the outer one solved.
#[test]
fn solver_data_constructor_injectivity() {
    use hwml_core::val::DataConstructor;

    let db = Database::new();
    let global = empty_global();
    let mut state = SolverState::new();
    let ty: hwml_core::ty::RcTy = Rc::new(Ty::UniverseType);

    let var_ty: hwml_core::RcValue = Rc::new(Value::UniverseCode(0));
    let a1: hwml_core::RcValue = Rc::new(Value::variable(Level::new(0), var_ty.clone()));
    let b1: hwml_core::RcValue = Rc::new(Value::variable(Level::new(1), var_ty.clone()));

    // Metas with arity=2 so they can reference a1 (Level 0) and b1 (Level 1).
    let mut local_2var = LocalEnv::new();
    local_2var.push(a1.clone());
    local_2var.push(b1.clone());

    let m_a = state.fresh_meta(ty.clone(), 2, MetaKind::Term);
    let m_b = state.fresh_meta(ty.clone(), 2, MetaKind::Term);
    let m_a_val: hwml_core::RcValue = Rc::new(Value::Flex(make_meta_flex(m_a, local_2var.clone())));
    let m_b_val: hwml_core::RcValue = Rc::new(Value::Flex(make_meta_flex(m_b, local_2var.clone())));

    // Use a real QualifiedName from a Salsa DB.
    let qn = make_qn(&db, "MyCon");

    let lhs = Rc::new(Value::DataConstructor(DataConstructor::new(qn, vec![a1.clone(), b1.clone()])));
    let rhs = Rc::new(Value::DataConstructor(DataConstructor::new(qn, vec![m_a_val, m_b_val])));

    let witness = state.fresh_meta(ty.clone(), 0, MetaKind::Term);
    let constraints_before = state.iter_constraints().count();
    state.emit_het_eq(lhs, ty.clone(), rhs, ty.clone(), 2, witness);

    let mut solver = Solver::new(&mut state, &global);
    solver.run().expect("solver should not error");

    // Outer constraint decomposed → two new sub-constraints created.
    assert!(
        state.iter_constraints().count() > constraints_before + 1,
        "constructor injectivity should emit 2 sub-constraints"
    );
}

/// Mismatched DataConstructor names → hard UnificationFailure.
#[test]
fn solver_data_constructor_mismatch_is_hard_failure() {
    use hwml_core::val::DataConstructor;

    let db = Database::new();
    let global = empty_global();
    let mut state = SolverState::new();
    let ty: hwml_core::ty::RcTy = Rc::new(Ty::UniverseType);

    let var_ty: hwml_core::RcValue = Rc::new(Value::UniverseCode(0));
    let a: hwml_core::RcValue = Rc::new(Value::variable(Level::new(0), var_ty.clone()));

    let qn1 = make_qn(&db, "Con1");
    let qn2 = make_qn(&db, "Con2");

    let lhs = Rc::new(Value::DataConstructor(DataConstructor::new(qn1, vec![a.clone()])));
    let rhs = Rc::new(Value::DataConstructor(DataConstructor::new(qn2, vec![a.clone()])));

    let witness = state.fresh_meta(ty.clone(), 0, MetaKind::Term);
    state.emit_het_eq(lhs, ty.clone(), rhs, ty.clone(), 1, witness);

    let mut solver = Solver::new(&mut state, &global);
    let result = solver.run();
    assert!(
        matches!(result, Err(hwml_elab::solver::SolveError::Elab(hwml_elab::error::ElabError::UnificationFailure { .. }))),
        "mismatched constructors should be a hard failure"
    );
}

// ─── Identity solver step ─────────────────────────────────────────────────────

/// Two definitionally-equal rigid values → constraint solved immediately.
#[test]
fn solver_identity_solves_equal_rigid_values() {
    let global = empty_global();
    let mut state = SolverState::new();
    let ty: hwml_core::ty::RcTy = Rc::new(Ty::UniverseType);

    let val: hwml_core::RcValue = Rc::new(Value::UniverseCode(3));

    let witness = state.fresh_meta(ty.clone(), 0, MetaKind::Term);
    let _cid = state.emit_het_eq(val.clone(), ty.clone(), val.clone(), ty.clone(), 0, witness);

    let mut solver = Solver::new(&mut state, &global);
    solver.run().expect("solver should not error");

    // All constraints should be solved.
    for (_, entry) in state.iter_constraints() {
        assert!(
            matches!(entry.status, hwml_elab::constraint::ConstraintStatus::Solved),
            "identity constraint should be solved"
        );
    }
}

// ─── Gap 3: pruning ───────────────────────────────────────────────────────────

/// ?m[x] = ?m2[x, y] where y is out of scope of ?m.
/// ?m2 should be pruned to ?m2'[x]; ?m solved to ?m2'[x].
#[test]
fn pattern_unify_prunes_out_of_scope_flex_arg() {
    let global = empty_global();
    let mut state = SolverState::new();
    let ty: hwml_core::ty::RcTy = Rc::new(Ty::UniverseType);

    let var_ty: hwml_core::RcValue = Rc::new(Value::UniverseCode(0));
    let x0 = Rc::new(Value::variable(Level::new(0), var_ty.clone()));
    let y1 = Rc::new(Value::variable(Level::new(1), var_ty.clone()));

    // ?m of arity 1, parameterized over x (level 0).
    let m_id = state.fresh_meta(ty.clone(), 1, MetaKind::Term);
    let mut m_local = LocalEnv::new();
    m_local.push(x0.clone());
    let flex_m = make_meta_flex(m_id, m_local);

    // ?m2 of arity 2, parameterized over x and y.
    let m2_id = state.fresh_meta(ty.clone(), 2, MetaKind::Term);
    let mut m2_local = LocalEnv::new();
    m2_local.push(x0.clone());
    m2_local.push(y1.clone());
    let rhs = Rc::new(Value::Flex(make_meta_flex(m2_id, m2_local)));

    // pattern_unify(?m[x] = ?m2[x, y]) — y is out of scope of ?m.
    let solved = pattern::pattern_unify(&global, &mut state, &flex_m, rhs, ty).unwrap();
    assert!(solved, "pruning should let unification succeed");

    // ?m2 must be solved (pruned to a fresh meta that doesn't depend on y).
    assert!(state.meta_solution(m2_id).is_some(), "?m2 should be pruned/solved");
    // ?m must be solved too.
    assert!(state.meta_solution(m_id).is_some(), "?m should be solved");
}

/// ?m[x] = ?m2[x] where all args are in scope — no pruning, ?m2 stays unsolved.
#[test]
fn pattern_unify_no_prune_when_all_flex_args_in_scope() {
    let global = empty_global();
    let mut state = SolverState::new();
    let ty: hwml_core::ty::RcTy = Rc::new(Ty::UniverseType);

    let var_ty: hwml_core::RcValue = Rc::new(Value::UniverseCode(0));
    let x0 = Rc::new(Value::variable(Level::new(0), var_ty.clone()));

    // Both ?m and ?m2 parameterized over x only.
    let m_id = state.fresh_meta(ty.clone(), 1, MetaKind::Term);
    let mut m_local = LocalEnv::new();
    m_local.push(x0.clone());
    let flex_m = make_meta_flex(m_id, m_local);

    let m2_id = state.fresh_meta(ty.clone(), 1, MetaKind::Term);
    let mut m2_local = LocalEnv::new();
    m2_local.push(x0.clone());
    let rhs = Rc::new(Value::Flex(make_meta_flex(m2_id, m2_local)));

    let solved = pattern::pattern_unify(&global, &mut state, &flex_m, rhs, ty).unwrap();
    assert!(solved, "same-scope flex should unify");

    // ?m2 should NOT be pruned — it stays unsolved.
    assert!(state.meta_solution(m2_id).is_none(), "?m2 should not be solved when all args in scope");
    // ?m should be solved to reference ?m2.
    assert!(state.meta_solution(m_id).is_some(), "?m should be solved");
}

// ─── Gap 4: lowering ─────────────────────────────────────────────────────────

/// ?m[x] = f x where f = x (rigid variable) applied to another rigid variable.
/// Result: ?m solved to `λx. x x` (a self-application — tests spine lowering).
#[test]
fn pattern_unify_lowers_rigid_with_spine() {
    use hwml_core::val::{Eliminator, Normal, Spine};

    let global = empty_global();
    let mut state = SolverState::new();
    let ty: hwml_core::ty::RcTy = Rc::new(Ty::UniverseType);

    let var_ty: hwml_core::RcValue = Rc::new(Value::UniverseCode(0));
    let x0 = Rc::new(Value::variable(Level::new(0), var_ty.clone()));

    // ?m of arity 1.
    let m_id = state.fresh_meta(ty.clone(), 1, MetaKind::Term);
    let mut m_local = LocalEnv::new();
    m_local.push(x0.clone());
    let flex_m = make_meta_flex(m_id, m_local);

    // RHS = x0 applied to x0: Rigid(Level(0), Spine([Application(x0)])).
    let mut spine = Spine::empty();
    spine.push(Eliminator::application(Normal::new(var_ty.clone(), x0.clone())));
    let rhs = Rc::new(Value::Rigid(hwml_core::val::Rigid::new(
        hwml_core::val::Variable::new(Level::new(0)),
        spine,
        var_ty.clone(),
    )));

    let solved = pattern::pattern_unify(&global, &mut state, &flex_m, rhs, ty).unwrap();
    assert!(solved, "lowering should solve ?m");
    assert!(state.meta_solution(m_id).is_some(), "?m should be solved after lowering");
}

// ─── Surface AST builders ────────────────────────────────────────────────────

fn id_expr(name: &[u8]) -> Box<hwml_surface::Expression> {
    Box::new(hwml_surface::Expression::Id(hwml_surface::Id {
        loc: 0..0,
        value: name.to_vec().into_boxed_slice(),
    }))
}

fn universe_expr() -> Box<hwml_surface::Expression> {
    Box::new(hwml_surface::Expression::Universe(hwml_surface::Universe {
        loc: 0..0,
        level: None,
    }))
}

/// Build the type `(A : Type) -> A -> A` as a surface expression.
fn build_id_type() -> hwml_surface::Expression {
    let pi = hwml_surface::Pi {
        loc: 0..0,
        bindings: hwml_surface::TypedBindings {
            groups: vec![hwml_surface::TypedBindingGroup {
                binders: vec![id_expr(b"A")],
                ty: universe_expr(),
            }],
        },
        target: Box::new(hwml_surface::Expression::Arrow(hwml_surface::Arrow {
            loc: 0..0,
            source: id_expr(b"A"),
            target: id_expr(b"A"),
        })),
    };
    hwml_surface::Expression::Pi(pi)
}

/// Build `fun A a => a` as a surface expression.
fn build_id_fun() -> hwml_surface::Expression {
    let fun = hwml_surface::Fun {
        loc: 0..0,
        bindings: hwml_surface::Bindings {
            groups: vec![
                hwml_surface::BindingGroup::Untyped(hwml_surface::UntypedBindingGroup {
                    binders: id_expr(b"A"),
                }),
                hwml_surface::BindingGroup::Untyped(hwml_surface::UntypedBindingGroup {
                    binders: id_expr(b"a"),
                }),
            ],
        },
        expr: id_expr(b"a"),
    };
    hwml_surface::Expression::Fun(fun)
}
