use crate::*;
use hwml_core::*;
use hwml_support::*;
use hwml_surface as surface;
use surface::Expression;

pub fn check_expr<'db, 'g>(
    env: SolverEnvironment<'db, 'g>,
    expr: Expression,
    ty: RcValue<'db>,
) -> TrustedSyntax<'db> {
    match expr {
        Expression::Fun(fun) => check_fun(env, fun, ty),
        expr => switch(env, expr, ty),
    }
}

pub fn clone<'db, 'g>(env: &SolverEnvironment<'db, 'g>) -> SolverEnvironment<'db, 'g> {
    env.clone()
}

pub fn switch<'db, 'g>(
    env: SolverEnvironment<'db, 'g>,
    expr: Expression,
    lhs_ty: RcValue<'db>,
) -> TrustedSyntax<'db> {
    let Trusted(Typed(syn_rhs, rhs_ty)) = synth_expr(env.clone(), expr);
    let sem_lhs = env.fresh_meta(lhs_ty.clone(), None);
    let sem_rhs = env.eval(&syn_rhs);
    let syn_lhs = env.quote(&sem_lhs, &lhs_ty);
    let bg = env.clone();
    env.constrain(async move {
        unify_ty(bg.clone(), lhs_ty.clone(), rhs_ty).await.unwrap();
        unify(bg.db(), bg, sem_lhs, sem_rhs, lhs_ty).await.unwrap();
    });
    Trusted(syn_lhs)
}

pub fn check_fun<'db, 'g>(
    env: SolverEnvironment<'db, 'g>,
    fun: surface::Fun,
    ty: RcValue<'db>,
) -> TrustedSyntax<'db> {
    todo!("check function")
}

pub fn synth_expr<'db, 'g>(
    env: SolverEnvironment<'db, 'g>,
    expr: Expression,
) -> TrustedTypedSyntax<'db> {
    match expr {
        Expression::Id(id) => synth_id(env, id),
        _ => panic!("failed to synth"),
    }
}

pub fn synth_id<'db, 'g>(
    env: SolverEnvironment<'db, 'g>,
    id: surface::Id,
) -> TrustedTypedSyntax<'db> {
    let text = match std::str::from_utf8(&*id.value) {
        Ok(str) => str,
        Err(e) => panic!("failed to convert from utf8"),
    };
    let name = Name::from_with_db(env.db(), text);
    crate::trusted::elab_name(env, None, name)
}
