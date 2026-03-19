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
    ty1: RcValue<'db>,
) -> TrustedSyntax<'db> {
    let meta = env.fresh_syn_meta(ty1.clone(), None);
    let tm1 = meta.clone();
    let Trusted(Typed(tm2, ty2)) = synth_expr(env.clone(), expr);
    let env_clone = clone(&env);
    env.spawn(async move {
        unify_ty(env_clone.clone(), ty1.clone(), ty2).await.unwrap();
        // let sem_tm1 = env.eval(&tm1.clone());
        // let sem_tm2 = env.eval(&tm2);
        // unify(env.db(), env, sem_tm1, sem_tm2, ty1).await.unwrap();
    });
    Trusted(meta)
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
