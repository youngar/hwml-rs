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

fn switch<'db, 'g>(
    env: SolverEnvironment<'db, 'g>,
    expr: Expression,
    lhs_ty: RcValue<'db>,
) -> TrustedSyntax<'db> {
    trusted::switch(env, None, lhs_ty, move |env| synth_expr(env, expr))
}

pub fn check_fun<'db, 'g>(
    env: SolverEnvironment<'db, 'g>,
    fun: surface::Fun,
    lhs_ty: RcValue<'db>,
) -> TrustedSyntax<'db> {
    //     let bg = env.clone();
    //     trusted::lambda(env, None, {})
    //     env.constrain(async move {
    //         let
    //     })
    // }
    todo!();
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
