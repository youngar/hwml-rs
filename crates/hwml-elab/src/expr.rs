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
    kernel::rule::switch(env, None, lhs_ty, move |env| synth_expr(env, expr))
}

pub fn check_fun<'db, 'g>(
    env: SolverEnvironment<'db, 'g>,
    fun: surface::Fun,
    lhs_ty: RcValue<'db>,
) -> TrustedSyntax<'db> {
    let mut env = env;
    let mut binders: Vec<TypedBinder<'db>> = Vec::new();

    let depth = env.tc_env.depth();
    for group in fun.bindings.groups {
        match group {
            surface::BindingGroup::Typed(group) => {
                let syn_ty = synth_expr(env.clone(), *group.ty);
                let sem_ty = env.eval(syn_ty.subject());
                for _binder in group.binders {
                    binders.push(Typed(
                        Binder {
                            source_range: None,
                            name: None,
                        },
                        sem_ty.clone(),
                    ));
                    env.tc_env.push_var(sem_ty.clone());
                }
            }
            _ => todo!("handle untyped binders"),
        }
    }

    let universe = Value::universe_rc(UniverseLevel::new(0));
    let mut ty = env.fresh_meta(universe.clone(), None);
    let mut tm = check_expr(env.clone(), *fun.expr, ty.clone());

    for binder in binders.iter().rev() {
        env.tc_env.pop();
        let target_ty = env.make_closure(Binding(&ty), &universe);
        let source_ty = binder.ty().clone();
        ty = Value::pi_rc(source_ty, target_ty);

        tm = kernel::rule::lambda(
            env.clone(),
            None,
            ty.clone(),
            binder.subject().clone(),
            move |_, _| tm,
        );
    }

    assert!(env.tc_env.depth() == depth);

    let sem_tm = env.eval(&tm);
    let meta = env.fresh_meta(lhs_ty.clone(), None);
    let result = env.quote(&meta, &lhs_ty);
    let bg = env.clone();

    env.constrain(async move {
        unify_ty(bg.clone(), lhs_ty.clone(), ty).await.unwrap();
        unify(bg.db(), bg, meta, sem_tm, lhs_ty).await.unwrap();
    });

    Trusted(result)
}

pub fn synth_expr<'db, 'g>(
    env: SolverEnvironment<'db, 'g>,
    expr: Expression,
) -> TrustedTypedSyntax<'db> {
    match expr {
        Expression::Id(id) => synth_id(env, id),
        expr => annotate(env, expr),
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
    kernel::rule::name(env, None, name)
}

pub fn annotate<'db, 'g>(
    env: SolverEnvironment<'db, 'g>,
    expr: Expression,
) -> TrustedTypedSyntax<'db> {
    let universe = Value::universe_rc(UniverseLevel::new(0));
    let ty = env.fresh_meta(universe.clone(), None);
    kernel::rule::annotate(env, ty, move |env, ty| check_expr(env, expr, ty))
}
