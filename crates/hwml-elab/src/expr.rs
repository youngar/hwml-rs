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
    let mut binders = Vec::new();
    for group in fun.bindings.group {
        match group {
            surface::BindingGroup::Typed(group) => {
                for binder in group.binders {
                    binders.push(binder);
                }
            }
        }
    }

    
    // Convert each function into 
    // If there are any typed binders, form an outer type annotation.
    let mut typed = false;
    for group in fun.bindings.groups {
        if let surface::BindingGroup::TypedBindingGroup(group) {

        }
    };
    if typed {

    }

    let mut tactic = |env, ty| {
        check_expr(env, *fun.expr, ty)
    };

    for group in fun.bindings.groups.iter().rev() {
        match group {
            surface::BindingGroup::Typed(typed) => todo!("support typed binding groups"),
            surface::BindingGroup::Untyped(untyped) => {
                for binder in untyped.binders {
                    match binder {
                        Expression::Id(id) => {
                            tactic = |env| {
                                trusted::
                        }
                        _ => todo!("support richer binder names"),
                    }
                }
            }
        };
        for binding in binders {

        }
    }
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
    trusted::name(env, None, name)
}

pub fn annotate<'db, 'g>(
    env: SolverEnvironment<'db, 'g>,
    expr: Expression,
) -> TrustedTypedSyntax<'db> {
    let universe = Value::universe_rc(UniverseLevel::new(0));
    let ty = env.fresh_meta(universe.clone(), None);
    trusted::annotate(env, ty, move |env, ty| check_expr(env, expr, ty))
}
