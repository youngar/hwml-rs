use crate::unify::unify;
use crate::*;
use hwml_core::*;

pub fn lambda<'db, 'g, F>(
    mut env: SolverEnvironment<'db, 'g>,
    loc: Option<SourceRange<'db>>,
    lhs_ty: RcValue<'db>,
    binder: Binder<'db>,
    body: F,
) -> TrustedSyntax<'db>
where
    F: FnOnce(SolverEnvironment<'db, 'g>, RcValue<'db>) -> TrustedSyntax<'db>,
{
    let sem_lhs = env.fresh_meta(lhs_ty.clone(), loc.clone());
    let syn_lhs = env.quote(&sem_lhs, &lhs_ty);

    let universe = Value::universe_rc(UniverseLevel::new(0));
    let source = env.fresh_meta(universe.clone(), loc.clone());
    let target = env.under_binder(binder.name, source.clone(), |env| {
        env.fresh_meta(universe.clone(), loc.clone())
    });
    let target_closure = env.make_closure(target.as_ref(), &universe);
    let rhs_ty = Value::pi_rc(source.clone(), target_closure);

    let Binding(Trusted(body)) = env.under_binder(binder.name, source.clone(), |env| {
        body(env.clone(), target.0)
    });

    let syn_rhs = Syntax::lambda_rc(Binding(body));
    let sem_rhs = env.eval(&syn_rhs);

    let bg = env.clone();
    env.constrain(async move {
        unify_ty(bg.clone(), lhs_ty.clone(), rhs_ty).await.unwrap();
        unify(bg.db(), bg, sem_lhs, sem_rhs, lhs_ty).await.unwrap();
    });

    Trusted(syn_lhs)
}
