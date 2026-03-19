use crate::unify::unify;
use crate::*;
use hwml_core::*;

async fn lambda_task<'db, 'g, F>(
    mut env: SolverEnvironment<'db, 'g>,
    loc: Option<SourceRange<'db>>,
    tm: RcValue<'db>,
    ty: RcValue<'db>,
    binder: Binder<'db>,
    body: F,
) where
    F: Fn(SolverEnvironment<'db, 'g>, RcValue<'db>) -> TrustedSyntax<'db> + 'db,
{
    // TODO: This should be using a level variable, with constraints.
    let universe = Value::universe_rc(UniverseLevel::new(0));

    // Build a Pi pattern.
    let source = env.fresh_meta(universe.clone(), loc.clone());
    let target = env.under_binder(binder.name, source.clone(), |env| {
        env.fresh_meta(universe.clone(), loc.clone())
    });

    // Ensure the expected type is `(x : a) -> b(x)`.
    let target_closure = env.make_closure(target.as_ref(), &universe);
    let pi = Value::pi_rc(source.clone(), target_closure);
    unify(env.db(), env.clone(), ty.clone(), pi, universe)
        .await
        .unwrap();

    // Elaborate the body: `env, x : source |- body : target`.
    let body = env
        .under_binder(binder.name, source.clone(), |env| {
            body(env.clone(), target.body)
        })
        .into_inner()
        .0;

    let syn_solution = Syntax::lambda_rc(Binding { body });
    let sem_solution = env.eval(&syn_solution);
    unify(env.db(), env, tm, sem_solution, ty).await.unwrap();
}

pub fn lambda<'db, 'g: 'db, F>(
    env: SolverEnvironment<'db, 'g>,
    loc: Option<SourceRange<'db>>,
    ty: RcValue<'db>,
    binder: Binder<'db>,
    body: F,
) -> TrustedSyntax<'db>
where
    F: Fn(SolverEnvironment<'db, 'g>, RcValue<'db>) -> TrustedSyntax<'db> + 'db,
{
    let meta = env.fresh_meta(ty.clone(), loc.clone());
    env.spawner.spawn(lambda_task(
        env.clone(),
        loc,
        meta.clone(),
        ty.clone(),
        binder,
        body,
    ));
    Trusted(env.quote(&meta, &ty))
}
