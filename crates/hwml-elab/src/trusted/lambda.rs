use crate::unify::unify;
use crate::*;
use hwml_core::*;

pub struct ElabLambda<A> {
    pub location: Location,
    pub body: A,
}

impl<A> Located for ElabLambda<A> {
    fn location(&self) -> Location {
        self.location
    }
}

impl<'db, 'g, A> ElabSyntaxTask<'db, 'g> for ElabLambda<A>
where
    A: ElabSyntax<'db, 'g> + Located,
{
    /// Check that the expected type is a pi, before elaborating the body.
    /// Return the elaborated lambda.
    async fn elab_syntax_task(
        self,
        env: &SolverEnvironment<'db, 'g>,
        ty: RcValue<'db>,
    ) -> TrustedSyntax<'db> {
        // TODO: This should be using a level variable, with constraints.
        let mut env = env.clone();
        let universe = Value::universe_rc(UniverseLevel::new(0));

        // Build a Pi pattern.
        let source = env.fresh_meta(universe.clone(), self.location());
        let target = env.under_binder(source.clone(), |env| {
            env.fresh_meta(universe.clone(), self.location())
        });

        // Ensure the expected type is `(x : a) -> b(x)`.
        let target_closure = env.make_closure(target.as_ref(), &universe);
        let pi = Value::pi_rc(source.clone(), target_closure);
        unify(env.db(), env.clone(), ty, pi, universe)
            .await
            .unwrap();

        // Elaborate the body: `env, x : source |- body : target`.
        let body = env
            .under_binder(source.clone(), |env| {
                self.body.elab_syntax(env, target.body).unwrap()
            })
            .into_inner()
            .0;

        Trusted(Syntax::lambda_rc(Binding { body }))
    }
}
