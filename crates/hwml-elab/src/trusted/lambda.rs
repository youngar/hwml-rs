use crate::unify::unify;
use crate::*;
use hwml_core::*;

pub struct ElabLambda<'db, A> {
    pub source_range: Option<SourceRange<'db>>,
    pub binder: Binder<'db>,
    pub body: A,
}

impl<'db, A> HasSourceRange<'db> for ElabLambda<'db, A> {
    fn source_range(&self) -> Option<SourceRange<'db>> {
        self.source_range.clone().into()
    }
}

impl<'db, 'g, A> ElabSyntaxTask<'db, 'g> for ElabLambda<'db, A>
where
    A: ElabSyntax<'db, 'g> + HasSourceRange<'db>,
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
        let source = env.fresh_meta(universe.clone(), self.source_range());
        let target = env.under_binder(self.binder.name, source.clone(), |env| {
            env.fresh_meta(universe.clone(), self.source_range())
        });

        // Ensure the expected type is `(x : a) -> b(x)`.
        let target_closure = env.make_closure(target.as_ref(), &universe);
        let pi = Value::pi_rc(source.clone(), target_closure);
        unify(env.db(), env.clone(), ty, pi, universe)
            .await
            .unwrap();

        // Elaborate the body: `env, x : source |- body : target`.
        let body = env
            .under_binder(self.binder.name, source.clone(), |env| {
                self.body.elab_syntax(env, target.body).unwrap()
            })
            .into_inner()
            .0;

        Trusted(Syntax::lambda_rc(Binding { body }))
    }
}
