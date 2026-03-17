use crate::*;
use hwml_core::*;
use std::result::Result;

#[derive(Debug, Clone)]
pub enum ElabError {
    Misc,
}

pub trait ElabSyntax<'db, 'g> {
    fn elab_syntax(
        self,
        env: &SolverEnvironment<'db, 'g>,
        ty: RcValue<'db>,
    ) -> Result<TrustedSyntax<'db>, ElabError>;
}

pub trait ElabTypedSyntax<'db, 'g> {
    fn elab_typed_syntax(
        self,
        env: &SolverEnvironment<'db, 'g>,
    ) -> Result<TrustedTypedSyntax<'db>, ElabError>;
}

pub trait ElabSyntaxTask<'db, 'g> {
    async fn elab_syntax_task(
        self,
        env: &SolverEnvironment<'db, 'g>,
        ty: RcValue<'db>,
    ) -> TrustedSyntax<'db>;
}

impl<'db, 'g: 'db, T> ElabSyntax<'db, 'g> for T
where
    T: ElabSyntaxTask<'db, 'g> + HasSourceRange<'db> + 'db + 'g,
{
    fn elab_syntax(
        self,
        env: &SolverEnvironment<'db, 'g>,
        ty: RcValue<'db>,
    ) -> Result<TrustedSyntax<'db>, ElabError> {
        let sem_meta = env.fresh_meta(ty.clone(), self.source_range());
        let syn_meta = env.quote(&sem_meta, &ty);

        let env_clone = env.clone();
        env.spawner.spawn(async move {
            let env = env_clone;
            let syn_tm: RcSyntax<'db> = self.elab_syntax_task(&env, ty.clone()).await.unwrap();
            let sem_tm: RcValue<'db> = env.eval(&syn_tm);
            unify(env.db(), env, sem_meta, sem_tm, ty).await;
            Ok(())
        });

        Ok(Trusted(syn_meta))
    }
}

pub trait ElabTypedSyntaxTask<'db, 'g> {
    async fn elab_typed_syntax_task(
        self,
        env: &SolverEnvironment<'db, 'g>,
    ) -> TrustedTypedSyntax<'db>;
}
