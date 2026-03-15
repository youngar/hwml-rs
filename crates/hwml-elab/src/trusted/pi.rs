use crate::*;
use hwml_core::*;

struct ElabPi<A, B> {
    source: A,
    target: B,
}

impl<'db, 'g, A, B> ElabSyntaxTask<'db, 'g> for ElabPi<A, B>
where
    A: ElabSyntax<'db, 'g>,
    B: ElabSyntax<'db, 'g>,
{
    async fn elab_syntax_task(
        self,
        _env: &SolverEnvironment<'db, 'g>,
        _ty: RcValue<'db>,
    ) -> TrustedSyntax<'db> {
        todo!("pi elaboration not yet implemented");
    }
}
