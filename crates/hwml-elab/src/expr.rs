use crate::*;
use hwml_core::*;
use hwml_surface as surface;

struct ElabExpr {
    expr: surface::Expression,
}

impl<'db, 'g> ElabSyntax<'db, 'g> for ElabExpr {
    fn elab_syntax(
        self,
        env: &SolverEnvironment<'db, 'g>,
        ty: RcValue<'db>,
    ) -> Result<TrustedSyntax<'db>, ElabError> {
        match self.expr {
            _ => Err(ElabError::Misc),
        }
    }
}
