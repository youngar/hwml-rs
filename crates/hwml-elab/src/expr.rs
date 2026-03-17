use crate::*;
use hwml_core::*;
use hwml_support::*;
use hwml_surface as surface;

struct ElabExpr {
    expr: surface::Expression,
}

impl<'db, 'g> ElabTypedSyntax<'db, 'g> for ElabExpr {
    fn elab_typed_syntax(
        self,
        env: &SolverEnvironment<'db, 'g>,
    ) -> Result<TrustedTypedSyntax<'db>, ElabError> {
        match self.expr {
            surface::Expression::Id(id) => {
                let text = match std::str::from_utf8(&*id.value) {
                    Ok(str) => str,
                    Err(e) => return Err(ElabError::Misc),
                };
                let name = Name::from_with_db(env.db(), text);
                let elab = ElabName {
                    source_range: None,
                    name,
                };
                elab.elab_typed_syntax(env)
            }
            _ => Err(ElabError::Misc),
        }
    }
}

impl<'db, 'g> ElabSyntax<'db, 'g> for ElabExpr {
    fn elab_syntax(
        self,
        env: &SolverEnvironment<'db, 'g>,
        ty: RcValue<'db>,
    ) -> Result<TrustedSyntax<'db>, ElabError> {
        match self.expr {
            // surface::Expression::Fun(fun) => {
            //     let binders = fun.bindings;
            //     let group = binders.groups[0]?;
            //     match group
            //     let binder = Binder {
            //         source_range: None,
            //         name: Some(fun.bindings.)
            //     };
            //     let body = ElabExpr {
            //         expr: (*fun.expr).clone(),
            //     };
            //     let elab = ElabLambda {
            //         source_range: None,
            //         binder,
            //         body,
            //     };
            //     elab.elab_syntax(env, ty)
            // }
            _ => Err(ElabError::Misc),
        }
    }
}
