use crate::*;
use hwml_core::*;
use std::rc::Rc;

#[derive(Clone, Debug)]
pub struct ElabVar {
    location: Location,
    index: Index,
}

impl Located for ElabVar {
    fn location(&self) -> Location {
        self.location
    }
}

impl<'db, 'g> ElabTypedSyntax<'db, 'g> for ElabVar {
    fn elab_typed_syntax(
        self,
        env: &SolverEnvironment<'db, 'g>,
    ) -> Result<TrustedTypedSyntax<'db>, ElabError> {
        let level = self.index.to_level(env.tc_env.values.local.depth());
        let ty = env.tc_env.type_of(level).clone();
        Ok(Trusted(Typed {
            subject: Syntax::variable_rc(self.index),
            ty,
        }))
    }
}
