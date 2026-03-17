use crate::*;
use hwml_core::*;

#[derive(Clone, Debug)]
pub struct ElabName<'db> {
    pub source_range: Option<SourceRange<'db>>,
    pub name: Name<'db>,
}

impl<'db> HasSourceRange<'db> for ElabName<'db> {
    fn source_range(&self) -> Option<SourceRange<'db>> {
        self.source_range.clone()
    }
}

impl<'db, 'g> ElabTypedSyntax<'db, 'g> for ElabName<'db> {
    fn elab_typed_syntax(
        self,
        env: &SolverEnvironment<'db, 'g>,
    ) -> Result<TrustedTypedSyntax<'db>, ElabError> {
        match env.resolve(self.name) {
            Some(term) => Ok(Trusted(term)),
            None => Err(ElabError::Misc),
        }
    }
}
