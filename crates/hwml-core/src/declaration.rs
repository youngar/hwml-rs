use crate::syn::*;

/// A trait for declarations which act as constants in the type theory.
pub trait ConstantDeclaration<'db> {
    /// The name of the declared constant.
    fn name(&self) -> &String;

    /// The type of the declared constant.
    fn ty(&self) -> &RcSyntax<'db>;
}

/// The various kinds of top-level declarations in the core language.
#[derive(Clone, Eq, PartialEq, Debug, Hash)]
pub enum Declaration<'db> {
    Definition(Definition<'db>),
}

impl<'db> Declaration<'db> {
    pub fn definition(name: String, ty: RcSyntax<'db>, value: RcSyntax<'db>) -> Declaration<'db> {
        Declaration::Definition(Definition { name, ty, value })
    }
}

/// A top-level definition.
#[derive(Clone, Eq, PartialEq, Debug, Hash)]
pub struct Definition<'db> {
    pub name: String,
    pub ty: RcSyntax<'db>,
    pub value: RcSyntax<'db>,
}

impl<'db> ConstantDeclaration<'db> for Definition<'db> {
    fn name(&self) -> &String {
        &self.name
    }

    fn ty(&self) -> &RcSyntax<'db> {
        &self.ty
    }
}
