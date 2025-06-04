use crate::syntax::*;

/// A trait for declarations which act as constants in the type theory.
pub trait ConstantDeclaration {
    /// The name of the declared constant.
    fn name(&self) -> &String;

    /// The type of the declared constant.
    fn ty(&self) -> &RcSyntax;
}

/// The various kinds of top-level declarations in the core language.
pub enum Declaration {
    Definition(Definition),
}

/// A top-level definition.
pub struct Definition {
    pub name: String,
    pub ty: RcSyntax,
    pub value: RcSyntax,
}

impl ConstantDeclaration for Definition {
    fn name(&self) -> &String {
        &self.name
    }

    fn ty(&self) -> &RcSyntax {
        &self.ty
    }
}
