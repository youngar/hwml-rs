use crate::syn::*;

/// A trait for declarations which act as constants in the type theory.
pub trait ConstantDeclaration {
    /// The name of the declared constant.
    fn name(&self) -> &String;

    /// The type of the declared constant.
    fn ty(&self) -> &RcSyntax;
}

/// The various kinds of top-level declarations in the core language.
#[derive(Clone, Eq, PartialEq, Debug, Hash)]
pub enum Declaration {
    Definition(Definition),
}

impl Declaration {
    pub fn definition(name: String, ty: RcSyntax, value: RcSyntax) -> Declaration {
        Declaration::Definition(Definition { name, ty, value })
    }
}

/// A top-level definition.
#[derive(Clone, Eq, PartialEq, Debug, Hash)]
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
