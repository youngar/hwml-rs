use crate::syn::*;
use crate::{common::ConstantId, MetaVariableId};

/// A primitive declaration.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct PrimitiveDecl<'db> {
    pub name: ConstantId<'db>,
    pub ty: RcSyntax<'db>,
}

impl<'db> PrimitiveDecl<'db> {
    pub fn new(name: ConstantId<'db>, ty: RcSyntax<'db>) -> Self {
        PrimitiveDecl { name, ty }
    }
}

/// A constant declaration with a value.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ConstantDecl<'db> {
    pub name: ConstantId<'db>,
    pub ty: RcSyntax<'db>,
    pub value: RcSyntax<'db>,
}

impl<'db> ConstantDecl<'db> {
    pub fn new(name: ConstantId<'db>, ty: RcSyntax<'db>, value: RcSyntax<'db>) -> Self {
        ConstantDecl { name, ty, value }
    }
}

/// A type constructor declaration.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TypeConstructorDecl<'db> {
    pub name: ConstantId<'db>,
    /// The parameters of the type constructor (telescope of types)
    pub parameters: Telescope<'db>,
    /// The indices of the type constructor (telescope of types)
    pub indices: Telescope<'db>,
    pub data_constructors: Vec<DataConstructorDecl<'db>>,
    pub universe: RcSyntax<'db>,
}

impl<'db> TypeConstructorDecl<'db> {
    pub fn new(
        name: ConstantId<'db>,
        parameters: Telescope<'db>,
        indices: Telescope<'db>,
        data_constructors: Vec<DataConstructorDecl<'db>>,
        universe: RcSyntax<'db>,
    ) -> Self {
        TypeConstructorDecl {
            name,
            parameters,
            indices,
            data_constructors,
            universe,
        }
    }
}

/// A data constructor within a type constructor declaration.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct DataConstructorDecl<'db> {
    pub name: ConstantId<'db>,
    /// The parameters of the data constructor (telescope of types)
    pub parameters: Telescope<'db>,
    /// The result type (the type constructor applied to indices)
    pub result_type: RcSyntax<'db>,
}

impl<'db> DataConstructorDecl<'db> {
    pub fn new(
        name: ConstantId<'db>,
        parameters: Telescope<'db>,
        result_type: RcSyntax<'db>,
    ) -> Self {
        DataConstructorDecl {
            name,
            parameters,
            result_type,
        }
    }

    /// Get the name of the data constructor.
    pub fn name(&self) -> ConstantId<'db> {
        self.name
    }

    /// Reconstruct the full Pi type from the telescope and result type.
    pub fn full_type(&self) -> RcSyntax<'db> {
        let mut result = self.result_type.clone();
        for ty in self.parameters.iter().rev() {
            result = Syntax::pi_rc(ty.clone(), BindingSyntax::new(result));
        }
        result
    }
}

/// A metavariable declaration.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct MetavariableDecl<'db> {
    pub id: MetaVariableId,
    /// The telescope of argument types (the substitution context).
    pub arguments: Telescope<'db>,
    /// The final type of the metavariable.
    pub ty: RcSyntax<'db>,
}

impl<'db> MetavariableDecl<'db> {
    pub fn new(id: MetaVariableId, arguments: Telescope<'db>, ty: RcSyntax<'db>) -> Self {
        MetavariableDecl { id, arguments, ty }
    }
}

/// A declaration in a module.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Declaration<'db> {
    /// A primitive.
    PrimitiveDecl(PrimitiveDecl<'db>),
    /// A regular constant/definition with a value.
    ConstantDecl(ConstantDecl<'db>),
    /// A type constructor, along with its data constructors.
    TypeConstructorDecl(TypeConstructorDecl<'db>),
    /// A metavariable declaration.
    MetavariableDecl(MetavariableDecl<'db>),
}

impl<'db> Declaration<'db> {
    pub fn primitive(name: ConstantId<'db>, ty: RcSyntax<'db>) -> Self {
        Declaration::PrimitiveDecl(PrimitiveDecl::new(name, ty))
    }

    pub fn constant(name: ConstantId<'db>, ty: RcSyntax<'db>, value: RcSyntax<'db>) -> Self {
        Declaration::ConstantDecl(ConstantDecl::new(name, ty, value))
    }

    pub fn type_constructor(
        name: ConstantId<'db>,
        parameters: Telescope<'db>,
        indices: Telescope<'db>,
        data_constructors: Vec<DataConstructorDecl<'db>>,
        universe: RcSyntax<'db>,
    ) -> Self {
        Declaration::TypeConstructorDecl(TypeConstructorDecl::new(
            name,
            parameters,
            indices,
            data_constructors,
            universe,
        ))
    }

    pub fn metavariable(id: MetaVariableId, arguments: Telescope<'db>, ty: RcSyntax<'db>) -> Self {
        Declaration::MetavariableDecl(MetavariableDecl::new(id, arguments, ty))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct CompilationUnit<'db> {
    pub declarations: Vec<Declaration<'db>>,
}

impl<'db> CompilationUnit<'db> {
    /// Create a new empty module.
    pub fn new() -> CompilationUnit<'db> {
        CompilationUnit {
            declarations: Vec::new(),
        }
    }

    pub fn from_declarations(declarations: Vec<Declaration<'db>>) -> CompilationUnit<'db> {
        CompilationUnit { declarations }
    }

    /// Add a declaration to the module.
    pub fn add_declaration(&mut self, declaration: Declaration<'db>) {
        self.declarations.push(declaration);
    }

    /// Add a constant declaration to the module.
    pub fn add_constant(&mut self, name: ConstantId<'db>, ty: RcSyntax<'db>, value: RcSyntax<'db>) {
        let declaration = Declaration::constant(name, ty, value);
        self.add_declaration(declaration)
    }

    /// Add a primitive declaration to the module.
    pub fn add_primitive(&mut self, name: ConstantId<'db>, ty: RcSyntax<'db>) {
        let declaration = Declaration::primitive(name, ty);
        self.add_declaration(declaration)
    }

    /// Add a type constructor declaration to the module.
    pub fn add_type_constructor(
        &mut self,
        name: ConstantId<'db>,
        parameters: Telescope<'db>,
        indices: Telescope<'db>,
        ty: RcSyntax<'db>,
        data_constructors: Vec<DataConstructorDecl<'db>>,
    ) {
        let declaration =
            Declaration::type_constructor(name, parameters, indices, data_constructors, ty);
        self.add_declaration(declaration)
    }
}
