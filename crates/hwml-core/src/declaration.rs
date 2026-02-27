use crate::syn::*;
use crate::ConstantId;

/// A primitive declaration.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Primitive<'db> {
    pub name: ConstantId<'db>,
    pub ty: RcSyntax<'db>,
}

impl<'db> Primitive<'db> {
    pub fn new(name: ConstantId<'db>, ty: RcSyntax<'db>) -> Self {
        Primitive { name, ty }
    }
}

/// A constant declaration with a value.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Constant<'db> {
    pub name: ConstantId<'db>,
    pub ty: RcSyntax<'db>,
    pub value: RcSyntax<'db>,
}

impl<'db> Constant<'db> {
    pub fn new(name: ConstantId<'db>, ty: RcSyntax<'db>, value: RcSyntax<'db>) -> Self {
        Constant { name, ty, value }
    }
}

/// A type constructor declaration.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TypeConstructor<'db> {
    pub name: ConstantId<'db>,
    pub data_constructors: Vec<DataConstructor<'db>>,
    pub universe: RcSyntax<'db>,
}

impl<'db> TypeConstructor<'db> {
    pub fn new(
        name: ConstantId<'db>,
        data_constructors: Vec<DataConstructor<'db>>,
        universe: RcSyntax<'db>,
    ) -> Self {
        TypeConstructor {
            name,
            data_constructors,
            universe,
        }
    }
}

/// A data constructor within a type constructor declaration.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct DataConstructor<'db> {
    pub name: ConstantId<'db>,
    /// The parameters of the data constructor (telescope of types)
    pub parameters: Telescope<'db>,
    /// The result type (the type constructor applied to indices)
    pub result_type: RcSyntax<'db>,
}

impl<'db> DataConstructor<'db> {
    pub fn new(
        name: ConstantId<'db>,
        parameters: Telescope<'db>,
        result_type: RcSyntax<'db>,
    ) -> Self {
        DataConstructor {
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
            result = Syntax::pi_rc(ty.clone(), result);
        }
        result
    }
}

/// A declaration in a module.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Declaration<'db> {
    /// A primitive.
    Primitive(Primitive<'db>),
    /// A regular constant/definition with a value.
    Constant(Constant<'db>),
    /// A type constructor, along with its data constructors.
    TypeConstructor(TypeConstructor<'db>),
}

impl<'db> Declaration<'db> {
    pub fn primitive(name: ConstantId<'db>, ty: RcSyntax<'db>) -> Self {
        Declaration::Primitive(Primitive::new(name, ty))
    }

    pub fn constant(name: ConstantId<'db>, ty: RcSyntax<'db>, value: RcSyntax<'db>) -> Self {
        Declaration::Constant(Constant::new(name, ty, value))
    }

    pub fn type_constructor(
        name: ConstantId<'db>,
        data_constructors: Vec<DataConstructor<'db>>,
        universe: RcSyntax<'db>,
    ) -> Self {
        Declaration::TypeConstructor(TypeConstructor::new(name, data_constructors, universe))
    }
}

/// A module containing a list of declarations.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Module<'db> {
    pub declarations: Vec<Declaration<'db>>,
}

impl<'db> Module<'db> {
    /// Create a new empty module.
    pub fn new() -> Module<'db> {
        Module {
            declarations: Vec::new(),
        }
    }

    pub fn from_declarations(declarations: Vec<Declaration<'db>>) -> Module<'db> {
        Module { declarations }
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
        ty: RcSyntax<'db>,
        data_constructors: Vec<DataConstructor<'db>>,
    ) {
        let declaration = Declaration::type_constructor(name, data_constructors, ty);
        self.add_declaration(declaration)
    }
}
