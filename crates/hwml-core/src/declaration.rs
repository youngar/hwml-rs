use crate::syn::*;

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Expression<'db> {
    /// A regular constant/definition with a value
    Constant(RcSyntax<'db>),
    /// A type constructor (inductive type)
    TypeConstructor {},
    /// A data constructor
    DataConstructor {},
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Declaration<'db> {
    pub name: ConstantId<'db>,
    pub ty: RcSyntax<'db>,
    pub expr: Expression<'db>,
}

impl<'db> Declaration<'db> {
    pub fn constant(name: ConstantId<'db>, ty: RcSyntax<'db>, value: RcSyntax<'db>) -> Self {
        Declaration {
            name,
            ty,
            expr: Expression::Constant(value),
        }
    }

    pub fn type_constructor(name: ConstantId<'db>, ty: RcSyntax<'db>) -> Self {
        Declaration {
            name,
            ty,
            expr: Expression::TypeConstructor {},
        }
    }

    pub fn data_constructor(
        name: ConstantId<'db>,
        ty: RcSyntax<'db>,
        inductive_type: ConstantId<'db>,
        constructor_index: usize,
    ) -> Self {
        Declaration {
            name,
            ty,
            expr: Expression::DataConstructor {},
        }
    }

    pub fn name(&self) -> &ConstantId<'db> {
        &self.name
    }

    pub fn ty(&self) -> &RcSyntax<'db> {
        &self.ty
    }

    pub fn expr(&self) -> &Expression<'db> {
        &self.expr
    }

    pub fn is_constant(&self) -> bool {
        matches!(self.expr, Expression::Constant(_))
    }

    pub fn is_type_constructor(&self) -> bool {
        matches!(self.expr, Expression::TypeConstructor { .. })
    }

    pub fn is_data_constructor(&self) -> bool {
        matches!(self.expr, Expression::DataConstructor { .. })
    }

    pub fn get_value(&self) -> Option<&RcSyntax<'db>> {
        match &self.expr {
            Expression::Constant(value) => Some(value),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Error<'db> {
    AlreadyDefined(ConstantId<'db>),
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

    /// Create a module from a vector of declarations.
    pub fn from_declarations(declarations: Vec<Declaration<'db>>) -> Module<'db> {
        Module { declarations }
    }

    /// Get all declarations in the module.
    pub fn declarations(&self) -> &[Declaration<'db>] {
        &self.declarations
    }

    /// Find a declaration by name.
    pub fn find_declaration(&self, name: &ConstantId<'db>) -> Option<&Declaration<'db>> {
        self.declarations.iter().find(|decl| &decl.name == name)
    }

    /// Check if a declaration with the given name exists.
    pub fn contains(&self, name: &ConstantId<'db>) -> bool {
        self.find_declaration(name).is_some()
    }

    /// Add a declaration to the module.
    /// Returns an error if a declaration with the same name already exists.
    pub fn add_declaration(&mut self, declaration: Declaration<'db>) -> Result<(), Error<'db>> {
        if self.contains(&declaration.name) {
            return Err(Error::AlreadyDefined(declaration.name));
        }
        self.declarations.push(declaration);
        Ok(())
    }

    /// Add a constant declaration to the module.
    pub fn add_constant(
        &mut self,
        name: ConstantId<'db>,
        ty: RcSyntax<'db>,
        value: RcSyntax<'db>,
    ) -> Result<(), Error<'db>> {
        let declaration = Declaration::constant(name, ty, value);
        self.add_declaration(declaration)
    }

    /// Add a type constructor declaration to the module.
    pub fn add_type_constructor(
        &mut self,
        name: ConstantId<'db>,
        ty: RcSyntax<'db>,
    ) -> Result<(), Error<'db>> {
        let declaration = Declaration::type_constructor(name, ty);
        self.add_declaration(declaration)
    }

    /// Add a data constructor declaration to the module.
    pub fn add_data_constructor(
        &mut self,
        name: ConstantId<'db>,
        ty: RcSyntax<'db>,
        inductive_type: ConstantId<'db>,
    ) -> Result<(), Error<'db>> {
        let declaration = Declaration::data_constructor(name, ty, inductive_type, 0);
        self.add_declaration(declaration)
    }
}
