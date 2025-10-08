use crate::syn::*;
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expression<'db> {
    /// A regular constant/definition with a value
    Constant(RcSyntax<'db>),
    /// A type constructor (inductive type)
    TypeConstructor {},
    /// A data constructor
    DataConstructor {},
}

#[derive(Debug, Clone, PartialEq, Eq)]
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

pub struct Environment<'db> {
    declarations: HashMap<ConstantId<'db>, Declaration<'db>>,
}

impl<'db> Environment<'db> {
    pub fn new() -> Environment<'db> {
        Environment {
            declarations: HashMap::new(),
        }
    }

    pub fn contains(&self, name: &ConstantId<'db>) -> bool {
        self.declarations.contains_key(name)
    }

    pub fn get(&self, name: &ConstantId<'db>) -> Option<&Declaration<'db>> {
        self.declarations.get(name)
    }

    fn check_name(&self, name: &ConstantId<'db>) -> Result<(), Error<'db>> {
        if self.contains(name) {
            return Err(Error::AlreadyDefined(*name));
        } else {
            Ok(())
        }
    }

    pub fn add_declaration(&mut self, declaration: Declaration<'db>) -> Result<(), Error<'db>> {
        self.check_name(&declaration.name)?;
        self.declarations.insert(declaration.name, declaration);
        Ok(())
    }

    pub fn add_constant(
        &mut self,
        name: ConstantId<'db>,
        ty: RcSyntax<'db>,
        value: RcSyntax<'db>,
    ) -> Result<(), Error<'db>> {
        let declaration = Declaration::constant(name, ty, value);
        self.add_declaration(declaration)
    }

    pub fn add_type_constructor(
        &mut self,
        name: ConstantId<'db>,
        ty: RcSyntax<'db>,
    ) -> Result<(), Error<'db>> {
        let declaration = Declaration::type_constructor(name, ty);
        self.add_declaration(declaration)
    }

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
