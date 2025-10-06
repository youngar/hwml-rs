use std::collections::HashMap;

use crate::name::*;
use crate::syn::*;

pub struct DefinitionDecl {
    pub name: Name,
    pub ty: RcSyntax,
    pub value: RcSyntax,
}

pub struct ConstructorDecl {
    pub name: Name,
    pub ty: RcSyntax,
}

pub struct InductiveTypeDecl {
    pub name: Name,
    pub ty: RcSyntax,
    pub constructors: Vec<ConstructorDecl>,
}

pub struct DefinitionInfo {
    name: Name,
    ty: RcSyntax,
    value: RcSyntax,
}

pub struct InductiveTypeInfo {
    name: Name,
    ty: RcSyntax,
    constructors: Vec<Name>,
}

pub enum ConstantInfo {
    Definition(DefinitionInfo),
    InductiveType(InductiveTypeInfo),
}

impl ConstantInfo {
    pub fn name(&self) -> &Name {
        match self {
            ConstantInfo::Definition(d) => &d.name,
            ConstantInfo::InductiveType(t) => &t.name,
        }
    }

    pub fn ty(&self) -> &RcSyntax {
        match self {
            ConstantInfo::Definition(d) => &d.ty,
            ConstantInfo::InductiveType(t) => &t.ty,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Error {
    AlreadyDefined(Name),
}

pub struct Environment {
    constant_table: HashMap<Name, ConstantInfo>,
}

impl Environment {
    pub fn new() -> Environment {
        Environment {
            constant_table: HashMap::new(),
        }
    }

    pub fn contains(&self, name: &Name) -> bool {
        self.constant_table.contains_key(name)
    }

    fn check_name(&self, name: &Name) -> Result<(), Error> {
        if self.contains(name) {
            return Err(Error::AlreadyDefined(name.clone()));
        } else {
            Ok(())
        }
    }

    pub fn add_definition(&mut self, d: DefinitionDecl) -> Result<(), Error> {
        self.check_name(&d.name)?;

        // todo: type-check.
        self.constant_table.insert(
            d.name.clone(),
            ConstantInfo::Definition(DefinitionInfo {
                name: d.name,
                ty: d.ty,
                value: d.value,
            }),
        );
        Ok(())
    }

    pub fn add_inductive(&mut self, t: InductiveTypeDecl) -> Result<(), Error> {
        self.check_name(&t.name)?;
        self.constant_table.insert(
            t.name.clone(),
            ConstantInfo::InductiveType(InductiveTypeInfo {
                name: t.name,
                ty: t.ty,
                constructors: t.constructors.into_iter().map(|c| c.name).collect(),
            }),
        );
        Ok(())
    }
}
