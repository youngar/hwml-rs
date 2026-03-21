use crate::*;
use std::collections::HashMap;
use std::fmt;

#[derive(Clone, Debug)]
pub struct ConstantInfo<'db> {
    pub ty: RcSyntax<'db>,
    pub value: RcSyntax<'db>,
}

impl<'db> ConstantInfo<'db> {
    pub fn new(ty: RcSyntax<'db>, value: RcSyntax<'db>) -> Self {
        ConstantInfo { ty, value }
    }
}

#[derive(Clone, Debug)]
pub struct PrimitiveInfo<'db> {
    pub ty: RcSyntax<'db>,
}

impl<'db> PrimitiveInfo<'db> {
    pub fn new(ty: RcSyntax<'db>) -> Self {
        PrimitiveInfo { ty }
    }
}

#[derive(Clone, Debug)]
pub struct TypeConstructorInfo<'db> {
    pub arguments: syn::Telescope<'db>,
    pub num_parameters: usize,
    pub level: UniverseLevel,
    /// The data constructors belonging to this type constructor.
    pub constructors: Vec<QualifiedName<'db>>,
}

impl<'db> TypeConstructorInfo<'db> {
    pub fn new<Args>(args: Args, num_parameters: usize, level: UniverseLevel) -> Self
    where
        Args: Into<syn::Telescope<'db>>,
    {
        TypeConstructorInfo {
            arguments: args.into(),
            num_parameters,
            level,
            constructors: Vec::new(),
        }
    }

    pub fn num_parameters(&self) -> usize {
        self.num_parameters
    }

    pub fn num_indices(&self) -> usize {
        self.arguments.len() - self.num_parameters
    }

    pub fn parameters(&self) -> &[RcSyntax<'db>] {
        &self.arguments.bindings[..self.num_parameters]
    }

    pub fn indices(&self) -> &[RcSyntax<'db>] {
        &self.arguments.bindings[self.num_parameters..]
    }

    pub fn constructors(&self) -> &[QualifiedName<'db>] {
        &self.constructors
    }
}

#[derive(Clone, Debug)]
pub struct DataConstructorInfo<'db> {
    pub arguments: syn::Telescope<'db>,
    pub ty: RcSyntax<'db>,
}

impl<'db> DataConstructorInfo<'db> {
    pub fn new<Args>(args: Args, ty: RcSyntax<'db>) -> Self
    where
        Args: Into<syn::Telescope<'db>>,
    {
        DataConstructorInfo {
            arguments: args.into(),
            ty,
        }
    }

    pub fn arity(&self) -> usize {
        self.arguments.len()
    }
}

#[derive(Clone, Debug)]
pub struct MetavariableInfo<'db> {
    /// The telescope of argument types (the substitution).
    pub arguments: syn::Telescope<'db>,
    /// The final type of the metavariable.
    pub ty: RcSyntax<'db>,
}

impl<'db> MetavariableInfo<'db> {
    pub fn new<Args>(args: Args, ty: RcSyntax<'db>) -> Self
    where
        Args: Into<syn::Telescope<'db>>,
    {
        MetavariableInfo {
            arguments: args.into(),
            ty,
        }
    }
}

#[derive(Clone, Debug)]
pub enum Global<'db> {
    Constant(ConstantInfo<'db>),
    Primitive(PrimitiveInfo<'db>),
    TypeConstructor(TypeConstructorInfo<'db>),
    DataConstructor(DataConstructorInfo<'db>),
}

#[derive(Debug, Clone)]
pub struct LookupError<'db> {
    pub kind: LookupErrorKind,
    pub id: QualifiedName<'db>,
}

impl<'db> fmt::Display for LookupError<'db> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.kind)
    }
}

#[derive(Debug, Clone)]
pub enum LookupErrorKind {
    UnknownConstant,
    NotConstant,
    NotTypeConstructor,
    NotDataConstructor,
    NotPrimitive,
}

impl<'db> fmt::Display for LookupErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnknownConstant => f.write_str("unknown constant"),
            Self::NotConstant => f.write_str("not a constant"),
            Self::NotTypeConstructor => f.write_str("not a type constructor"),
            Self::NotDataConstructor => f.write_str("not a data constructor"),
            Self::NotPrimitive => f.write_str("not a primitive"),
        }
    }
}

/// Result type for looking up a specific kind of global definition.
#[derive(Debug, Clone)]
pub enum LookupResult<'a, T> {
    /// The lookup succeeded and found the expected type.
    Found(&'a T),
    /// The constant exists but is not of the expected type.
    WrongKind(LookupErrorKind),
    /// The constant does not exist.
    NotFound,
}

#[derive(Debug, Clone)]
pub struct MetaVariableLookupError {
    pub id: MetaVariableId,
}

impl fmt::Display for MetaVariableLookupError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "unknown metavariable: {}", self.id)
    }
}

#[derive(Clone, Debug)]
pub struct GlobalEnv<'db> {
    /// Constant environment mapping QualifiedName to values.
    constants: HashMap<QualifiedName<'db>, Global<'db>>,
    /// Metavariable context mapping MetaVariableId to metavariable info.
    metavariables: HashMap<MetaVariableId, MetavariableInfo<'db>>,
}

impl<'db> GlobalEnv<'db> {
    pub fn new() -> Self {
        Self {
            constants: HashMap::new(),
            metavariables: HashMap::new(),
        }
    }

    pub fn contains(&self, name: QualifiedName<'db>) -> bool {
        self.constants.contains_key(&name)
    }

    /// Lookup a constant by name.
    pub fn constant(
        &self,
        name: QualifiedName<'db>,
    ) -> Result<&ConstantInfo<'db>, LookupError<'db>> {
        match self.constants.get(&name) {
            Some(Global::Constant(info)) => Ok(info),
            Some(_) => Err(LookupError {
                kind: LookupErrorKind::NotConstant,
                id: name,
            }),
            None => Err(LookupError {
                kind: LookupErrorKind::UnknownConstant,
                id: name,
            }),
        }
    }

    /// Add a constant to the global environment.
    pub fn add_constant(&mut self, name: QualifiedName<'db>, info: ConstantInfo<'db>) {
        self.constants.insert(name, Global::Constant(info));
    }

    /// Lookup a primitive by name.
    pub fn primitive(
        &self,
        name: QualifiedName<'db>,
    ) -> Result<&PrimitiveInfo<'db>, LookupError<'db>> {
        match self.constants.get(&name) {
            Some(Global::Primitive(info)) => Ok(info),
            Some(_) => Err(LookupError {
                kind: LookupErrorKind::NotPrimitive,
                id: name,
            }),
            None => Err(LookupError {
                kind: LookupErrorKind::UnknownConstant,
                id: name,
            }),
        }
    }

    /// Add a primitive to the global environment.
    pub fn add_primitive(&mut self, name: QualifiedName<'db>, info: PrimitiveInfo<'db>) {
        self.constants.insert(name, Global::Primitive(info));
    }

    /// Lookup a type constructor by name.
    pub fn type_constructor(
        &self,
        name: QualifiedName<'db>,
    ) -> Result<&TypeConstructorInfo<'db>, LookupError<'db>> {
        match self.constants.get(&name) {
            Some(Global::TypeConstructor(info)) => Ok(info),
            Some(_) => Err(LookupError {
                kind: LookupErrorKind::NotTypeConstructor,
                id: name,
            }),
            None => Err(LookupError {
                kind: LookupErrorKind::UnknownConstant,
                id: name,
            }),
        }
    }

    /// Add a type constructor to the global environment.
    pub fn add_type_constructor(
        &mut self,
        name: QualifiedName<'db>,
        info: TypeConstructorInfo<'db>,
    ) {
        self.constants.insert(name, Global::TypeConstructor(info));
    }

    /// Lookup a data constructor by name.
    pub fn data_constructor(
        &self,
        name: QualifiedName<'db>,
    ) -> Result<&DataConstructorInfo<'db>, LookupError<'db>> {
        match self.constants.get(&name) {
            Some(Global::DataConstructor(info)) => Ok(info),
            Some(_) => Err(LookupError {
                kind: LookupErrorKind::NotDataConstructor,
                id: name,
            }),
            None => Err(LookupError {
                kind: LookupErrorKind::UnknownConstant,
                id: name,
            }),
        }
    }

    /// Add a data constructor to the global environment.
    pub fn add_data_constructor(
        &mut self,
        name: QualifiedName<'db>,
        info: DataConstructorInfo<'db>,
    ) {
        self.constants.insert(name, Global::DataConstructor(info));
    }

    /// Add a metavariable with its type to the global environment.
    pub fn add_metavariable<Args>(&mut self, id: MetaVariableId, args: Args, ty: RcSyntax<'db>)
    where
        Args: Into<syn::Telescope<'db>>,
    {
        self.metavariables
            .insert(id, MetavariableInfo::new(args, ty));
    }

    /// Lookup metavariable info by id.
    pub fn metavariable(
        &self,
        id: MetaVariableId,
    ) -> Result<&MetavariableInfo<'db>, MetaVariableLookupError> {
        self.metavariables
            .get(&id)
            .ok_or(MetaVariableLookupError { id })
    }

    /// Iterate over all metavariables in the global environment.
    pub fn iter_metavariables(
        &self,
    ) -> impl Iterator<Item = (&MetaVariableId, &MetavariableInfo<'db>)> {
        self.metavariables.iter()
    }

    /// Get the maximum metavariable ID in the global environment, or None if empty.
    pub fn max_metavariable_id(&self) -> Option<MetaVariableId> {
        self.metavariables.keys().max().copied()
    }
}
