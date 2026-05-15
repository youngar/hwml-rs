use crate::*;
use std::{collections::HashMap, fmt};
use syn::{RcSyntax, Telescope};

use val::{RcValue, Value};

/// Tracks transparent bindings (Let-bound variables) for δ-reduction.
#[derive(Clone, Debug)]
pub struct TransparentEnv<'db> {
    bindings: im::Vector<Option<RcValue<'db>>>,
}

impl<'db> TransparentEnv<'db> {
    pub fn new() -> Self {
        Self {
            bindings: im::Vector::new(),
        }
    }

    pub fn lookup(&self, level: Level) -> Option<RcValue<'db>> {
        let index: usize = level.into();
        self.bindings.get(index).and_then(|opt| opt.clone())
    }

    pub fn push_transparent(&mut self, value: RcValue<'db>) {
        self.bindings.push_back(Some(value));
    }

    pub fn push_rigid(&mut self) {
        self.bindings.push_back(None);
    }

    pub fn pop(&mut self) {
        self.bindings.pop_back();
    }

    pub fn truncate(&mut self, depth: usize) {
        self.bindings.truncate(depth);
    }

    pub fn depth(&self) -> usize {
        self.bindings.len()
    }
}

/// A mapping from bound variables to associated values.
#[derive(Clone, Debug)]
pub struct LocalEnv<'db> {
    /// The typing environment.
    locals: Vec<RcValue<'db>>,
}

impl<'db> LocalEnv<'db> {
    pub fn new() -> LocalEnv<'db> {
        Self { locals: Vec::new() }
    }

    pub fn get(&self, level: Level) -> &RcValue<'db> {
        let index: usize = level.into();
        &self.locals[index]
    }

    /// Set the value at a specific level.
    ///
    /// Used by pattern matching to turn a variable into a transparent let-binding
    /// when we learn its value (e.g., `n ~ @zero`). After this, any evaluation
    /// that looks up this level will see the new value instead of a rigid variable.
    pub fn set(&mut self, level: Level, value: RcValue<'db>) {
        let index: usize = level.into();
        self.locals[index] = value;
    }

    /// The number of bound variables in scope.
    pub fn depth(&self) -> usize {
        self.locals.len() as usize
    }

    /// Extend the environment by pushing a definition onto the end.
    pub fn push(&mut self, value: RcValue<'db>) {
        self.locals.push(value);
    }

    /// Extend the environment by pushing a variable onto the end.
    pub fn push_var(&mut self, ty: val::RcTy<'db>) -> RcValue<'db> {
        let depth = self.depth();
        let value = Value::variable_rc(Level::new(depth), ty);
        self.push(value.clone());
        value
    }

    pub fn pop(&mut self) {
        self.locals.pop();
    }

    /// Extend the environment with multiple values.
    pub fn extend<T>(&mut self, values: T)
    where
        T: IntoIterator<Item = RcValue<'db>>,
    {
        self.locals.extend(values);
    }

    /// Truncate the environment to the given depth.
    pub fn truncate(&mut self, depth: usize) {
        self.locals.truncate(depth);
    }

    pub fn extend_vars<T>(&mut self, types: T)
    where
        T: IntoIterator<Item = val::RcTy<'db>>,
    {
        for ty in types {
            self.push_var(ty);
        }
    }

    /// Iterate over the values in the environment.
    pub fn iter(&self) -> std::slice::Iter<'_, RcValue<'db>> {
        self.locals.iter()
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
pub enum Global<'db> {
    Constant(ConstantInfo<'db>),
    Primitive(PrimitiveInfo<'db>),
    TypeConstructor(TypeConstructorInfo<'db>),
    DataConstructor(DataConstructorInfo<'db>),
}

#[derive(Clone)]
pub struct GlobalEnv<'db> {
    /// Database reference for Salsa queries (needed for encode_type in quotation).
    /// Stored here to avoid threading through all evaluation functions.
    db: &'db dyn salsa::Database,
    /// Constant environment mapping QualifiedName to values.
    constants: HashMap<QualifiedName<'db>, Global<'db>>,
    /// Metavariable context mapping MetaVariableId to metavariable info.
    metavariables: HashMap<MetaVariableId, MetavariableInfo<'db>>,
}

// Manual Debug impl because salsa::Database doesn't implement Debug
impl<'db> fmt::Debug for GlobalEnv<'db> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("GlobalEnv")
            .field("db", &"<dyn Database>")
            .field("constants", &self.constants)
            .field("metavariables", &self.metavariables)
            .finish()
    }
}

impl<'db> GlobalEnv<'db> {
    pub fn new(db: &'db dyn salsa::Database) -> Self {
        Self {
            db,
            constants: HashMap::new(),
            metavariables: HashMap::new(),
        }
    }

    /// Get the database reference
    pub fn db(&self) -> &'db dyn salsa::Database {
        self.db
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
        Args: Into<Telescope<'db>>,
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

#[derive(Clone, Debug)]
pub struct ConstantInfo<'db> {
    pub ty: RcSyntax<'db>,
    pub value: RcSyntax<'db>,
    /// If `true`, the evaluator treats this constant as opaque (irreducible).
    /// This is used during mutual recursion: constants in an SCC are marked
    /// opaque during body elaboration to prevent infinite loops.
    pub is_opaque: bool,
}

impl<'db> ConstantInfo<'db> {
    pub fn new(ty: RcSyntax<'db>, value: RcSyntax<'db>) -> Self {
        ConstantInfo {
            ty,
            value,
            is_opaque: false, // Default: transparent (can be reduced)
        }
    }

    /// Create an opaque constant stub (for use during mutual recursion).
    pub fn new_opaque(ty: RcSyntax<'db>, value: RcSyntax<'db>) -> Self {
        ConstantInfo {
            ty,
            value,
            is_opaque: true,
        }
    }

    /// Mark this constant as transparent (allow reduction).
    pub fn set_transparent(&mut self) {
        self.is_opaque = false;
    }

    /// Mark this constant as opaque (block reduction).
    pub fn set_opaque(&mut self) {
        self.is_opaque = true;
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
    pub arguments: Telescope<'db>,
    pub num_parameters: usize,
    pub level: UniverseLevel,
    /// The data constructors belonging to this type constructor.
    pub constructors: Vec<QualifiedName<'db>>,
}

impl<'db> TypeConstructorInfo<'db> {
    pub fn new<Args>(args: Args, num_parameters: usize, level: UniverseLevel) -> Self
    where
        Args: Into<Telescope<'db>>,
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

    pub fn parameters(&self) -> impl Iterator<Item = &RcSyntax<'db>> {
        self.arguments.cells[..self.num_parameters]
            .iter()
            .map(|c| &c.ty)
    }

    pub fn indices(&self) -> impl Iterator<Item = &RcSyntax<'db>> {
        self.arguments.cells[self.num_parameters..]
            .iter()
            .map(|c| &c.ty)
    }

    pub fn constructors(&self) -> &[QualifiedName<'db>] {
        &self.constructors
    }
}

#[derive(Clone, Debug)]
pub struct DataConstructorInfo<'db> {
    pub arguments: Telescope<'db>,
    pub ty: RcSyntax<'db>,
}

impl<'db> DataConstructorInfo<'db> {
    pub fn new<Args>(args: Args, ty: RcSyntax<'db>) -> Self
    where
        Args: Into<Telescope<'db>>,
    {
        DataConstructorInfo {
            arguments: args.into(),
            ty,
        }
    }
}

#[derive(Clone, Debug)]
pub struct MetavariableInfo<'db> {
    /// The telescope of argument types (the substitution).
    pub arguments: Telescope<'db>,
    /// The final type of the metavariable.
    pub ty: RcSyntax<'db>,
}

impl<'db> MetavariableInfo<'db> {
    pub fn new<Args>(args: Args, ty: RcSyntax<'db>) -> Self
    where
        Args: Into<Telescope<'db>>,
    {
        MetavariableInfo {
            arguments: args.into(),
            ty,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Environment<'db, 'g> {
    pub global: &'g GlobalEnv<'db>,
    pub local: LocalEnv<'db>,
    pub transparent: TransparentEnv<'db>,
}

impl<'db, 'g> Environment<'db, 'g> {
    pub fn new(global: &'g GlobalEnv<'db>) -> Self {
        Self {
            global,
            local: LocalEnv::new(),
            transparent: TransparentEnv::new(),
        }
    }

    // Forwarding methods to GlobalEnv

    /// Lookup a type constructor by name.
    pub fn type_constructor(
        &self,
        name: QualifiedName<'db>,
    ) -> Result<&TypeConstructorInfo<'db>, LookupError<'_>> {
        self.global.type_constructor(name)
    }

    /// Lookup a data constructor by name.
    pub fn data_constructor(
        &self,
        name: QualifiedName<'db>,
    ) -> Result<&DataConstructorInfo<'db>, LookupError<'_>> {
        self.global.data_constructor(name)
    }

    // Forwarding methods to LocalEnv

    /// Get a local variable by level.
    /// Returns the rigid variable representation.
    /// NOTE: Does NOT unfold transparent bindings - that's the job of the conversion checker!
    pub fn get(&self, level: Level) -> RcValue<'db> {
        self.local.get(level).clone()
    }

    pub fn set(&mut self, level: Level, value: RcValue<'db>) {
        self.local.set(level, value)
    }

    /// The number of bound variables in scope.
    pub fn depth(&self) -> usize {
        self.local.depth()
    }

    /// Extend the environment by pushing a definition onto the end.
    /// This is rigid (not transparent) by default.
    pub fn push(&mut self, value: RcValue<'db>) {
        self.transparent.push_rigid();
        self.local.push(value)
    }

    /// Extend the environment by pushing a variable onto the end.
    pub fn push_var(&mut self, ty: val::RcTy<'db>) -> RcValue<'db> {
        self.transparent.push_rigid();
        self.local.push_var(ty)
    }

    /// Extend the environment with multiple variables.
    pub fn extend_vars<T>(&mut self, types: T)
    where
        T: IntoIterator<Item = val::RcTy<'db>>,
    {
        for ty in types {
            self.push_var(ty);
        }
    }

    /// Push a transparent binding (for Let expressions).
    /// This adds both the variable to the local environment and tracks it as transparent.
    pub fn push_transparent(
        &mut self,
        ty: val::RcTy<'db>,
        value: RcValue<'db>,
    ) -> RcValue<'db> {
        let var = self.local.push_var(ty);
        self.transparent.push_transparent(value);
        var
    }

    /// Look up a transparent binding for a variable.
    pub fn lookup_transparent(&self, level: Level) -> Option<RcValue<'db>> {
        self.transparent.lookup(level)
    }

    /// Pop the last value from the local environment.
    pub fn pop(&mut self) {
        self.local.pop();
        self.transparent.pop();
    }

    /// Get the length of the local environment.
    pub fn len(&self) -> usize {
        self.local.depth()
    }

    /// Truncate the local environment to the given depth.
    pub fn truncate(&mut self, depth: usize) {
        self.local.truncate(depth);
        self.transparent.truncate(depth);
    }
}

impl<'db, 'g> Extend<RcValue<'db>> for Environment<'db, 'g> {
    fn extend<T>(&mut self, iter: T)
    where
        T: IntoIterator<Item = RcValue<'db>>,
    {
        self.local.locals.extend(iter);
    }
}
