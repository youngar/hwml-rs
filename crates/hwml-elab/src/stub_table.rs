use crate::util::surface_id_to_path;
use hwml_core::{QualifiedName, SourceRange};
use hwml_surface as surface;
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct DuplicateDefinitionError<'db> {
    pub name: QualifiedName<'db>,
    pub first_location: SourceRange<'db>,
    pub second_location: SourceRange<'db>,
}

impl<'db> std::fmt::Display for DuplicateDefinitionError<'db> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Duplicate definition of '{:?}' at {:?} (first defined at {:?})",
            self.name, self.second_location, self.first_location
        )
    }
}

impl<'db> std::error::Error for DuplicateDefinitionError<'db> {}

#[derive(Clone, Debug)]
pub struct StubTable<'db> {
    stubs: HashMap<QualifiedName<'db>, Stub<'db>>,
}

#[derive(Clone, Debug)]
pub struct Stub<'db> {
    pub source_range: SourceRange<'db>,
}

impl<'db> StubTable<'db> {
    pub fn new() -> Self {
        Self {
            stubs: HashMap::new(),
        }
    }

    pub fn contains(&self, name: QualifiedName<'db>) -> bool {
        self.stubs.contains_key(&name)
    }

    pub fn insert(
        &mut self,
        name: QualifiedName<'db>,
        _statement: surface::Statement,
        source_range: SourceRange<'db>,
    ) -> Result<(), DuplicateDefinitionError<'db>> {
        if let Some(existing) = self.stubs.get(&name) {
            return Err(DuplicateDefinitionError {
                name,
                first_location: existing.source_range.clone(),
                second_location: source_range.clone(),
            });
        }

        self.stubs.insert(name, Stub { source_range });
        Ok(())
    }

    pub fn get(&self, name: QualifiedName<'db>) -> Option<&Stub<'db>> {
        self.stubs.get(&name)
    }

    pub fn stubs(&self) -> impl Iterator<Item = (QualifiedName<'db>, &Stub<'db>)> {
        self.stubs.iter().map(|(name, stub)| (*name, stub))
    }

    pub fn len(&self) -> usize {
        self.stubs.len()
    }

    pub fn is_empty(&self) -> bool {
        self.stubs.is_empty()
    }
}

pub fn harvest_program<'db>(
    db: &'db dyn salsa::Database,
    stub_table: &mut StubTable<'db>,
    source: hwml_core::Source<'db>,
    namespace: QualifiedName<'db>,
    program: &surface::Program,
) -> Result<(), String> {
    harvest_statements(db, stub_table, source, namespace, &program.statements)
}

pub fn harvest_statements<'db>(
    db: &'db dyn salsa::Database,
    stub_table: &mut StubTable<'db>,
    source: hwml_core::Source<'db>,
    namespace: QualifiedName<'db>,
    statements: &[surface::Statement],
) -> Result<(), String> {
    for statement in statements {
        harvest_statement(db, stub_table, source, namespace, statement)?;
    }
    Ok(())
}

fn harvest_statement<'db>(
    db: &'db dyn salsa::Database,
    stub_table: &mut StubTable<'db>,
    source: hwml_core::Source<'db>,
    namespace: QualifiedName<'db>,
    statement: &surface::Statement,
) -> Result<(), String> {
    match statement {
        surface::Statement::Namespace(ns) => {
            harvest_namespace(db, stub_table, source, namespace, ns)?;
            Ok(())
        }
        surface::Statement::Def(def) => {
            let source_range = SourceRange::new(source, def.loc.clone());
            harvest_def(db, stub_table, namespace, def, source_range)?;
            Ok(())
        }
        surface::Statement::Meta(meta) => {
            let source_range = SourceRange::new(source, meta.loc.clone());
            harvest_meta(db, stub_table, namespace, meta, source_range)?;
            Ok(())
        }
        surface::Statement::Prim(prim) => {
            let source_range = SourceRange::new(source, prim.loc.clone());
            harvest_prim(db, stub_table, namespace, prim, source_range)?;
            Ok(())
        }
        surface::Statement::Inductive(ind) => {
            let source_range = SourceRange::new(source, ind.loc.clone());
            harvest_inductive(db, stub_table, namespace, ind, source_range)?;
            Ok(())
        }
        _ => Ok(()),
    }
}

fn harvest_namespace<'db>(
    db: &'db dyn salsa::Database,
    stub_table: &mut StubTable<'db>,
    source: hwml_core::Source<'db>,
    namespace: QualifiedName<'db>,
    ns: &surface::Namespace,
) -> Result<(), String> {
    // Extend the current namespace with the new new namespace, and recurse into
    // the namespace's statements.
    let path =
        surface_id_to_path(db, &ns.name).ok_or_else(|| "Invalid namespace name".to_string())?;
    let namespace = QualifiedName::qualify_path(db, Some(namespace), &path)
        .ok_or_else(|| "Failed to qualify namespace".to_string())?;
    for statement in &ns.statements {
        harvest_statement(db, stub_table, source, namespace, statement)?;
    }
    Ok(())
}

fn harvest_def<'db>(
    db: &'db dyn salsa::Database,
    stub_table: &mut StubTable<'db>,
    namespace: QualifiedName<'db>,
    def: &surface::Def,
    source_range: SourceRange<'db>,
) -> Result<(), String> {
    let path =
        surface_id_to_path(db, &def.id).ok_or_else(|| "Invalid definition name".to_string())?;
    let name = QualifiedName::qualify_path(db, Some(namespace), &path)
        .ok_or_else(|| "Failed to qualify definition name".to_string())?;
    stub_table
        .insert(name, surface::Statement::Def(def.clone()), source_range)
        .map_err(|e| e.to_string())?;
    Ok(())
}

fn harvest_meta<'db>(
    db: &'db dyn salsa::Database,
    stub_table: &mut StubTable<'db>,
    namespace: QualifiedName<'db>,
    meta: &surface::Meta,
    source_range: SourceRange<'db>,
) -> Result<(), String> {
    let path = surface_id_to_path(db, &meta.id).ok_or_else(|| "Invalid meta name".to_string())?;
    let name = QualifiedName::qualify_path(db, Some(namespace), &path)
        .ok_or_else(|| "Failed to qualify meta name".to_string())?;
    stub_table
        .insert(name, surface::Statement::Meta(meta.clone()), source_range)
        .map_err(|e| e.to_string())?;
    Ok(())
}

fn harvest_prim<'db>(
    db: &'db dyn salsa::Database,
    stub_table: &mut StubTable<'db>,
    namespace: QualifiedName<'db>,
    prim: &surface::Prim,
    source_range: SourceRange<'db>,
) -> Result<(), String> {
    let path =
        surface_id_to_path(db, &prim.id).ok_or_else(|| "Invalid primitive name".to_string())?;
    let name = QualifiedName::qualify_path(db, Some(namespace), &path)
        .ok_or_else(|| "Failed to qualify primitive name".to_string())?;
    stub_table
        .insert(name, surface::Statement::Prim(prim.clone()), source_range)
        .map_err(|e| e.to_string())?;
    Ok(())
}

fn harvest_inductive<'db>(
    db: &'db dyn salsa::Database,
    stub_table: &mut StubTable<'db>,
    namespace: QualifiedName<'db>,
    ind: &surface::Inductive,
    source_range: SourceRange<'db>,
) -> Result<(), String> {
    // Add the data type definition.
    let path =
        surface_id_to_path(db, &ind.name).ok_or_else(|| "Invalid inductive name".to_string())?;
    let name = QualifiedName::qualify_path(db, Some(namespace), &path)
        .ok_or_else(|| "Failed to qualify inductive name".to_string())?;
    stub_table
        .insert(
            name,
            surface::Statement::Inductive(ind.clone()),
            source_range.clone(),
        )
        .map_err(|e| e.to_string())?;

    // Add all constructors underneath the inductive's namespace.
    for constructor in &ind.constructors {
        let ctor_path = surface_id_to_path(db, &constructor.name)
            .ok_or_else(|| "Invalid constructor name".to_string())?;
        let ctor_name = QualifiedName::qualify_path(db, Some(name), &ctor_path)
            .ok_or_else(|| "Failed to qualify constructor name".to_string())?;
        let ctor_source_range = SourceRange::new(source_range.source, constructor.loc.clone());
        stub_table
            .insert(
                ctor_name,
                surface::Statement::Inductive(ind.clone()),
                ctor_source_range,
            )
            .map_err(|e| format!("Failed to register constructor: {}", e))?;
    }
    Ok(())
}
