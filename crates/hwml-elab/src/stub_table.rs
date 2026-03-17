use crate::resolver::Resolver;
use hwml_core::{Name, QualifiedName};
use hwml_support::{FromWithDb, Location};
use hwml_surface as surface;
use std::collections::HashMap;

pub fn harvest_declarations<'db>(
    db: &'db dyn salsa::Database,
    program: &surface::Program,
    stub_table: &mut StubTable<'db>,
    resolver: &Resolver<'db>,
) -> Result<(), String> {
    stub_table.harvest(db, program, resolver)
}

#[derive(Clone, Debug)]
pub struct StubTable<'db> {
    stubs: HashMap<QualifiedName<'db>, Stub>,
}

#[derive(Clone, Debug)]
pub struct Stub {
    pub statement: surface::Statement,
    pub location: Location,
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
        statement: surface::Statement,
        location: Location,
    ) -> Result<(), DuplicateDefinitionError<'db>> {
        if let Some(existing) = self.stubs.get(&name) {
            return Err(DuplicateDefinitionError {
                name,
                first_location: existing.location,
                second_location: location,
            });
        }

        self.stubs.insert(
            name,
            Stub {
                statement,
                location,
            },
        );
        Ok(())
    }

    pub fn get(&self, name: QualifiedName<'db>) -> Option<&Stub> {
        self.stubs.get(&name)
    }

    pub fn stubs(&self) -> impl Iterator<Item = (QualifiedName<'db>, &Stub)> {
        self.stubs.iter().map(|(name, stub)| (*name, stub))
    }

    pub fn len(&self) -> usize {
        self.stubs.len()
    }

    pub fn is_empty(&self) -> bool {
        self.stubs.is_empty()
    }

    pub fn harvest(
        &mut self,
        db: &'db dyn salsa::Database,
        program: &surface::Program,
        resolver: &Resolver<'db>,
    ) -> Result<(), String> {
        let mut current_resolver = resolver.clone();
        for statement in &program.statements {
            current_resolver = self.harvest_statement(db, statement, &current_resolver)?;
        }
        Ok(())
    }

    fn harvest_statement(
        &mut self,
        db: &'db dyn salsa::Database,
        statement: &surface::Statement,
        resolver: &Resolver<'db>,
    ) -> Result<Resolver<'db>, String> {
        match statement {
            surface::Statement::Namespace(ns) => {
                self.harvest_namespace(db, ns, resolver)?;
                Ok(resolver.clone())
            }
            surface::Statement::Def(def) => {
                self.harvest_def(db, def, resolver)?;
                Ok(resolver.clone())
            }
            surface::Statement::Meta(meta) => {
                self.harvest_meta(db, meta, resolver)?;
                Ok(resolver.clone())
            }
            surface::Statement::Prim(prim) => {
                self.harvest_prim(db, prim, resolver)?;
                Ok(resolver.clone())
            }
            surface::Statement::Inductive(ind) => {
                self.harvest_inductive(db, ind, resolver)?;
                Ok(resolver.clone())
            }
            surface::Statement::Open(open) => self.harvest_open(db, open, resolver),
        }
    }

    fn harvest_namespace(
        &mut self,
        db: &'db dyn salsa::Database,
        ns: &surface::Namespace,
        resolver: &Resolver<'db>,
    ) -> Result<(), String> {
        let segments: Vec<&[u8]> = ns.name.segments().collect();

        // Fold over the segments, pushing each one onto the resolver
        let mut nested_resolver = resolver.clone();
        for segment_bytes in segments {
            let segment_str = std::str::from_utf8(segment_bytes)
                .map_err(|e| format!("Invalid UTF-8 in namespace segment: {}", e))?;
            let segment_name = Name::from_with_db(db, segment_str);
            nested_resolver = nested_resolver.push_namespace(db, segment_name);
        }

        // Recursively harvest all nested statements with the fully extended resolver
        for statement in &ns.statements {
            self.harvest_statement(db, statement, &nested_resolver)?;
        }

        // The namespace is automatically popped when nested_resolver goes out of scope
        Ok(())
    }

    /// Harvest a `def` statement.
    /// Supports qualified names like `Math.Algebra.add`.
    fn harvest_def(
        &mut self,
        db: &'db dyn salsa::Database,
        def: &surface::Def,
        resolver: &Resolver<'db>,
    ) -> Result<(), String> {
        let path = surface_id_to_path(db, &def.id)?;

        // Split into namespace segments and definition name
        let (namespace_segments, def_name) = path.split_at(path.len() - 1);
        let def_name = def_name[0]; // Last segment is the definition name

        // Extend the resolver with namespace segments
        let mut extended_resolver = resolver.clone();
        for &segment in namespace_segments {
            extended_resolver = extended_resolver.push_namespace(db, segment);
        }

        // Qualify the definition name with the extended namespace
        let qualified_name = extended_resolver.qualify(db, def_name);

        // Insert the unelaborated statement into the stub table
        let statement = surface::Statement::Def(def.clone());
        self.insert(qualified_name, statement, Location::UNKNOWN)
            .map_err(|e| e.to_string())?;

        println!("[Harvesting] def: {}", qualified_name.to_string(db));

        Ok(())
    }

    /// Harvest a `meta` statement.
    /// Supports qualified names like `Math.Algebra.meta_var`.
    fn harvest_meta(
        &mut self,
        db: &'db dyn salsa::Database,
        meta: &surface::Meta,
        resolver: &Resolver<'db>,
    ) -> Result<(), String> {
        let path = surface_id_to_path(db, &meta.id)?;

        // Split into namespace segments and definition name
        let (namespace_segments, meta_name) = path.split_at(path.len() - 1);
        let meta_name = meta_name[0];

        // Extend the resolver with namespace segments
        let mut extended_resolver = resolver.clone();
        for &segment in namespace_segments {
            extended_resolver = extended_resolver.push_namespace(db, segment);
        }

        let qualified_name = extended_resolver.qualify(db, meta_name);

        let statement = surface::Statement::Meta(meta.clone());
        self.insert(qualified_name, statement, Location::UNKNOWN)
            .map_err(|e| e.to_string())?;

        println!("[Harvesting] meta: {}", qualified_name.to_string(db));

        Ok(())
    }

    /// Harvest a `prim` statement.
    /// Supports qualified names like `Math.Algebra.prim_op`.
    fn harvest_prim(
        &mut self,
        db: &'db dyn salsa::Database,
        prim: &surface::Prim,
        resolver: &Resolver<'db>,
    ) -> Result<(), String> {
        let path = surface_id_to_path(db, &prim.id)?;

        // Split into namespace segments and definition name
        let (namespace_segments, prim_name) = path.split_at(path.len() - 1);
        let prim_name = prim_name[0];

        // Extend the resolver with namespace segments
        let extended_resolver = resolver.extend(db, namespace_segments);

        let qualified_name = extended_resolver.qualify(db, prim_name);

        let statement = surface::Statement::Prim(prim.clone());
        self.insert(qualified_name, statement, Location::UNKNOWN)
            .map_err(|e| e.to_string())?;

        println!("[Harvesting] prim: {}", qualified_name.to_string(db));

        Ok(())
    }

    /// Harvest an `inductive` statement.
    /// Supports qualified names like `Math.Algebra.Nat`.
    /// Also registers all data constructors in the stub table.
    fn harvest_inductive(
        &mut self,
        db: &'db dyn salsa::Database,
        ind: &surface::Inductive,
        resolver: &Resolver<'db>,
    ) -> Result<(), String> {
        let path = surface_id_to_path(db, &ind.name)?;

        // Split into namespace segments and type name
        let (namespace_segments, type_name) = path.split_at(path.len() - 1);
        let type_name = type_name[0];

        // Extend the resolver with namespace segments
        let mut extended_resolver = resolver.clone();
        for &segment in namespace_segments {
            extended_resolver = extended_resolver.push_namespace(db, segment);
        }

        let qualified_name = extended_resolver.qualify(db, type_name);

        // Register the inductive type itself
        let statement = surface::Statement::Inductive(ind.clone());
        self.insert(qualified_name, statement, Location::UNKNOWN)
            .map_err(|e| e.to_string())?;

        println!("[Harvesting] inductive: {}", qualified_name.to_string(db));

        // Register each data constructor
        // Constructors are placed in the same namespace as the inductive type
        for constructor in &ind.constructors {
            let ctor_path = surface_id_to_path(db, &constructor.name)?;

            // Constructors can also have qualified names
            let (ctor_namespace_segments, ctor_name) = ctor_path.split_at(ctor_path.len() - 1);
            let ctor_name = ctor_name[0];

            // Extend the resolver with constructor's namespace segments
            let mut ctor_resolver = extended_resolver.clone();
            for &segment in ctor_namespace_segments {
                ctor_resolver = ctor_resolver.push_namespace(db, segment);
            }

            let ctor_qualified_name = ctor_resolver.qualify(db, ctor_name);

            // LIMITATION: Constructors are registered as synthetic Def statements.
            // This is incorrect but allows name resolution to work during the harvesting pass.
            // The constructor's type is used as its "value" (nonsensical), and parameters are
            // ignored (empty bindings). Proper constructor elaboration will replace this when
            // we implement the elaboration pass, which will generate correct constructor terms
            // with proper parameter handling and type-directed construction.
            let ctor_def = surface::Def::new(
                constructor.name.clone(),
                surface::Bindings::new(vec![]),
                Some(constructor.ty.clone()),
                constructor.ty.clone(), // Placeholder: type used as value
            );
            let ctor_statement = surface::Statement::Def(ctor_def);

            self.insert(ctor_qualified_name, ctor_statement, Location::UNKNOWN)
                .map_err(|e| {
                    format!(
                        "Failed to register constructor {}: {}",
                        ctor_name.to_string(db),
                        e
                    )
                })?;

            println!(
                "[Harvesting]   constructor: {}",
                ctor_qualified_name.to_string(db)
            );
        }

        Ok(())
    }

    /// Harvest an `open` statement.
    /// This converts the surface open statement into an OpenDirective and adds it to the resolver.
    fn harvest_open(
        &mut self,
        db: &'db dyn salsa::Database,
        open: &surface::Open,
        resolver: &Resolver<'db>,
    ) -> Result<Resolver<'db>, String> {
        // Parse the namespace (which might be a qualified name like Math.Algebra)
        // Use the segments() method to split by dots
        let segments: Vec<&[u8]> = open.namespace.segments().collect();

        // Build the qualified name by chaining segments
        let mut qualified_ns: Option<QualifiedName<'db>> = None;
        for segment_bytes in segments {
            let segment_str = std::str::from_utf8(segment_bytes)
                .map_err(|e| format!("Invalid UTF-8 in namespace segment: {}", e))?;
            let name = Name::from_with_db(db, segment_str);
            qualified_ns = Some(QualifiedName::new(db, qualified_ns, name));
        }

        let namespace =
            qualified_ns.ok_or_else(|| "Empty namespace in open statement".to_string())?;

        // Convert surface modifiers to elab modifiers
        let mut modifiers = Vec::new();
        for modifier in &open.modifiers {
            match modifier {
                surface::OpenModifier::Only(_loc, ids) => {
                    let paths: Result<Vec<Vec<Name<'db>>>, String> =
                        ids.iter().map(|id| surface_id_to_path(db, id)).collect();
                    // TODO: Convert surface location (Range<usize>) to elaborator Location
                    // For now, use UNKNOWN since we don't have a SourceFile context here
                    modifiers.push(crate::resolver::OpenModifier::Only(
                        paths?,
                        Location::UNKNOWN,
                    ));
                }
                surface::OpenModifier::Hiding(_loc, ids) => {
                    let paths: Result<Vec<Vec<Name<'db>>>, String> =
                        ids.iter().map(|id| surface_id_to_path(db, id)).collect();
                    // TODO: Convert surface location (Range<usize>) to elaborator Location
                    modifiers.push(crate::resolver::OpenModifier::Hiding(
                        paths?,
                        Location::UNKNOWN,
                    ));
                }
                surface::OpenModifier::Renaming(_loc, from, to) => {
                    let from_path = surface_id_to_path(db, from)?;
                    let to_path = surface_id_to_path(db, to)?;
                    // TODO: Convert surface location (Range<usize>) to elaborator Location
                    modifiers.push(crate::resolver::OpenModifier::Renaming(
                        from_path,
                        to_path,
                        Location::UNKNOWN,
                    ));
                }
            }
        }

        // Convert the optional alias
        let as_alias = if let Some(alias_id) = &open.as_alias {
            Some(surface_id_to_name(db, alias_id)?)
        } else {
            None
        };

        // Create the directive
        let directive = crate::resolver::OpenDirective {
            namespace,
            modifiers,
            as_alias,
        };

        println!(
            "[Pre-Pass] Processing open directive: {} (alias: {:?})",
            namespace.to_string(db),
            as_alias.map(|a| format!("{:?}", a))
        );

        // Return a new resolver with the directive added
        Ok(resolver.clone().add_open_directive(directive))
    }
}

// ============================================================================
// Helper Functions
// ============================================================================

/// Convert a surface Id to a core Name (single segment only).
///
/// This function handles simple identifiers without dots.
/// For qualified names, use `surface_id_to_path` instead.
fn surface_id_to_name<'db>(
    db: &'db dyn salsa::Database,
    id: &surface::Id,
) -> Result<Name<'db>, String> {
    // Convert bytes to a string
    let name_str = std::str::from_utf8(&id.value)
        .map_err(|e| format!("Invalid UTF-8 in identifier: {}", e))?;

    // Check if this is a qualified name (contains dots)
    if name_str.contains('.') {
        return Err(format!(
            "Expected simple identifier, got qualified name: {}. \
             Use surface_id_to_path for qualified names.",
            name_str
        ));
    }

    Ok(Name::from_with_db(db, name_str))
}

/// Convert a surface Id to a vector of Names (path segments).
///
/// This handles both simple identifiers (single segment) and qualified names (multiple segments).
/// For example:
/// - "add" -> ["add"]
/// - "Math.Algebra.add" -> ["Math", "Algebra", "add"]
fn surface_id_to_path<'db>(
    db: &'db dyn salsa::Database,
    id: &surface::Id,
) -> Result<Vec<Name<'db>>, String> {
    let segments: Vec<&[u8]> = id.segments().collect();

    let mut names = Vec::new();
    for segment in segments {
        let segment_str = std::str::from_utf8(segment)
            .map_err(|e| format!("Invalid UTF-8 in identifier segment: {}", e))?;
        names.push(Name::from_with_db(db, segment_str));
    }

    // The parser should never produce empty identifiers
    debug_assert!(
        !names.is_empty(),
        "Parser should never produce empty identifiers"
    );

    Ok(names)
}

/// Error returned when trying to insert a duplicate definition.
#[derive(Debug, Clone)]
pub struct DuplicateDefinitionError<'db> {
    pub name: QualifiedName<'db>,
    pub first_location: Location,
    pub second_location: Location,
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
