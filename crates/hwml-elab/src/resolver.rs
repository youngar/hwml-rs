use crate::dubbing::DubbingTable;
use crate::stub_table::StubTable;
use hwml_core::*;
use std::rc::Rc;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum OpenModifier<'db> {
    Only(Vec<Vec<Name<'db>>>, Option<SourceRange<'db>>),
    Hiding(Vec<Vec<Name<'db>>>, Option<SourceRange<'db>>),
    Renaming(Vec<Name<'db>>, Vec<Name<'db>>, Option<SourceRange<'db>>),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct OpenDirective<'db> {
    pub namespace: QualifiedName<'db>,
    pub modifiers: Vec<OpenModifier<'db>>,
    pub as_alias: Option<Name<'db>>,
}

impl<'db> OpenDirective<'db> {
    pub fn new(namespace: QualifiedName<'db>) -> Self {
        OpenDirective {
            namespace,
            modifiers: Vec::new(),
            as_alias: None,
        }
    }

    pub fn with_modifiers(
        namespace: QualifiedName<'db>,
        modifiers: Vec<OpenModifier<'db>>,
    ) -> Self {
        OpenDirective {
            namespace,
            modifiers,
            as_alias: None,
        }
    }

    pub fn with_alias(namespace: QualifiedName<'db>, alias: Name<'db>) -> Self {
        OpenDirective {
            namespace,
            modifiers: Vec::new(),
            as_alias: Some(alias),
        }
    }

    /// Check if a name should be imported according to the modifiers.
    /// Returns None if the name is filtered out, or Some(internal_name) with renaming applied.
    ///
    /// CRITICAL: Order of operations matters!
    /// 1. Apply ALL renamings first to get the internal name
    /// 2. Then check Only/Hiding filters against the internal name
    ///
    /// NOTE: Currently only matches the first segment of paths. Full path matching
    /// (e.g., `Algebra.add` vs `Geometry.add`) will be handled by the elaborator
    /// when it processes projection tails.
    fn apply_modifiers(&self, name: Name<'db>) -> Option<Name<'db>> {
        // Step 1: Resolve all renamings to get the internal name
        // If user typed 'to', we need to look up 'from' in the namespace
        // For paths, we only match the first segment
        let mut internal_name = name;
        for modifier in &self.modifiers {
            if let OpenModifier::Renaming(from_path, to_path, _loc) = modifier {
                // Only match if the first segment of to_path matches the name
                if let Some(&to_first) = to_path.first() {
                    if name == to_first {
                        // Rewrite to the first segment of from_path
                        if let Some(&from_first) = from_path.first() {
                            internal_name = from_first;
                        }
                    }
                }
            }
        }

        // Step 2: Apply filters to the internal name
        let mut has_only = false;
        let mut in_only_list = false;

        for modifier in &self.modifiers {
            match modifier {
                OpenModifier::Only(paths, _loc) => {
                    has_only = true;
                    // Check if the internal name matches the first segment of any path
                    for path in paths {
                        if let Some(&first) = path.first() {
                            if internal_name == first {
                                in_only_list = true;
                                break;
                            }
                        }
                    }
                }
                OpenModifier::Hiding(paths, _loc) => {
                    // Check if the internal name matches the first segment of any path
                    for path in paths {
                        if let Some(&first) = path.first() {
                            if internal_name == first {
                                return None; // Explicitly hidden
                            }
                        }
                    }
                }
                OpenModifier::Renaming(_, _, _loc) => {
                    // Already handled in step 1
                }
            }
        }

        // If there's an Only modifier and the internal name isn't in the list, filter it out
        if has_only && !in_only_list {
            return None;
        }

        Some(internal_name)
    }
}

/// Errors that can occur during name resolution.
#[derive(Debug, Clone)]
pub enum ResolutionError<'db> {
    /// The path was not found in any scope
    UnknownIdentifier(Vec<Name<'db>>),
    /// The path resolves to multiple definitions from different opened namespaces
    AmbiguousIdentifier(Vec<Name<'db>>, Vec<QualifiedName<'db>>),
}

impl<'db> std::fmt::Display for ResolutionError<'db> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ResolutionError::UnknownIdentifier(path) => {
                write!(f, "Unknown identifier: {:?}", path)
            }
            ResolutionError::AmbiguousIdentifier(path, candidates) => {
                write!(
                    f,
                    "Ambiguous identifier: {:?} could refer to any of: {:?}",
                    path, candidates
                )
            }
        }
    }
}

impl<'db> std::error::Error for ResolutionError<'db> {}

/// Helper function to extend a base qualified name with a path of segments.
///
/// # Arguments
/// * `db` - The database
/// * `base` - Optional base qualified name (None for root)
/// * `path` - Slice of name segments to append
///
/// # Returns
/// A qualified name representing `base/path[0]/path[1]/...`
fn extend_path<'db, Db>(
    db: &'db Db,
    mut base: Option<QualifiedName<'db>>,
    path: &[Name<'db>],
) -> QualifiedName<'db>
where
    Db: salsa::Database + ?Sized,
{
    for &name in path {
        base = Some(QualifiedName::new(db, base, name));
    }
    base.expect("extend_path called with empty path")
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Resolver<'db> {
    namespace: Option<QualifiedName<'db>>,
    open_directives: Vec<OpenDirective<'db>>,
}

impl<'db> Resolver<'db> {
    pub fn new() -> Self {
        Self {
            namespace: None,
            open_directives: Vec::new(),
        }
    }

    pub fn namespace(&self) -> Option<QualifiedName<'db>> {
        self.namespace
    }

    pub fn extend<Db>(&self, db: &'db Db, path: &[Name<'db>]) -> Self
    where
        Db: salsa::Database + ?Sized,
    {
        let namespace = QualifiedName::from_path(self.namespace, path);
        Self {
            namespace: Some(namespace),
            open_directives: self.open_directives.clone(),
        }
    }

    pub fn add_open_directive(mut self, directive: OpenDirective<'db>) -> Self {
        self.open_directives.push(directive);
        self
    }

    pub fn qualify<Db>(&self, db: &'db Db, name: Name<'db>) -> QualifiedName<'db>
    where
        Db: salsa::Database + ?Sized,
    {
        QualifiedName::new(db, self.namespace, name)
    }

    pub fn resolve<Db>(
        &self,
        db: &'db Db,
        name: Name<'db>,
        global_env: &GlobalEnv<'db>,
    ) -> Option<QualifiedName<'db>>
    where
        Db: salsa::Database + ?Sized,
    {
        // Step 1: Check current namespace and walk up the hierarchy
        let mut namespace = self.namespace;
        while let Some(ns) = namespace {
            let qualified = QualifiedName::new(db, Some(ns), name);
            if global_env.contains(qualified) {
                return Some(qualified);
            }
            namespace = ns.package(db);
        }

        // Step 2: Check root namespace
        let qualified = QualifiedName::new(db, None, name);
        if global_env.contains(qualified) {
            Some(qualified)
        } else {
            None
        }
    }
}

pub fn resolve_path<'db, Db>(
    db: &'db Db,
    path: &[Name<'db>],
    dubbing_table: &DubbingTable<'db>,
    resolver: &Resolver<'db>,
    stub_table: &StubTable<'db>,
) -> Result<QualifiedName<'db>, ResolutionError<'db>>
where
    Db: salsa::Database + ?Sized,
{
    // Internal API contract: path must be non-empty
    debug_assert!(!path.is_empty(), "resolve_path requires non-empty path");

    let base_name = path[0];
    let tail = &path[1..];

    // STEP 1: Aliases (Prefix Rewriting)
    // If `base_name` matches an alias like "M" from "open Math as M",
    // rewrite to the full namespace path and do a direct lookup.
    for directive in &resolver.open_directives {
        if directive.as_alias == Some(base_name) {
            // Rewrite: M.add → Math/add
            let fully_qualified = extend_path(db, Some(directive.namespace), tail);
            if stub_table.contains(fully_qualified) {
                return Ok(ResolvedName::Global(fully_qualified));
            }
        }
    }

    // STEP 2: Local Variables and Values
    // Locals and values shadow everything. If `base_name` is local or a value, return it with the tail.
    // The elaborator will use the tail for type-directed field projections.
    if let Some(dubbed) = dubbing_table.resolve(base_name) {
        match dubbed {
            crate::dubbing::Dubbed::Local(level) => {
                return Ok(ResolvedName::Local(level, tail.to_vec()));
            }
            crate::dubbing::Dubbed::Value(typed_value) => {
                return Ok(ResolvedName::Value(typed_value, tail.to_vec()));
            }
        }
    }

    // STEP 3: Current Namespace Match
    // Append the ENTIRE path to the current namespace and walk up the hierarchy.
    let mut namespace = resolver.current_namespace;
    while let Some(ns) = namespace {
        let qualified = extend_path(db, Some(ns), path);
        if stub_table.contains(qualified) {
            return Ok(ResolvedName::Global(qualified));
        }
        namespace = ns.package(db);
    }

    // STEP 4: Opened Namespaces
    // Modifiers ONLY apply to `base_name`.
    // If `base_name` passes the filter, append the `tail` and check the global table.
    let mut matches = Vec::new();

    for directive in &resolver.opened_directives {
        // Skip aliased opens (handled in Step 1)
        if directive.as_alias.is_some() {
            continue;
        }

        // Apply modifiers to the base name only
        if let Some(lookup_base) = directive.apply_modifiers(base_name) {
            // Build the full path: directive.namespace/lookup_base/tail...
            let base_qn = QualifiedName::new(db, Some(directive.namespace), lookup_base);
            let qualified = if tail.is_empty() {
                base_qn
            } else {
                extend_path(db, Some(base_qn), tail)
            };

            if stub_table.contains(qualified) {
                matches.push(qualified);
            }
        }
    }

    // Deduplicate matches before checking for ambiguity
    // Multiple directives might resolve to the same definition
    matches.sort();
    matches.dedup();

    // Check for ambiguity
    match matches.len() {
        0 => {
            // No matches in opened namespaces, continue to step 5
        }
        1 => {
            // Exactly one match, return it
            return Ok(ResolvedName::Global(matches[0]));
        }
        _ => {
            // Multiple matches - ambiguous!
            return Err(ResolutionError::AmbiguousIdentifier(path.to_vec(), matches));
        }
    }

    // STEP 5: Absolute Root Match
    // Append the ENTIRE path to the root and check the global table.
    let root_fqn = extend_path(db, None, path);
    if stub_table.contains(root_fqn) {
        return Ok(ResolvedName::Global(root_fqn));
    }

    // STEP 6: Failure
    // The path was not found in any scope
    Err(ResolutionError::UnknownIdentifier(path.to_vec()))
}

/// Convenience wrapper for resolving a single name (backwards compatibility).
pub fn resolve_name<'db, Db>(
    db: &'db Db,
    name: Name<'db>,
    dubbing_table: &DubbingTable<'db>,
    resolver: &Resolver<'db>,
    stub_table: &StubTable<'db>,
) -> Result<QualifiedName<'db>, ResolutionError<'db>>
where
    Db: salsa::Database + ?Sized,
{
    resolve_path(db, &[name], dubbing_table, resolver, stub_table)
}

#[cfg(test)]
mod resolution_tests {
    use super::*;
    use crate::dubbing::{Dubbed, Dubbing};
    use hwml_support::FromWithDb;
    use hwml_surface as surface;

    #[test]
    fn test_local_shadows_global() {
        let db = hwml_core::Database::new();
        let mut stub_table = StubTable::new();
        let mut dubbing_table = DubbingTable::new();
        let resolver = Resolver::new();

        let foo_name = Name::from_with_db(&db, "foo");

        // Add a global definition "foo" using the parser
        let input = b"def foo := 42";
        let program = hwml_surface::parsing::parse(input).expect("parse failed");
        if let surface::Statement::Def(def) = &program.statements[0] {
            let statement = surface::Statement::Def(def.clone());
            let root_foo = QualifiedName::new(&db, None, foo_name);
            stub_table
                .insert(root_foo, statement, Location::UNKNOWN)
                .unwrap();
        }

        // Add a local variable "foo" at level 0
        dubbing_table.extend(Dubbing {
            name: foo_name,
            subject: Dubbed::Local(Level(0)),
        });

        // Resolution should find the local, not the global
        let result = resolve_name(&db, foo_name, &dubbing_table, &resolver, &stub_table);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), ResolvedName::Local(Level(0), vec![]));
    }

    #[test]
    fn test_current_namespace_resolution() {
        let db = hwml_core::Database::new();
        let mut stub_table = StubTable::new();
        let dubbing_table = DubbingTable::new();

        let math_name = Name::from_with_db(&db, "Math");
        let add_name = Name::from_with_db(&db, "add");

        // Create a resolver in the Math namespace
        let resolver = Resolver::new().push_namespace(&db, math_name);

        // Add a global definition "Math/add" using the parser
        let input = b"def add := 1";
        let program = hwml_surface::parsing::parse(input).expect("parse failed");
        if let surface::Statement::Def(def) = &program.statements[0] {
            let statement = surface::Statement::Def(def.clone());
            let math_add = QualifiedName::new(
                &db,
                Some(QualifiedName::new(&db, None, math_name)),
                add_name,
            );
            stub_table
                .insert(math_add, statement, Location::UNKNOWN)
                .unwrap();

            // Resolution should find Math/add when we're in the Math namespace
            let result = resolve_name(&db, add_name, &dubbing_table, &resolver, &stub_table);
            assert!(result.is_ok());
            assert_eq!(result.unwrap(), ResolvedName::Global(math_add));
        }
    }

    #[test]
    fn test_root_namespace_fallback() {
        let db = hwml_core::Database::new();
        let mut stub_table = StubTable::new();
        let dubbing_table = DubbingTable::new();

        let math_name = Name::from_with_db(&db, "Math");
        let foo_name = Name::from_with_db(&db, "foo");

        // Create a resolver in the Math namespace
        let resolver = Resolver::new().push_namespace(&db, math_name);

        // Add a global definition "foo" at the root (not in Math) using the parser
        let input = b"def foo := 1";
        let program = hwml_surface::parsing::parse(input).expect("parse failed");
        if let surface::Statement::Def(def) = &program.statements[0] {
            let statement = surface::Statement::Def(def.clone());
            let root_foo = QualifiedName::new(&db, None, foo_name);
            stub_table
                .insert(root_foo, statement, Location::UNKNOWN)
                .unwrap();

            // Resolution should fall back to root namespace and find "foo"
            let result = resolve_name(&db, foo_name, &dubbing_table, &resolver, &stub_table);
            assert!(result.is_ok());
            assert_eq!(result.unwrap(), ResolvedName::Global(root_foo));
        }
    }

    #[test]
    fn test_unknown_identifier_error() {
        let db = hwml_core::Database::new();
        let stub_table = StubTable::new();
        let dubbing_table = DubbingTable::new();
        let resolver = Resolver::new();

        let unknown_name = Name::from_with_db(&db, "unknown");

        // Resolution should fail with UnknownIdentifier
        let result = resolve_name(&db, unknown_name, &dubbing_table, &resolver, &stub_table);
        assert!(result.is_err());
        match result.unwrap_err() {
            ResolutionError::UnknownIdentifier(path) => {
                assert_eq!(path, vec![unknown_name]);
            }
            ResolutionError::AmbiguousIdentifier(_, _) => {
                panic!("Expected UnknownIdentifier, got AmbiguousIdentifier");
            }
        }
    }

    #[test]
    fn test_current_namespace_takes_priority_over_root() {
        let db = hwml_core::Database::new();
        let mut stub_table = StubTable::new();
        let dubbing_table = DubbingTable::new();

        let math_name = Name::from_with_db(&db, "Math");
        let foo_name = Name::from_with_db(&db, "foo");

        // Create a resolver in the Math namespace
        let resolver = Resolver::new().push_namespace(&db, math_name);

        // Add "foo" at the root using the parser
        let input1 = b"def foo := 1";
        let program1 = hwml_surface::parsing::parse(input1).expect("parse failed");
        if let surface::Statement::Def(def1) = &program1.statements[0] {
            let statement1 = surface::Statement::Def(def1.clone());
            let root_foo = QualifiedName::new(&db, None, foo_name);
            stub_table
                .insert(root_foo, statement1, Location::UNKNOWN)
                .unwrap();
        }

        // Add "Math/foo" using the parser
        let input2 = b"def foo := 2";
        let program2 = hwml_surface::parsing::parse(input2).expect("parse failed");
        if let surface::Statement::Def(def2) = &program2.statements[0] {
            let statement2 = surface::Statement::Def(def2.clone());
            let math_foo = QualifiedName::new(
                &db,
                Some(QualifiedName::new(&db, None, math_name)),
                foo_name,
            );
            stub_table
                .insert(math_foo, statement2, Location::UNKNOWN)
                .unwrap();

            // Resolution should find Math/foo (current namespace), not root foo
            let result = resolve_name(&db, foo_name, &dubbing_table, &resolver, &stub_table);
            assert!(result.is_ok());
            assert_eq!(result.unwrap(), ResolvedName::Global(math_foo));
        }
    }

    #[test]
    fn test_open_directive_basic() {
        let db = hwml_core::Database::new();
        let mut stub_table = StubTable::new();
        let dubbing_table = DubbingTable::new();

        let math_name = Name::from_with_db(&db, "Math");
        let add_name = Name::from_with_db(&db, "add");

        // Create Math namespace
        let math_ns = QualifiedName::new(&db, None, math_name);

        // Add Math/add
        let input = b"def add := 1";
        let program = hwml_surface::parsing::parse(input).expect("parse failed");
        if let surface::Statement::Def(def) = &program.statements[0] {
            let statement = surface::Statement::Def(def.clone());
            let math_add = QualifiedName::new(&db, Some(math_ns), add_name);
            stub_table
                .insert(math_add, statement, Location::UNKNOWN)
                .unwrap();
        }

        // Create a resolver with an open directive for Math
        let directive = OpenDirective::new(math_ns);
        let resolver = Resolver::new().add_open_directive(directive);

        // Resolution should find Math/add via the open directive
        let result = resolve_name(&db, add_name, &dubbing_table, &resolver, &stub_table);
        assert!(result.is_ok());
        let math_add = QualifiedName::new(&db, Some(math_ns), add_name);
        assert_eq!(result.unwrap(), ResolvedName::Global(math_add));
    }

    #[test]
    fn test_open_directive_with_only_modifier() {
        let db = hwml_core::Database::new();
        let mut stub_table = StubTable::new();
        let dubbing_table = DubbingTable::new();

        let math_name = Name::from_with_db(&db, "Math");
        let add_name = Name::from_with_db(&db, "add");
        let sub_name = Name::from_with_db(&db, "sub");

        // Create Math namespace
        let math_ns = QualifiedName::new(&db, None, math_name);

        // Add Math/add and Math/sub
        let input1 = b"def add := 1";
        let program1 = hwml_surface::parsing::parse(input1).expect("parse failed");
        if let surface::Statement::Def(def) = &program1.statements[0] {
            let statement = surface::Statement::Def(def.clone());
            let math_add = QualifiedName::new(&db, Some(math_ns), add_name);
            stub_table
                .insert(math_add, statement, Location::UNKNOWN)
                .unwrap();
        }

        let input2 = b"def sub := 2";
        let program2 = hwml_surface::parsing::parse(input2).expect("parse failed");
        if let surface::Statement::Def(def) = &program2.statements[0] {
            let statement = surface::Statement::Def(def.clone());
            let math_sub = QualifiedName::new(&db, Some(math_ns), sub_name);
            stub_table
                .insert(math_sub, statement, Location::UNKNOWN)
                .unwrap();
        }

        // Create a resolver with "open Math (add)" - only import add
        let directive = OpenDirective::with_modifiers(
            math_ns,
            vec![OpenModifier::Only(vec![vec![add_name]], Location::UNKNOWN)],
        );
        let resolver = Resolver::new().add_open_directive(directive);

        // Resolution should find Math/add
        let result = resolve_name(&db, add_name, &dubbing_table, &resolver, &stub_table);
        assert!(result.is_ok());

        // Resolution should NOT find Math/sub (filtered by Only)
        let result = resolve_name(&db, sub_name, &dubbing_table, &resolver, &stub_table);
        assert!(result.is_err());
        match result.unwrap_err() {
            ResolutionError::UnknownIdentifier(_) => {}
            _ => panic!("Expected UnknownIdentifier"),
        }
    }

    #[test]
    fn test_open_directive_ambiguity() {
        let db = hwml_core::Database::new();
        let mut stub_table = StubTable::new();
        let dubbing_table = DubbingTable::new();

        let math_name = Name::from_with_db(&db, "Math");
        let physics_name = Name::from_with_db(&db, "Physics");
        let add_name = Name::from_with_db(&db, "add");

        // Create Math and Physics namespaces
        let math_ns = QualifiedName::new(&db, None, math_name);
        let physics_ns = QualifiedName::new(&db, None, physics_name);

        // Add Math/add
        let input1 = b"def add := 1";
        let program1 = hwml_surface::parsing::parse(input1).expect("parse failed");
        if let surface::Statement::Def(def) = &program1.statements[0] {
            let statement = surface::Statement::Def(def.clone());
            let math_add = QualifiedName::new(&db, Some(math_ns), add_name);
            stub_table
                .insert(math_add, statement, Location::UNKNOWN)
                .unwrap();
        }

        // Add Physics/add
        let input2 = b"def add := 2";
        let program2 = hwml_surface::parsing::parse(input2).expect("parse failed");
        if let surface::Statement::Def(def) = &program2.statements[0] {
            let statement = surface::Statement::Def(def.clone());
            let physics_add = QualifiedName::new(&db, Some(physics_ns), add_name);
            stub_table
                .insert(physics_add, statement, Location::UNKNOWN)
                .unwrap();
        }

        // Create a resolver with both Math and Physics opened
        let directive1 = OpenDirective::new(math_ns);
        let directive2 = OpenDirective::new(physics_ns);
        let resolver = Resolver::new()
            .add_open_directive(directive1)
            .add_open_directive(directive2);

        // Resolution should fail with AmbiguousIdentifier
        let result = resolve_name(&db, add_name, &dubbing_table, &resolver, &stub_table);
        assert!(result.is_err());
        match result.unwrap_err() {
            ResolutionError::AmbiguousIdentifier(path, candidates) => {
                assert_eq!(path, vec![add_name]);
                assert_eq!(candidates.len(), 2);
            }
            _ => panic!("Expected AmbiguousIdentifier"),
        }
    }

    #[test]
    fn test_open_directive_qualified_only() {
        let db = hwml_core::Database::new();
        let mut stub_table = StubTable::new();
        let dubbing_table = DubbingTable::new();

        // Create Math/Algebra/add and Math/Geometry/point
        let math_name = Name::from_with_db(&db, "Math");
        let algebra_name = Name::from_with_db(&db, "Algebra");
        let geometry_name = Name::from_with_db(&db, "Geometry");
        let add_name = Name::from_with_db(&db, "add");
        let point_name = Name::from_with_db(&db, "point");

        let math_ns = QualifiedName::new(&db, None, math_name);
        let algebra_ns = QualifiedName::new(&db, Some(math_ns), algebra_name);
        let geometry_ns = QualifiedName::new(&db, Some(math_ns), geometry_name);

        // Register the namespaces themselves as empty namespace statements
        let ns_input = b"namespace Algebra {}";
        let ns_program = hwml_surface::parsing::parse(ns_input).expect("parse failed");
        if let surface::Statement::Namespace(ns) = &ns_program.statements[0] {
            let statement = surface::Statement::Namespace(ns.clone());
            stub_table
                .insert(algebra_ns, statement, Location::UNKNOWN)
                .unwrap();
        }

        let ns_input2 = b"namespace Geometry {}";
        let ns_program2 = hwml_surface::parsing::parse(ns_input2).expect("parse failed");
        if let surface::Statement::Namespace(ns) = &ns_program2.statements[0] {
            let statement = surface::Statement::Namespace(ns.clone());
            stub_table
                .insert(geometry_ns, statement, Location::UNKNOWN)
                .unwrap();
        }

        // Add Math/Algebra/add
        let input1 = b"def add := 1";
        let program1 = hwml_surface::parsing::parse(input1).expect("parse failed");
        if let surface::Statement::Def(def) = &program1.statements[0] {
            let statement = surface::Statement::Def(def.clone());
            let algebra_add = QualifiedName::new(&db, Some(algebra_ns), add_name);
            stub_table
                .insert(algebra_add, statement, Location::UNKNOWN)
                .unwrap();
        }

        // Add Math/Geometry/point
        let input2 = b"def point := 2";
        let program2 = hwml_surface::parsing::parse(input2).expect("parse failed");
        if let surface::Statement::Def(def) = &program2.statements[0] {
            let statement = surface::Statement::Def(def.clone());
            let geometry_point = QualifiedName::new(&db, Some(geometry_ns), point_name);
            stub_table
                .insert(geometry_point, statement, Location::UNKNOWN)
                .unwrap();
        }

        // Create "open Math (Algebra.add)" - only import Algebra.add
        // Note: Currently only matches first segment, so this imports anything starting with "Algebra"
        let directive = OpenDirective::with_modifiers(
            math_ns,
            vec![OpenModifier::Only(
                vec![vec![algebra_name, add_name]],
                Location::UNKNOWN,
            )],
        );
        let resolver = Resolver::new().add_open_directive(directive);

        // Resolution should find "Algebra" when looking up "Algebra" (first segment matches)
        // This resolves to Math/Algebra (the namespace)
        let result = resolve_name(&db, algebra_name, &dubbing_table, &resolver, &stub_table);
        assert!(result.is_ok());
        if let Ok(ResolvedName::Global(qn)) = result {
            assert_eq!(qn, algebra_ns);
        }

        // Resolution should NOT find Geometry (not in Only list)
        let result = resolve_name(&db, geometry_name, &dubbing_table, &resolver, &stub_table);
        assert!(result.is_err());
    }

    #[test]
    fn test_open_directive_qualified_hiding() {
        let db = hwml_core::Database::new();
        let mut stub_table = StubTable::new();
        let dubbing_table = DubbingTable::new();

        // Create Math/Internal/Debug and Math/Public/API
        let math_name = Name::from_with_db(&db, "Math");
        let internal_name = Name::from_with_db(&db, "Internal");
        let public_name = Name::from_with_db(&db, "Public");
        let debug_name = Name::from_with_db(&db, "Debug");
        let api_name = Name::from_with_db(&db, "API");

        let math_ns = QualifiedName::new(&db, None, math_name);
        let internal_ns = QualifiedName::new(&db, Some(math_ns), internal_name);
        let public_ns = QualifiedName::new(&db, Some(math_ns), public_name);

        // Register the namespaces themselves
        let ns_input = b"namespace Internal {}";
        let ns_program = hwml_surface::parsing::parse(ns_input).expect("parse failed");
        if let surface::Statement::Namespace(ns) = &ns_program.statements[0] {
            let statement = surface::Statement::Namespace(ns.clone());
            stub_table
                .insert(internal_ns, statement, Location::UNKNOWN)
                .unwrap();
        }

        let ns_input2 = b"namespace Public {}";
        let ns_program2 = hwml_surface::parsing::parse(ns_input2).expect("parse failed");
        if let surface::Statement::Namespace(ns) = &ns_program2.statements[0] {
            let statement = surface::Statement::Namespace(ns.clone());
            stub_table
                .insert(public_ns, statement, Location::UNKNOWN)
                .unwrap();
        }

        // Add Math/Internal/Debug
        let input1 = b"def Debug := 1";
        let program1 = hwml_surface::parsing::parse(input1).expect("parse failed");
        if let surface::Statement::Def(def) = &program1.statements[0] {
            let statement = surface::Statement::Def(def.clone());
            let internal_debug = QualifiedName::new(&db, Some(internal_ns), debug_name);
            stub_table
                .insert(internal_debug, statement, Location::UNKNOWN)
                .unwrap();
        }

        // Add Math/Public/API
        let input2 = b"def API := 2";
        let program2 = hwml_surface::parsing::parse(input2).expect("parse failed");
        if let surface::Statement::Def(def) = &program2.statements[0] {
            let statement = surface::Statement::Def(def.clone());
            let public_api = QualifiedName::new(&db, Some(public_ns), api_name);
            stub_table
                .insert(public_api, statement, Location::UNKNOWN)
                .unwrap();
        }

        // Create "open Math hiding (Internal.Debug)" - hide Internal.*
        let directive = OpenDirective::with_modifiers(
            math_ns,
            vec![OpenModifier::Hiding(
                vec![vec![internal_name, debug_name]],
                Location::UNKNOWN,
            )],
        );
        let resolver = Resolver::new().add_open_directive(directive);

        // Resolution should find Public (not hidden)
        let result = resolve_name(&db, public_name, &dubbing_table, &resolver, &stub_table);
        assert!(result.is_ok());

        // Resolution should NOT find Internal (hidden)
        let result = resolve_name(&db, internal_name, &dubbing_table, &resolver, &stub_table);
        assert!(result.is_err());
    }

    #[test]
    fn test_open_directive_qualified_renaming() {
        let db = hwml_core::Database::new();
        let mut stub_table = StubTable::new();
        let dubbing_table = DubbingTable::new();

        // Create Std/Nat/Add
        let std_name = Name::from_with_db(&db, "Std");
        let nat_name = Name::from_with_db(&db, "Nat");
        let add_name = Name::from_with_db(&db, "Add");
        let n_name = Name::from_with_db(&db, "N");
        let plus_name = Name::from_with_db(&db, "+");

        let std_ns = QualifiedName::new(&db, None, std_name);
        let nat_ns = QualifiedName::new(&db, Some(std_ns), nat_name);

        // Register the Nat namespace
        let ns_input = b"namespace Nat {}";
        let ns_program = hwml_surface::parsing::parse(ns_input).expect("parse failed");
        if let surface::Statement::Namespace(ns) = &ns_program.statements[0] {
            let statement = surface::Statement::Namespace(ns.clone());
            stub_table
                .insert(nat_ns, statement, Location::UNKNOWN)
                .unwrap();
        }

        // Add Std/Nat/Add
        let input = b"def Add := 1";
        let program = hwml_surface::parsing::parse(input).expect("parse failed");
        if let surface::Statement::Def(def) = &program.statements[0] {
            let statement = surface::Statement::Def(def.clone());
            let nat_add = QualifiedName::new(&db, Some(nat_ns), add_name);
            stub_table
                .insert(nat_add, statement, Location::UNKNOWN)
                .unwrap();
        }

        // Create "open Std renaming (Nat.Add to N.+)"
        // Currently only matches first segment: Nat -> N
        let directive = OpenDirective::with_modifiers(
            std_ns,
            vec![OpenModifier::Renaming(
                vec![nat_name, add_name],
                vec![n_name, plus_name],
                Location::UNKNOWN,
            )],
        );
        let resolver = Resolver::new().add_open_directive(directive);

        // Resolution should find Nat when we look up N (renaming applied)
        // The apply_modifiers method rewrites N -> Nat (first segment only)
        let result = resolve_name(&db, n_name, &dubbing_table, &resolver, &stub_table);
        assert!(result.is_ok());
        if let Ok(ResolvedName::Global(qn)) = result {
            // Should resolve to Std/Nat (the namespace)
            assert_eq!(qn, nat_ns);
        }
    }
}
