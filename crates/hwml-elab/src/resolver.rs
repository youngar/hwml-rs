use crate::stub_table::StubTable;
use hwml_core::{Name, QualifiedName};
use std::collections::HashSet;

#[derive(Debug)]
pub enum OpenError {
    DuplicateOpen,
}

type OpenResult<T> = Result<T, OpenError>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OpenDirective<'db> {
    pub namespace: QualifiedName<'db>,
    pub alias: Box<[Name<'db>]>,
}

impl<'db> OpenDirective<'db> {
    /// Create a new open directive with an alias.
    pub fn alias(namespace: QualifiedName<'db>, alias: Box<[Name<'db>]>) -> Self {
        Self { namespace, alias }
    }

    /// Rewrite a path against this open directive.
    ///
    /// If there's an alias, checks if the alias prefix matches the beginning of the path,
    /// and if so, returns the path qualified against the real namespace.
    ///
    /// If there's no alias, qualifies the entire path against the namespace.
    pub fn try_rewrite<Db>(&self, db: &'db Db, path: &[Name<'db>]) -> Option<QualifiedName<'db>>
    where
        Db: salsa::Database + ?Sized,
    {
        assert!(
            !path.is_empty(),
            "OpenDirective::try_rewrite called with empty path"
        );

        // Check if all alias segments match the beginning of the path.
        if !path[..path.len() - 1].starts_with(&*self.alias) {
            return None;
        }

        // The alias matches, qualify the remaining path parts against the real namespace.
        let remaining_path = &path[self.alias.len()..];
        QualifiedName::qualify_path(db, Some(self.namespace), remaining_path)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LexicalScope<'db> {
    // A set of all namespaces opened in this scope. Used to detect duplicate opens.
    pub opened: HashSet<QualifiedName<'db>>,
    /// A list of all open directives in this scope.
    pub directives: Vec<OpenDirective<'db>>,
}

impl<'db> LexicalScope<'db> {
    pub fn new() -> Self {
        Self {
            opened: HashSet::new(),
            directives: Vec::new(),
        }
    }

    /// Attempts to add a new open to this scope. Returns an error if the
    /// namespace was already opened in this block.
    pub fn add_open(&mut self, namespace: QualifiedName<'db>) -> OpenResult<()> {
        self.add_alias(namespace, Box::new([]))
    }

    /// Attempts to add a new aliased open to this scope. Returns an error if the
    /// namespace was already opened in this block.
    pub fn add_alias(
        &mut self,
        namespace: QualifiedName<'db>,
        alias: Box<[Name<'db>]>,
    ) -> OpenResult<()> {
        if !self.opened.insert(namespace) {
            return Err(OpenError::DuplicateOpen);
        }
        self.directives.push(OpenDirective::alias(namespace, alias));
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Scope<'db> {
    /// A lexical scope that allows Open statements, but does not introduce a new namespace.
    Lexical(LexicalScope<'db>),
    /// A namespace scope that introduces a new namespace and implicitly opens it.
    Namespace(QualifiedName<'db>, LexicalScope<'db>),
}

impl<'db> Scope<'db> {
    fn lexical() -> Self {
        Scope::Lexical(LexicalScope::new())
    }

    fn namespace(namespace: QualifiedName<'db>) -> Self {
        Scope::Namespace(namespace, LexicalScope::new())
    }

    fn lexical_scope(&self) -> &LexicalScope<'db> {
        match self {
            Scope::Lexical(scope) => scope,
            Scope::Namespace(_, scope) => scope,
        }
    }

    fn lexical_scope_mut(&mut self) -> &mut LexicalScope<'db> {
        match self {
            Scope::Lexical(scope) => scope,
            Scope::Namespace(_, scope) => scope,
        }
    }

    fn add_open(&mut self, namespace: QualifiedName<'db>) -> OpenResult<()> {
        self.add_alias(namespace, Box::new([]))
    }

    fn add_alias(
        &mut self,
        namespace: QualifiedName<'db>,
        alias: Box<[Name<'db>]>,
    ) -> OpenResult<()> {
        self.lexical_scope_mut().add_alias(namespace, alias)
    }
}

#[derive(Debug, Clone)]
pub enum ResolutionError<'db> {
    UnknownIdentifier(Vec<Name<'db>>),
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Resolver<'db> {
    /// The current namespace.
    namespace: Option<QualifiedName<'db>>,
    /// The stack of scopes from outermost to innermost.
    scopes: Vec<Scope<'db>>,
}

impl<'db> Resolver<'db> {
    /// Create a new Resolver starting at the root namespace.
    pub fn new() -> Self {
        let namespace = None;
        let scopes = vec![Scope::Lexical(LexicalScope::new())];
        Self { namespace, scopes }
    }

    /// Gets the current namespace.
    pub fn namespace(&self) -> Option<QualifiedName<'db>> {
        self.namespace
    }

    /// Qualifies a single name against the current namespace.
    pub fn qualify<Db>(&self, db: &'db Db, name: Name<'db>) -> QualifiedName<'db>
    where
        Db: salsa::Database + ?Sized,
    {
        QualifiedName::new(db, self.namespace, name)
    }

    /// Qualifies a path against the current namespace.
    pub fn qualify_path<Db>(&self, db: &'db Db, path: &[Name<'db>]) -> QualifiedName<'db>
    where
        Db: salsa::Database + ?Sized,
    {
        QualifiedName::qualify_path(db, self.namespace, path)
            .expect("qualify_path should always succeed with non-empty path")
    }

    /// Enter a new lexical scope without entering a new namespace.
    pub fn push_scope(&self) -> Self {
        let namespace = self.namespace;
        let mut scopes = self.scopes.clone();
        scopes.push(Scope::Lexical(LexicalScope::new()));
        Self { namespace, scopes }
    }

    /// Enter a new namespace, which is implicitly a new lexical scope.
    pub fn push_namespace<Db>(&self, db: &'db Db, path: &[Name<'db>]) -> Self
    where
        Db: salsa::Database + ?Sized,
    {
        let mut namespace = self.namespace;
        let mut scopes = self.scopes.clone();
        for name in path {
            namespace = Some(QualifiedName::new(db, namespace, *name));
            scopes.push(Scope::namespace(namespace.unwrap()));
        }
        Self { namespace, scopes }
    }

    /// Open a namespace in the current scope.
    /// Returns the updated resolver on success, or the original resolver on error.
    pub fn open_namespace(
        mut self,
        namespace: QualifiedName<'db>,
    ) -> Result<Self, (OpenError, Self)> {
        match self
            .scopes
            .last_mut()
            .expect("push_scope should have been called in constructor")
            .add_open(namespace)
        {
            Ok(()) => Ok(self),
            Err(e) => Err((e, self)),
        }
    }

    /// Alias a namepace in the current scope.
    /// Returns the updated resolver on success, or the original resolver on error.
    pub fn alias_namespace(
        mut self,
        namespace: QualifiedName<'db>,
        alias: Box<[Name<'db>]>,
    ) -> Result<Self, (OpenError, Self)> {
        match self
            .scopes
            .last_mut()
            .expect("push_scope should have been called in constructor")
            .add_alias(namespace, alias)
        {
            Ok(()) => Ok(self),
            Err(e) => Err((e, self)),
        }
    }
}

/// Resolves a path to a list of fully qualified names using the provided resolver and stub table.
///
/// Returns a vector of all matching qualified names found in the resolver's scopes.
/// The caller should have already checked locals before calling this function.
///
/// # Algorithm
/// 1. Iterate through scopes from innermost to outermost
/// 2. For each scope:
///    a. Try qualifying the path against the current namespace if we are a namespace scope.
///    b. For each OpenDirective in the scope, try qualifying the path against it (alias must match the beginning of the path).
///    c. Check if each qualified name exists in stub_table, resolving it.
///    d. Collect all existing qualified names.
/// 3. If at least 1 name was found in a scope, deduplicate and return
/// 4. If no names found in current scope, continue to next outer scope
/// 5. If no scopes yield results, return empty vector
pub fn resolve_path<'db, Db>(
    db: &'db Db,
    stub_table: &StubTable<'db>,
    resolver: &Resolver<'db>,
    path: &[Name<'db>],
) -> Vec<QualifiedName<'db>>
where
    Db: salsa::Database,
{
    assert!(!path.is_empty(), "resolve_path requires non-empty path");

    // Debug: Show what we're resolving (disabled for less noise)
    let path_str = path
        .iter()
        .map(|n| n.to_string(db))
        .collect::<Vec<_>>()
        .join(".");
    eprintln!("[RESOLVE] Looking up path: {}", path_str);

    // Walk from innermost to outermost, tracking the namespace at each level
    for scope in resolver.scopes.iter().rev() {
        let mut candidates = vec![];
        if let Scope::Namespace(ns, scope) = scope {
            // CRITICAL: Walk up the namespace hierarchy
            // For namespace Foo/Bar, try: Foo/Bar/path, Foo/path, path
            let mut current_ns = Some(*ns);
            loop {
                if let Some(qualified) = QualifiedName::qualify_path(db, current_ns, path) {
                    eprintln!(
                        "[RESOLVE] Trying namespace qualification: {}",
                        qualified.to_string(db)
                    );
                    if stub_table.contains(qualified) {
                        candidates.push(qualified);
                    }
                }

                // Walk up to parent namespace
                if let Some(ns_val) = current_ns {
                    current_ns = ns_val.namespace(db);
                } else {
                    break;
                }
            }

            for open in scope.directives.iter() {
                if let Some(qualified) = open.try_rewrite(db, path) {
                    eprintln!(
                        "[RESOLVE] Trying alias qualification: {}",
                        qualified.to_string(db)
                    );
                    if stub_table.contains(qualified) {
                        candidates.push(qualified);
                    }
                }
            }
        } else if let Scope::Lexical(scope) = scope {
            for open in scope.directives.iter() {
                if let Some(qualified) = open.try_rewrite(db, path) {
                    eprintln!(
                        "[RESOLVE] Trying alias qualification: {}",
                        qualified.to_string(db)
                    );
                    if stub_table.contains(qualified) {
                        candidates.push(qualified);
                    }
                }
            }
        }

        // If we found at least one candidate at this level, deduplicate and return
        if !candidates.is_empty() {
            // Deduplicate using a HashSet
            let unique_candidates: HashSet<QualifiedName<'db>> = candidates.into_iter().collect();
            return unique_candidates.into_iter().collect();
        }
    }

    // No scopes yielded any results
    Vec::new()
}
