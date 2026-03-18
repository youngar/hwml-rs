use crate::stub_table::StubTable;
use hwml_core::*;
use std::collections::HashSet;

#[derive(Debug)]
pub enum OpenError {
    DuplicateOpen,
}

type OpenResult<T> = Result<T, OpenError>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OpenDirective<'db> {
    pub namespace: QualifiedName<'db>,
    pub alias: Option<QualifiedName<'db>>,
}

impl<'db> OpenDirective<'db> {
    /// Create a new open directive without an alias.
    pub fn open(namespace: QualifiedName<'db>) -> Self {
        Self {
            namespace,
            alias: None,
        }
    }

    /// Create a new open directive with an alias.
    pub fn alias(namespace: QualifiedName<'db>, alias: QualifiedName<'db>) -> Self {
        Self {
            namespace,
            alias: Some(alias),
        }
    }

    /// Resolve a path against this open directive.
    ///
    /// If there's an alias, checks if the alias prefix matches the beginning of the path,
    /// and if so, returns the path qualified against the real namespace.
    ///
    /// If there's no alias, qualifies the entire path against the namespace.
    pub fn resolve<Db>(&self, db: &'db Db, path: &[Name<'db>]) -> Option<QualifiedName<'db>>
    where
        Db: salsa::Database + ?Sized,
    {
        assert!(
            !path.is_empty(),
            "OpenDirective::resolve called with empty path"
        );

        if let Some(alias) = self.alias {
            // Check if the alias prefix matches the beginning of the path.
            let alias_segments = alias.segments(db);

            // If the path is shorter than the alias, it can't match.
            if path.len() < alias_segments.len() {
                return None;
            }

            // Check if all alias segments match the beginning of the path.
            for (i, alias_segment) in alias_segments.iter().enumerate() {
                if path[i] != *alias_segment {
                    return None;
                }
            }

            // The alias matches, qualify the remaining path parts against the real namespace.
            let remaining_path = &path[alias_segments.len()..];
            QualifiedName::qualify_path(db, Some(self.namespace), remaining_path)
        } else {
            // No alias: qualify the entire path against the namespace.
            QualifiedName::qualify_path(db, Some(self.namespace), path)
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LexicalScope<'db> {
    // A set of all namespaces opened in this scope. Used to detect duplicate opens.
    pub opened: HashSet<QualifiedName<'db>>,
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
        if !self.opened.insert(namespace) {
            return Err(OpenError::DuplicateOpen);
        }
        self.directives.push(OpenDirective::open(namespace));
        Ok(())
    }

    /// Attempts to add a new aliased open to this scope. Returns an error if the
    /// namespace was already opened in this block.
    pub fn add_alias(
        &mut self,
        alias: QualifiedName<'db>,
        namespace: QualifiedName<'db>,
    ) -> OpenResult<()> {
        if !self.opened.insert(namespace) {
            return Err(OpenError::DuplicateOpen);
        }
        self.directives.push(OpenDirective::alias(namespace, alias));
        Ok(())
    }
}

#[derive(Clone, PartialEq, Eq)]
pub enum Scope<'db> {
    Lexical(LexicalScope<'db>),
    Namespace(QualifiedName<'db>, LexicalScope<'db>),
}

impl<'db> Scope<'db> {
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
        self.lexical_scope_mut().add_open(namespace)
    }

    fn add_alias(
        &mut self,
        alias: QualifiedName<'db>,
        target: QualifiedName<'db>,
    ) -> OpenResult<()> {
        self.lexical_scope_mut().add_alias(alias, target)
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

#[derive(Clone, PartialEq, Eq)]
pub struct Resolver<'db> {
    /// The current namespace.
    namespace: Option<QualifiedName<'db>>,
    scopes: Vec<Scope<'db>>,
}

impl<'db> Resolver<'db> {
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
        let new_namespace = QualifiedName::qualify_path(db, self.namespace, path)
            .expect("push_namespace requires non-empty path");
        let mut scopes = self.scopes.clone();
        scopes.push(Scope::Namespace(new_namespace, LexicalScope::new()));
        Self {
            namespace: Some(new_namespace),
            scopes,
        }
    }

    /// Open a namespace in the current scope.
    pub fn open_namespace(mut self, namespace: QualifiedName<'db>) -> OpenResult<()> {
        self.scopes
            .last_mut()
            .expect("push_scope should have been called in constructor")
            .add_open(namespace)
    }

    /// Alias a namepace in the current scope.
    pub fn alias_namespace(
        mut self,
        alias: QualifiedName<'db>,
        target: QualifiedName<'db>,
    ) -> OpenResult<()> {
        self.scopes
            .last_mut()
            .expect("push_scope should have been called in constructor")
            .add_alias(alias, target)
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
///    a. Try qualifying the path against the current namespace (or root if None)
///    b. For each OpenDirective in the scope, try resolving the path
///    c. Check if each qualified name exists in stub_table
///    d. Collect all existing qualified names
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
    Db: salsa::Database + ?Sized,
{
    // Internal API contract: path must be non-empty
    debug_assert!(!path.is_empty(), "resolve_path requires non-empty path");

    // Iterate through scopes from innermost to outermost
    for scope in resolver.scopes.iter().rev() {
        let mut candidates = Vec::new();

        // Try qualifying the path against the current namespace (or root if None)
        if let Some(qualified) = QualifiedName::qualify_path(db, resolver.namespace, path) {
            if stub_table.contains(qualified) {
                candidates.push(qualified);
            }
        }

        // For each OpenDirective in the scope, try resolving the path.
        let lexical_scope = scope.lexical_scope();
        for directive in &lexical_scope.directives {
            if let Some(qualified) = directive.resolve(db, path) {
                if stub_table.contains(qualified) {
                    candidates.push(qualified);
                }
            }
        }

        // If we found at least one candidate in this scope, deduplicate and return
        if !candidates.is_empty() {
            // Deduplicate using a HashSet
            let unique_candidates: HashSet<QualifiedName<'db>> = candidates.into_iter().collect();
            return unique_candidates.into_iter().collect();
        }
    }

    // No scopes yielded any results
    Vec::new()
}
