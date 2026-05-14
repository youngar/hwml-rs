use std::rc::Rc;

use hwml_core::{
    name::Name,
    syn::Telescope,
    ty::Ty,
    val::{ConstantInfo, DataConstructorInfo, GlobalEnv, PrimitiveInfo, TypeConstructorInfo},
    QualifiedName, RcSyntax, Source, SourceInfo, UniverseLevel, Word,
};
use hwml_support::FromWithDb;
use hwml_surface::{Program, Statement};

// TODO(critical): This module needs several major features before production:
// 1. Thread real Source (not synthetic) through elaboration for error messages
//    See design/package-manager.md Part 1 "Source Location Architecture"
// 2. Implement pattern_quote/renaming for meta-variable solving
//    See design/renaming.md - required for pruning and occurs check
// 3. Implement open modifiers (only, hiding, renaming)
// 4. Test data constructor resolution from stub table

use crate::{
    ctx::ElabCtx,
    elab::{self, Elaborator},
    error::ElabError,
    names::str_to_simple_qname,
    resolver::{OpenError, Resolver},
    state::SolverState,
    stub_table::StubTable,
    util::surface_id_to_path,
    zonk::{substitute_metas_in_syntax, zonk},
};

/// Helper to create a synthetic source for testing/entry points
fn synthetic_source<'db>(db: &'db dyn salsa::Database, label: &str) -> Source<'db> {
    let word = Word::new(db, label);
    Source::new(db, SourceInfo::Synthetic(word))
}

/// An elaborated top-level declaration.
#[derive(Debug, Clone)]
pub enum ElaboratedDecl<'db> {
    Constant {
        name: QualifiedName<'db>,
        info: ConstantInfo<'db>,
    },
    Primitive {
        name: QualifiedName<'db>,
        info: PrimitiveInfo<'db>,
    },
    TypeConstructor {
        name: QualifiedName<'db>,
        info: TypeConstructorInfo<'db>,
    },
}

/// Result of elaborating a surface `Program`.
pub struct ElabProgramResult<'db> {
    pub decls: Vec<ElaboratedDecl<'db>>,
    pub errors: Vec<ElabError<'db>>,
}

/// Global elaboration environment for program-level name resolution.
/// Combines resolver (for scoping) and stub_table (for name lookup).
///
/// This is distinct from ElabCtx which handles local variables (lambda/Pi binders).
/// GlobalElabEnv manages namespaces, open statements, and global declarations.
struct GlobalElabEnv<'db> {
    resolver: Resolver<'db>,
    stub_table: StubTable<'db>,
}

impl<'db> GlobalElabEnv<'db> {
    fn new() -> Self {
        Self {
            resolver: Resolver::new(),
            stub_table: StubTable::new(),
        }
    }
}

/// Elaborate all declarations in a surface `Program`, accumulating errors.
///
/// Declarations are processed in two passes:
/// - First, harvest all declarations into the stub table (for order-independent resolution)
/// - Then, elaborate each declaration using the populated stub table and resolver
///
/// # Arguments
/// * `source` - Optional source file identifier. If None, uses a synthetic source.
pub fn elab_program<'db, Db>(
    db: &'db Db,
    global: &mut GlobalEnv<'db>,
    program: &Program,
) -> ElabProgramResult<'db>
where
    Db: salsa::Database,
{
    elab_program_with_source(db, global, program, None)
}

/// Elaborate a program with an explicit source identifier.
///
/// This version allows specifying the source file for better error messages.
pub fn elab_program_with_source<'db, Db>(
    db: &'db Db,
    global: &mut GlobalEnv<'db>,
    program: &Program,
    source: Option<Source<'db>>,
) -> ElabProgramResult<'db>
where
    Db: salsa::Database,
{
    let mut decls = Vec::new();
    let mut errors = Vec::new();
    let mut global_env = GlobalElabEnv::new();

    // Use provided source or create synthetic one
    let source = source.unwrap_or_else(|| {
        let label = Word::new(db, "<synthetic>");
        Source::new(db, SourceInfo::Synthetic(label))
    });

    // Start at root namespace (None = global root)
    let root_namespace: Option<QualifiedName<'db>> = None;

    if let Err(harvest_err) = crate::stub_table::harvest_program(
        db,
        &mut global_env.stub_table,
        source,
        root_namespace,
        program,
    ) {
        // Convert harvesting error to ElabError
        errors.push(ElabError::NotInScope {
            name: format!("Harvesting error: {}", harvest_err),
            span: None,
            elab_backtrace: Vec::new(),
        });
    }

    // Elaborate declarations using the populated stub table.
    elab_statements(
        db,
        global,
        &program.statements,
        &global_env.resolver,
        &global_env.stub_table,
        source,
        &mut decls,
        &mut errors,
    );

    ElabProgramResult { decls, errors }
}

/// Elaborate a surface `Program` using a pre-built global `StubTable`.
///
/// This variant is used for workspace-mode compilation where the `StubTable`
/// has already been populated from all files in the workspace via
/// `workspace_declarations()`.
///
/// Unlike `elab_program()`, this does NOT harvest declarations - it uses the
/// provided `StubTable` directly. This enables:
/// - Multi-file compilation with cross-file references
/// - Library-level aggregation (all files pooled together)
/// - Cross-library dependency resolution
///
/// # Arguments
/// * `global_stub_table` - Pre-built StubTable from `workspace_declarations()`
///   containing declarations from all files and dependencies
/// * `source` - Source file identifier for error messages
///
/// # Example
/// ```ignore
/// // Load workspace
/// let workspace_stubs = workspace_declarations(&db, manifest_path);
///
/// // Parse each file
/// for file in workspace_files {
///     let program = parse(file);
///
///     // Elaborate with global stub table
///     let result = elab_program_with_global_stubs(
///         &db, &mut global, &program, &workspace_stubs, source
///     );
/// }
/// ```
pub fn elab_program_with_global_stubs<'db, Db>(
    db: &'db Db,
    global: &mut GlobalEnv<'db>,
    program: &Program,
    global_stub_table: &StubTable<'db>,
    source: Source<'db>,
) -> ElabProgramResult<'db>
where
    Db: salsa::Database,
{
    let mut decls = Vec::new();
    let mut errors = Vec::new();

    // Create resolver with default namespace
    let resolver = Resolver::new();

    // Elaborate using the pre-built global stub table
    elab_statements(
        db,
        global,
        &program.statements,
        &resolver,
        global_stub_table,
        source,
        &mut decls,
        &mut errors,
    );

    ElabProgramResult { decls, errors }
}

/// Hoist all `Open` statements to create the scope for a block.
/// Returns a new resolver with all opens applied.
///
/// This implements Pass 1 of statement elaboration: scope construction.
fn hoist_open_statements<'db, Db>(
    db: &'db Db,
    statements: &[Statement],
    resolver: &Resolver<'db>,
    errors: &mut Vec<ElabError<'db>>,
) -> Resolver<'db>
where
    Db: salsa::Database,
{
    let mut block_resolver = resolver.clone();

    for stmt in statements {
        if let Statement::Open(open) = stmt {
            // Convert surface Id to path
            let path = match surface_id_to_path(db, &open.namespace) {
                Ok(p) if !p.is_empty() => p,
                Ok(_) => continue, // Empty path
                Err(e) => {
                    // Report specific error (wildcard, consecutive underscores, etc.)
                    errors.push(ElabError::NotInScope {
                        name: format!("Invalid open namespace '{}': {}", open.namespace.value, e),
                        span: None,
                        elab_backtrace: Vec::new(),
                    });
                    continue;
                }
            };

            // Qualify the namespace path against the parent resolver.
            // Note: We don't validate that the namespace exists in the stub table here.
            // Namespaces themselves are not declarations (they don't have entries in stub_table).
            // The resolver will handle name resolution for declarations within the namespace.
            let target_ns = resolver.qualify_path(db, &path);

            // Handle alias if present
            if let Some(ref alias_id) = open.as_alias {
                let alias_path = match surface_id_to_path(db, alias_id) {
                    Ok(p) if !p.is_empty() => p,
                    Ok(_) => continue, // Empty path
                    Err(e) => {
                        errors.push(ElabError::NotInScope {
                            name: format!("Invalid alias '{}': {}", alias_id.value, e),
                            span: None,
                            elab_backtrace: Vec::new(),
                        });
                        continue;
                    }
                };
                let alias_path = alias_path.into_boxed_slice();
                // Add the alias to the scope
                block_resolver = match block_resolver.alias_namespace(target_ns, alias_path) {
                    Ok(new_resolver) => new_resolver,
                    Err((OpenError::DuplicateOpen, resolver_back)) => {
                        errors.push(ElabError::NotInScope {
                            name: format!("Duplicate alias: {}", &alias_id.value),
                            span: None,
                            elab_backtrace: Vec::new(),
                        });
                        resolver_back
                    }
                };
            } else {
                // Unqualified open
                block_resolver = match block_resolver.open_namespace(target_ns) {
                    Ok(new_resolver) => new_resolver,
                    Err((OpenError::DuplicateOpen, resolver_back)) => {
                        errors.push(ElabError::NotInScope {
                            name: format!("Duplicate open: {}", &open.namespace.value),
                            span: None,
                            elab_backtrace: Vec::new(),
                        });
                        resolver_back
                    }
                };
            }

            // TODO: Implement open modifiers (only, hiding, renaming)
            // For now, return an error rather than silently ignoring them
            if !open.modifiers.is_empty() {
                errors.push(ElabError::NotImplemented {
                    feature: format!(
                        "open modifiers (only/hiding/renaming) for namespace: {}",
                        &open.namespace.value
                    ),
                    span: None,
                    elab_backtrace: Vec::new(),
                });
                continue;
            }
        }
    }

    block_resolver
}

/// Elaborate a `Def` statement (constant definition).
fn elab_def_statement<'db, Db>(
    db: &'db Db,
    global: &mut GlobalEnv<'db>,
    def: &hwml_surface::Def,
    resolver: &Resolver<'db>,
    stub_table: &StubTable<'db>,
    source: Source<'db>,
    decls: &mut Vec<ElaboratedDecl<'db>>,
    errors: &mut Vec<ElabError<'db>>,
) where
    Db: salsa::Database,
{
    let qname = match str_to_simple_qname(db, resolver.namespace(), &def.id.value) {
        Ok(qn) => qn,
        Err(e) => {
            errors.push(ElabError::NotInScope {
                name: format!("Invalid definition name: {}", e),
                span: None,
                elab_backtrace: Vec::new(),
            });
            return;
        }
    };

    // Elaborate inside a block so `global` borrow ends before mutation.
    // NOTE: Namespace resolution for the constant is handled inside elab_constant
    let result: Result<ConstantInfo<'db>, ElabError<'db>> = {
        let mut state = SolverState::new();
        let mut elab = Elaborator::new(global, ElabCtx::empty(), &mut state, resolver, stub_table, source);
        elab::decl::elab_constant(db, &mut elab, def).and_then(|elaborated| {
            zonk(&mut state)?;
            let ty = substitute_metas_in_syntax(db, &elaborated.ty, &state);
            let val = substitute_metas_in_syntax(db, &elaborated.value, &state);
            Ok(ConstantInfo::new(ty, val))
        })
    };

    match result {
        Ok(info) => {
            global.add_constant(qname, info.clone());
            decls.push(ElaboratedDecl::Constant { name: qname, info });
        }
        Err(e) => errors.push(e),
    }
}

/// Elaborate a `Prim` statement (primitive declaration).
fn elab_prim_statement<'db, Db>(
    db: &'db Db,
    global: &mut GlobalEnv<'db>,
    prim: &hwml_surface::Prim,
    resolver: &Resolver<'db>,
    stub_table: &StubTable<'db>,
    source: Source<'db>,
    decls: &mut Vec<ElaboratedDecl<'db>>,
    errors: &mut Vec<ElabError<'db>>,
) where
    Db: salsa::Database,
{
    let qname = match str_to_simple_qname(db, resolver.namespace(), &prim.id.value) {
        Ok(qn) => qn,
        Err(e) => {
            errors.push(ElabError::NotInScope {
                name: format!("Invalid primitive name: {}", e),
                span: None,
                elab_backtrace: Vec::new(),
            });
            return;
        }
    };

    let result: Result<PrimitiveInfo<'db>, ElabError<'db>> = {
        let mut state = SolverState::new();
        let mut elab = Elaborator::new(global, ElabCtx::empty(), &mut state, resolver, stub_table, source);
        use hwml_core::ty::Ty;
        elab::expr::check(db, &mut elab, &prim.ty, Rc::new(Ty::UniverseType)).and_then(|checked| {
            zonk(&mut state)?;
            let ty = substitute_metas_in_syntax(db, &checked.into_inner(), &state);
            Ok(PrimitiveInfo::new(ty))
        })
    };

    match result {
        Ok(info) => {
            global.add_primitive(qname, info.clone());
            decls.push(ElaboratedDecl::Primitive { name: qname, info });
        }
        Err(e) => errors.push(e),
    }
}

/// Elaborate an `Inductive` statement (type + data constructor declarations).
/// Uses a 3-phase approach to enable self-references.
fn elab_inductive_statement<'db, Db>(
    db: &'db Db,
    global: &mut GlobalEnv<'db>,
    ind: &hwml_surface::Inductive,
    resolver: &Resolver<'db>,
    stub_table: &StubTable<'db>,
    source: Source<'db>,
    decls: &mut Vec<ElaboratedDecl<'db>>,
    errors: &mut Vec<ElabError<'db>>,
) where
    Db: salsa::Database,
{
    // CRITICAL: Use the QualifiedName from the stub table, not a freshly created one!
    // The stub table has the canonical QualifiedName that was created during workspace harvesting.
    // Creating a new one via bytes_to_simple_qname will have a different Salsa ID!
    let ind_path = match surface_id_to_path(db, &ind.name) {
        Ok(p) if !p.is_empty() => p,
        Ok(_) => {
            errors.push(ElabError::NotInScope {
                name: format!("Inductive name '{}' is empty", ind.name.value),
                span: None,
                elab_backtrace: Vec::new(),
            });
            return;
        }
        Err(e) => {
            errors.push(ElabError::NotInScope {
                name: format!("Invalid inductive name '{}': {}", ind.name.value, e),
                span: None,
                elab_backtrace: Vec::new(),
            });
            return;
        }
    };
    let qname = resolver.qualify_path(db, &ind_path);

    // Push the inductive's namespace for parameter/index elaboration
    // This matches the behavior in elab_inductive_impl where everything uses the inductive's namespace
    let ind_resolver = resolver.push_namespace(db, &ind_path);

    // PHASE 1: Elaborate header to get type constructor signature
    // This must happen BEFORE elaborating constructors so self-references work
    // CRITICAL: Use ind_resolver so that names resolve in the inductive's namespace context
    let mut header_state = SolverState::new();
    let header_result: Result<
        (Vec<RcSyntax<'db>>, Vec<RcSyntax<'db>>, RcSyntax<'db>),
        ElabError<'db>,
    > = (|| {
        let mut elab = Elaborator::new(
            global,
            ElabCtx::empty(),
            &mut header_state,
            &ind_resolver, // Use the namespace-pushed resolver
            stub_table,
            source,
        );
        let (params, _) = elab::decl::elab_telescope(db, &mut elab, &ind.parameters.groups)?;
        let (indices, _) = elab::decl::elab_telescope(db, &mut elab, &ind.indices.groups)?;
        let universe = elab::expr::check(db, &mut elab, &ind.universe, Rc::new(Ty::UniverseType))?
            .into_inner();
        Ok((params, indices, universe))
    })();

    // PHASE 2: Hoist the type constructor into GlobalEnv
    let (params, indices, universe) = match header_result {
        Ok(result) => {
            let (params, indices, universe) = result;
            let mut args = params.clone();
            args.extend(indices.clone());
            // Convert Vec<RcSyntax> to Telescope with numbered names
            let args_telescope = Telescope::from_pairs(
                args.into_iter()
                    .enumerate()
                    .map(|(i, ty)| (hwml_core::name::Name::from_with_db(db, format!("{}", i)), ty))
            );
            let level = extract_universe_level(&universe);
            let stub_info = TypeConstructorInfo::new(args_telescope, params.len(), UniverseLevel::new(level));
            global.add_type_constructor(qname, stub_info);
            (params, indices, universe)
        }
        Err(e) => {
            eprintln!(
                "[HOIST] Phase 1 failed for {}: {:?}",
                qname.to_string(db),
                e
            );
            errors.push(e);
            return;
        }
    };

    // PHASE 3: Now elaborate the full inductive (including constructors)
    let result: Result<
        (
            TypeConstructorInfo<'db>,
            Vec<(QualifiedName<'db>, DataConstructorInfo<'db>)>,
        ),
        ElabError<'db>,
    > = {
        let mut state = SolverState::new();
        let mut elab = Elaborator::new(global, ElabCtx::empty(), &mut state, resolver, stub_table, source);
        elab::decl::elab_inductive(db, &mut elab, ind).and_then(|elaborated| {
            zonk(&mut state)?;
            let num_params = elaborated.params.len();
            let args: Vec<_> = elaborated
                .params
                .iter()
                .chain(elaborated.indices.iter())
                .map(|s| substitute_metas_in_syntax(db, s, &state))
                .collect();
            // Convert Vec<RcSyntax> to Telescope with numbered names
            let args_telescope = Telescope::from_pairs(
                args.into_iter()
                    .enumerate()
                    .map(|(i, ty)| (hwml_core::name::Name::from_with_db(db, format!("{}", i)), ty))
            );
            let universe_syn = substitute_metas_in_syntax(db, &elaborated.universe, &state);
            let level = extract_universe_level(&universe_syn);
            let tcon_info = TypeConstructorInfo::new(args_telescope, num_params, UniverseLevel::new(level));

            // Build DataConstructorInfo for each constructor
            let mut data_constructors = Vec::new();
            for ctor in &elaborated.constructors {
                let ctor_name_str = String::from_utf8_lossy(&ctor.name).into_owned();
                let ctor_path = match surface_id_to_path(
                    db,
                    &hwml_surface::Id {
                        value: ctor_name_str.clone().into(),
                        loc: 0..0,
                    },
                ) {
                    Ok(p) if !p.is_empty() => p,
                    Ok(_) => {
                        return Err(ElabError::NotInScope {
                            name: format!("Constructor name '{}' is empty", ctor_name_str),
                            span: None,
                            elab_backtrace: Vec::new(),
                        });
                    }
                    Err(e) => {
                        return Err(ElabError::NotInScope {
                            name: format!("Invalid constructor name '{}': {}", ctor_name_str, e),
                            span: None,
                            elab_backtrace: Vec::new(),
                        });
                    }
                };
                let ctor_qname = QualifiedName::qualify_path(db, Some(qname), &ctor_path)
                    .ok_or_else(|| ElabError::NotInScope {
                        name: "Failed to qualify constructor name".to_string(),
                        span: None,
                        elab_backtrace: Vec::new(),
                    })?;
                let ctor_ty = substitute_metas_in_syntax(db, &ctor.result, &state);
                // Convert Vec<RcSyntax> to Telescope with numbered names
                let params_telescope = Telescope::from_pairs(
                    ctor.params.iter().cloned()
                        .enumerate()
                        .map(|(i, ty)| (hwml_core::name::Name::from_with_db(db, format!("{}", i)), ty))
                );
                let dcon_info = DataConstructorInfo::new(params_telescope, ctor_ty);
                data_constructors.push((ctor_qname, dcon_info));
            }

            Ok((tcon_info, data_constructors))
        })
    };

    match result {
        Ok((info, data_constructors)) => {
            eprintln!(
                "[ELAB] Adding type constructor {} with {} data constructors",
                qname.to_string(db),
                data_constructors.len()
            );
            global.add_type_constructor(qname, info.clone());
            decls.push(ElaboratedDecl::TypeConstructor { name: qname, info });

            // Add all data constructors to the global environment
            for (ctor_qname, dcon_info) in data_constructors {
                eprintln!(
                    "[ELAB] Adding data constructor {}",
                    ctor_qname.to_string(db)
                );
                global.add_data_constructor(ctor_qname, dcon_info);
            }
        }
        Err(e) => {
            eprintln!(
                "[ELAB] Error elaborating inductive {}: {}",
                qname.to_string(db),
                match &e {
                    ElabError::NotInScope { name, .. } => {
                        format!("NotInScope: {}", name)
                    }
                    _ => format!("{:?}", e),
                }
            );
            errors.push(e);
        }
    }
}

/// Elaborate a `Namespace` statement (nested declarations).
/// This function is separate to enable the forward declaration needed for recursion.
fn elab_namespace_statement<'db, Db>(
    db: &'db Db,
    global: &mut GlobalEnv<'db>,
    ns: &hwml_surface::Namespace,
    resolver: &Resolver<'db>,
    stub_table: &StubTable<'db>,
    source: Source<'db>,
    decls: &mut Vec<ElaboratedDecl<'db>>,
    errors: &mut Vec<ElabError<'db>>,
) where
    Db: salsa::Database,
{
    // Convert the namespace Id to a path
    let ns_path = match surface_id_to_path(db, &ns.name) {
        Ok(p) if !p.is_empty() => p,
        Ok(_) => {
            errors.push(ElabError::NotInScope {
                name: format!("Namespace name '{}' is empty", ns.name.value),
                span: None,
                elab_backtrace: Vec::new(),
            });
            return;
        }
        Err(e) => {
            errors.push(ElabError::NotInScope {
                name: format!("Invalid namespace name '{}': {}", ns.name.value, e),
                span: None,
                elab_backtrace: Vec::new(),
            });
            return;
        }
    };

    // Push a new namespace scope (functional style)
    let ns_resolver = resolver.push_namespace(db, &ns_path);

    // Recursively elaborate nested statements with the new resolver
    elab_statements(
        db,
        global,
        &ns.statements,
        &ns_resolver,
        stub_table,
        source,
        decls,
        errors,
    );
}

/// Elaborate statements with functional scope management.
/// The resolver is passed by value and cloned for nested scopes.
fn elab_statements<'db, Db>(
    db: &'db Db,
    global: &mut GlobalEnv<'db>,
    statements: &[Statement],
    resolver: &Resolver<'db>,
    stub_table: &StubTable<'db>,
    source: Source<'db>,
    decls: &mut Vec<ElaboratedDecl<'db>>,
    errors: &mut Vec<ElabError<'db>>,
) where
    Db: salsa::Database,
{
    // Pass 1: Hoist all Open statements to create the block scope
    let block_resolver = hoist_open_statements(db, statements, resolver, errors);

    // Pass 2: Elaborate declarations with the hoisted scope
    for stmt in statements {
        match stmt {
            Statement::Def(def) => {
                elab_def_statement(db, global, def, &block_resolver, stub_table, source, decls, errors);
            }
            Statement::Prim(prim) => {
                elab_prim_statement(db, global, prim, &block_resolver, stub_table, source, decls, errors);
            }
            Statement::Inductive(ind) => {
                elab_inductive_statement(
                    db,
                    global,
                    ind,
                    &block_resolver,
                    stub_table,
                    source,
                    decls,
                    errors,
                );
            }
            Statement::Namespace(ns) => {
                elab_namespace_statement(
                    db,
                    global,
                    ns,
                    &block_resolver,
                    stub_table,
                    source,
                    decls,
                    errors,
                );
            }
            Statement::Open(_) | Statement::Meta(_) => {
                // Open statements were already processed in Pass 1
                // Meta statements are currently ignored
            }
            Statement::Invalid(err) => {
                // Invalid statements from parse errors - skip elaboration
                // The parse error will already be reported
                eprintln!("[ELAB] Skipping invalid statement: {}", err.message);
            }
        }
    }
}

/// Extract universe level from a `Syntax::UniverseCode(n)` node. Defaults to 0.
fn extract_universe_level(syn: &hwml_core::Syntax) -> usize {
    match syn {
        hwml_core::Syntax::UniverseCode(n) => *n,
        _ => 0,
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// Library-Wide SCC-Based Elaboration
// ═══════════════════════════════════════════════════════════════════════════

/// Elaborate multiple programs (files) from a library using library-wide SCC-based elaboration.
///
/// This is the CORRECT entry point for library elaboration that supports mutual recursion
/// across files while preserving file-local `open` statements.
///
/// ## Architecture
///
/// 1. Gather all declarations from ALL files into a single flat list, each with its
///    file-local resolver (preserving `open` statements)
/// 2. Compute SCCs at the library level (files are transparent for dependency analysis)
/// 3. For each SCC, execute three-phase elaboration:
///    - Phase 1: Elaborate headers using each declaration's file-local resolver
///    - Phase 2: Hoist all stubs to GlobalEnv
///    - Phase 3: Elaborate bodies using each declaration's file-local resolver
///
/// This allows mutual recursion within and across files while maintaining file-local
/// lexical scoping and dependency ordering.
pub fn elab_library_with_sccs<'db, Db>(
    db: &'db Db,
    global: &mut GlobalEnv<'db>,
    programs: &[(std::path::PathBuf, &Program)],
    global_stub_table: &StubTable<'db>,
) -> ElabProgramResult<'db>
where
    Db: salsa::Database,
{
    use crate::scc::{compute_library_sccs, validate_scc_annotations, DeclInfo};
    use crate::scc_elab::{elaborate_bodies, elaborate_headers, hoist_headers};
    use crate::solver::Solver;

    let mut decls = Vec::new();
    let mut errors = Vec::new();

    // Step 1: Gather all declarations from ALL files into a single flat list
    let mut all_decls: Vec<DeclInfo<'db>> = Vec::new();

    for (source_path, program) in programs {
        // Create a file-local resolver for this file
        // This starts at root but will be updated as we process namespace/open statements
        let mut file_resolver = Resolver::new();

        // Process this file's open statements at the top level
        // (This is simplified - in reality we'd need to track opens as we traverse)
        for stmt in &program.statements {
            if let hwml_surface::Statement::Open(open_stmt) = stmt {
                if let Ok(path) = crate::util::surface_id_to_path(db, &open_stmt.namespace) {
                    if !path.is_empty() {
                        if let Some(qname) = QualifiedName::qualify_path(db, None, &path) {
                            // Check if it exists in the global stub table
                            if global_stub_table.get(qname).is_some() {
                                // Use open_namespace which returns Result<Self, (Error, Self)>
                                match file_resolver.clone().open_namespace(qname) {
                                    Ok(updated_resolver) => file_resolver = updated_resolver,
                                    Err((_, resolver)) => file_resolver = resolver, // Ignore duplicate opens
                                }
                            }
                        }
                    }
                }
            }
        }

        eprintln!(
            "[LIBRARY_ELAB] Gathering declarations from {}",
            source_path.display()
        );

        // Create a Source for this file
        let library_name = hwml_core::Word::new(db, "library"); // TODO: Get actual library name
        let path_string = source_path.display().to_string();
        let canonical_path = hwml_core::Word::new(db, path_string.as_str());
        let source_file_id = hwml_core::SourceFileId::new(db, library_name, canonical_path);
        let source = hwml_core::Source::new(db, hwml_core::SourceInfo::File(source_file_id));

        gather_declarations(
            db,
            &program.statements,
            None, // Start at root namespace
            &file_resolver,
            source,
            &mut all_decls,
        );
    }

    eprintln!(
        "[SCC] Gathered {} declarations from {} files",
        all_decls.len(),
        programs.len()
    );

    if all_decls.is_empty() {
        return ElabProgramResult { decls, errors };
    }

    // Step 2: Compute library-wide SCCs
    let sccs = compute_library_sccs(db, &all_decls, global_stub_table);

    eprintln!("[SCC] Computed {} SCCs", sccs.len());

    // Step 3: Process each SCC with three-phase elaboration
    for (scc_idx, scc) in sccs.iter().enumerate() {
        eprintln!(
            "[SCC] Processing SCC {} with {} declarations",
            scc_idx,
            scc.indices.len()
        );
        // Validate: mutually recursive defs must have type annotations
        if let Err(validation_error) = validate_scc_annotations(scc, &all_decls) {
            errors.push(ElabError::NotImplemented {
                feature: validation_error,
                span: None,
                elab_backtrace: Vec::new(),
            });
            continue;
        }

        // Create a fresh SolverState for this SCC
        let mut state = SolverState::new();

        // Phase 1: Elaborate headers (uses each declaration's file-local resolver)
        let headers = match elaborate_headers(
            db,
            global,
            &mut state,
            &Resolver::new(), // This is ignored - each decl uses its own resolver
            global_stub_table,
            scc,
            &all_decls,
        ) {
            Ok(h) => h,
            Err(e) => {
                errors.push(e);
                continue;
            }
        };

        // Phase 2: Hoist headers into GlobalEnv
        if let Err(e) = hoist_headers(db, global, &headers) {
            errors.push(e);
            continue;
        }

        // Phase 3: Elaborate bodies (uses each declaration's file-local resolver)
        let data_constructors = match elaborate_bodies(
            db,
            global,
            &mut state,
            &Resolver::new(), // This is ignored - each decl uses its own resolver
            global_stub_table,
            scc,
            &all_decls,
            &headers,
        ) {
            Ok(dcs) => dcs,
            Err(e) => {
                errors.push(e);
                continue;
            }
        };

        // Run constraint solver to completion
        // LENIENT: Continue even if solver fails (collect all errors)
        //
        // NOTE: Postponed checks (DOE) are currently not supported in program elaboration.
        // For now, we just run the solver and ignore ready checks.
        let mut solver = Solver::new(&mut state, global, db);
        match solver.run() {
            Ok(_ready_checks) => {
                // TODO(DOE): Process ready_checks here once DOE is fully enabled
            }
            Err(solve_err) => {
                use crate::solver::SolveError;
                match solve_err {
                    SolveError::NoProgress => {
                        errors.push(ElabError::NotImplemented {
                            feature: format!("Constraint solver made no progress in SCC {}", scc_idx),
                            span: None,
                            elab_backtrace: Vec::new(),
                        });
                    }
                    SolveError::Elab(elab_err) => {
                        errors.push(elab_err);
                    }
                }
                // Continue to next SCC instead of breaking the entire library
                continue;
            }
        }

        // Zonk to substitute solved metavariables
        // LENIENT: Continue even if zonking fails
        if let Err(e) = zonk(&mut state) {
            errors.push(e);
            continue;
        }

        // Hoist data constructors
        for (qname, dcon_info) in data_constructors {
            global.add_data_constructor(qname, dcon_info);
        }

        // Collect successfully elaborated declarations
        for (header_idx, &decl_idx) in scc.indices.iter().enumerate() {
            let header = &headers[header_idx];
            match header {
                crate::scc_elab::DeclHeader::TypeConstructor { qname, .. } => {
                    if let Ok(info) = global.type_constructor(*qname) {
                        decls.push(ElaboratedDecl::TypeConstructor {
                            name: *qname,
                            info: info.clone(),
                        });
                    }
                }
                crate::scc_elab::DeclHeader::Constant { qname, .. } => {
                    if let Ok(info) = global.constant(*qname) {
                        decls.push(ElaboratedDecl::Constant {
                            name: *qname,
                            info: info.clone(),
                        });
                    }
                }
                crate::scc_elab::DeclHeader::Primitive { qname, .. } => {
                    if let Ok(info) = global.primitive(*qname) {
                        decls.push(ElaboratedDecl::Primitive {
                            name: *qname,
                            info: info.clone(),
                        });
                    }
                }
            }
        }
    }

    ElabProgramResult { decls, errors }
}

/// Elaborate a single program using library-wide SCC-based elaboration.
///
/// DEPRECATED: Use `elab_library_with_sccs` instead for proper library-wide elaboration.
/// This function is kept for compatibility but calls the proper multi-file version.
///
/// This is the new entry point that supports mutual recursion across files.
///
/// ## Architecture
///
/// 1. Gather all top-level declarations from all statements into a flat list
/// 2. Compute SCCs at the library level (files are transparent)
/// 3. For each SCC, execute three-phase elaboration:
///    - Phase 1: Elaborate headers (type signatures, type constructor params)
///    - Phase 2: Hoist all stubs to GlobalEnv
///    - Phase 3: Elaborate bodies (can now reference each other)
///
/// This allows mutual recursion within and across files while maintaining
/// dependency ordering for non-recursive declarations.
pub fn elab_program_with_library_sccs<'db, Db>(
    db: &'db Db,
    global: &mut GlobalEnv<'db>,
    program: &Program,
    global_stub_table: &StubTable<'db>,
) -> ElabProgramResult<'db>
where
    Db: salsa::Database,
{
    use crate::scc::{compute_library_sccs, validate_scc_annotations, DeclInfo};
    use crate::scc_elab::{elaborate_bodies, elaborate_headers, hoist_headers};
    use crate::solver::Solver;

    let mut decls = Vec::new();
    let mut errors = Vec::new();

    // Create resolver (starts at root namespace)
    let resolver = Resolver::new();

    // Step 1: Gather all declarations into a flat list
    let mut all_decls: Vec<DeclInfo<'db>> = Vec::new();

    // Create a synthetic source for single-program elaboration
    let source_label = hwml_core::Word::new(db, "program");
    let source = hwml_core::Source::new(db, hwml_core::SourceInfo::Synthetic(source_label));

    gather_declarations(
        db,
        &program.statements,
        None, // Start at root namespace
        &resolver,
        source,
        &mut all_decls,
    );

    eprintln!("[SCC] Gathered {} declarations", all_decls.len());

    if all_decls.is_empty() {
        return ElabProgramResult { decls, errors };
    }

    // Step 2: Compute library-wide SCCs
    let sccs = compute_library_sccs(db, &all_decls, global_stub_table);

    eprintln!("[SCC] Computed {} SCCs", sccs.len());

    // Step 3: Process each SCC with three-phase elaboration
    for (scc_idx, scc) in sccs.iter().enumerate() {
        eprintln!(
            "[SCC] Processing SCC {} with {} declarations",
            scc_idx,
            scc.indices.len()
        );
        // Validate: mutually recursive defs must have type annotations
        if let Err(validation_error) = validate_scc_annotations(scc, &all_decls) {
            errors.push(ElabError::NotImplemented {
                feature: validation_error,
                span: None,
                elab_backtrace: Vec::new(),
            });
            continue;
        }

        // Create a fresh SolverState for this SCC
        let mut state = SolverState::new();

        // Phase 1: Elaborate headers
        let headers = match elaborate_headers(
            db,
            global,
            &mut state,
            &resolver,
            global_stub_table,
            scc,
            &all_decls,
        ) {
            Ok(h) => h,
            Err(e) => {
                errors.push(e);
                continue;
            }
        };

        // Phase 2: Hoist all headers as stubs
        if let Err(e) = hoist_headers(db, global, &headers) {
            errors.push(e);
            continue;
        }

        // Phase 3: Elaborate bodies
        let data_constructors = match elaborate_bodies(
            db,
            global,
            &mut state,
            &resolver,
            global_stub_table,
            scc,
            &all_decls,
            &headers,
        ) {
            Ok(dcs) => dcs,
            Err(e) => {
                errors.push(e);
                continue;
            }
        };

        // Run constraint solver to completion
        let mut solver = Solver::new(&mut state, global, db);
        match solver.run() {
            Ok(_ready_checks) => {
                // TODO(DOE): Process ready_checks here once DOE is fully enabled
            }
            Err(_e) => {
                errors.push(ElabError::UnificationFailure {
                    lhs: Rc::new(hwml_core::Value::UniverseCode(0)),
                    rhs: Rc::new(hwml_core::Value::UniverseCode(0)),
                    span: None,
                    elab_backtrace: Vec::new(),
                });
                continue;
            }
        }

        // Zonk to substitute solved metavariables
        if let Err(e) = zonk(&mut state) {
            errors.push(e);
            continue;
        }

        // Add data constructors to global environment
        for (ctor_qname, dcon_info) in data_constructors {
            global.add_data_constructor(ctor_qname, dcon_info.clone());
        }

        // Collect elaborated declarations for the result
        for header in &headers {
            match header {
                crate::scc_elab::DeclHeader::TypeConstructor { qname, .. } => {
                    if let Ok(info) = global.type_constructor(*qname) {
                        decls.push(ElaboratedDecl::TypeConstructor {
                            name: *qname,
                            info: info.clone(),
                        });
                    }
                }
                crate::scc_elab::DeclHeader::Constant { qname, .. } => {
                    if let Ok(info) = global.constant(*qname) {
                        decls.push(ElaboratedDecl::Constant {
                            name: *qname,
                            info: info.clone(),
                        });
                    }
                }
                crate::scc_elab::DeclHeader::Primitive { qname, .. } => {
                    if let Ok(info) = global.primitive(*qname) {
                        decls.push(ElaboratedDecl::Primitive {
                            name: *qname,
                            info: info.clone(),
                        });
                    }
                }
            }
        }
    }

    ElabProgramResult { decls, errors }
}

/// Recursively gather all declarations from a list of statements.
///
/// This flattens namespace hierarchies and processes all statements into a single
/// flat list of DeclInfo, making files transparent.
fn gather_declarations<'db, Db>(
    db: &'db Db,
    statements: &[Statement],
    current_namespace: Option<QualifiedName<'db>>,
    resolver: &Resolver<'db>,
    source: hwml_core::Source<'db>,
    out: &mut Vec<crate::scc::DeclInfo<'db>>,
) where
    Db: salsa::Database,
{
    for stmt in statements {
        match stmt {
            Statement::Namespace(ns) => {
                // Qualify namespace name
                let path = match surface_id_to_path(db, &ns.name) {
                    Ok(p) if !p.is_empty() => p,
                    Ok(_) => continue, // Empty namespace name
                    Err(e) => {
                        eprintln!(
                            "[STUB] Warning: Invalid namespace name '{}': {}",
                            ns.name.value, e
                        );
                        continue;
                    }
                };
                let ns_qname = match QualifiedName::qualify_path(db, current_namespace, &path) {
                    Some(q) => q,
                    None => continue,
                };

                // CRITICAL: Update the resolver to push this namespace onto the stack
                // This ensures that declarations inside the namespace have the correct resolver context
                let ns_resolver = resolver.push_namespace(db, &path);

                // Recursively gather declarations from nested namespace
                gather_declarations(db, &ns.statements, Some(ns_qname), &ns_resolver, source, out);
            }
            Statement::Def(_) | Statement::Inductive(_) | Statement::Prim(_) => {
                // CRITICAL: Use surface_id_to_path to handle dotted names like "Std.Bool"
                // This must match how the harvester creates QualifiedNames!
                let qname = match stmt {
                    Statement::Def(def) => {
                        let path = match surface_id_to_path(db, &def.id) {
                            Ok(p) if !p.is_empty() => p,
                            Ok(_) => continue, // Empty name
                            Err(e) => {
                                eprintln!(
                                    "[STUB] Warning: Invalid def name '{}': {}",
                                    def.id.value, e
                                );
                                continue;
                            }
                        };
                        match QualifiedName::qualify_path(db, current_namespace, &path) {
                            Some(q) => q,
                            None => continue,
                        }
                    }
                    Statement::Inductive(ind) => {
                        let path = match surface_id_to_path(db, &ind.name) {
                            Ok(p) if !p.is_empty() => p,
                            Ok(_) => continue, // Empty name
                            Err(e) => {
                                eprintln!(
                                    "[STUB] Warning: Invalid inductive name '{}': {}",
                                    ind.name.value, e
                                );
                                continue;
                            }
                        };
                        match QualifiedName::qualify_path(db, current_namespace, &path) {
                            Some(q) => q,
                            None => continue,
                        }
                    }
                    Statement::Prim(prim) => {
                        let path = match surface_id_to_path(db, &prim.id) {
                            Ok(p) if !p.is_empty() => p,
                            Ok(_) => continue, // Empty name
                            Err(e) => {
                                eprintln!(
                                    "[STUB] Warning: Invalid primitive name '{}': {}",
                                    prim.id.value, e
                                );
                                continue;
                            }
                        };
                        match QualifiedName::qualify_path(db, current_namespace, &path) {
                            Some(q) => q,
                            None => continue,
                        }
                    }
                    _ => unreachable!(),
                };

                // DEBUG: Show raw qualified name structure
                eprintln!(
                    "[GATHER] Created QualifiedName {:?} = '{}' | namespace: {:?} | segments: {:?}",
                    qname,
                    qname.to_string(db),
                    current_namespace.map(|n| n.to_string(db)),
                    qname
                        .segments(db)
                        .iter()
                        .map(|s| s.to_string(db))
                        .collect::<Vec<_>>()
                );

                // Add to flat list with the current resolver (captures file-local `open` statements)
                out.push(crate::scc::DeclInfo {
                    index: out.len(),
                    qualified_name: qname,
                    stmt: stmt.clone(),
                    resolver: resolver.clone(),
                    source,
                });
            }
            Statement::Open(_) | Statement::Meta(_) => {
                // These don't contribute to the SCC graph
            }
            Statement::Invalid(_) => {
                // Invalid statements from parse errors - skip
            }
        }
    }
}
