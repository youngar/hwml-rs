use std::rc::Rc;

use hwml_core::{
    val::{ConstantInfo, GlobalEnv, PrimitiveInfo, TypeConstructorInfo},
    QualifiedName, Source, SourceInfo, UniverseLevel, Word,
};
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
    names::bytes_to_simple_qname,
    resolver::{resolve_path, OpenError, Resolver},
    state::SolverState,
    stub_table::StubTable,
    util::surface_id_to_path,
    zonk::{substitute_metas_in_syntax, zonk},
};

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
pub fn elab_program<'db, Db>(
    db: &'db Db,
    global: &mut GlobalEnv<'db>,
    program: &Program,
) -> ElabProgramResult<'db>
where
    Db: salsa::Database,
{
    let mut decls = Vec::new();
    let mut errors = Vec::new();
    let mut global_env = GlobalElabEnv::new();

    // Harvest all declarations into the stub table.
    // This allows order-independent name resolution.
    // TODO: Replace synthetic source with real SourceFileId when threading through the pipeline
    let source = {
        let label = Word::new(db, "<synthetic>");
        Source::new(db, SourceInfo::Synthetic(label))
    };

    // Create root namespace - using FromWithDb to create a simple QualifiedName from a string
    let root_namespace: QualifiedName<'db> = hwml_support::FromWithDb::from_with_db(db, "");

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
        });
    }

    // Elaborate declarations using the populated stub table.
    elab_statements(
        db,
        global,
        &program.statements,
        &global_env.resolver,
        &global_env.stub_table,
        &mut decls,
        &mut errors,
    );

    ElabProgramResult { decls, errors }
}

/// Elaborate statements with functional scope management.
/// The resolver is passed by value and cloned for nested scopes.
fn elab_statements<'db, Db>(
    db: &'db Db,
    global: &mut GlobalEnv<'db>,
    statements: &[Statement],
    resolver: &Resolver<'db>,
    stub_table: &StubTable<'db>,
    decls: &mut Vec<ElaboratedDecl<'db>>,
    errors: &mut Vec<ElabError<'db>>,
) where
    Db: salsa::Database,
{
    // Hoist all Open statements from this block to create the scope
    let mut block_resolver = resolver.clone();
    for stmt in statements {
        if let Statement::Open(open) = stmt {
            // Convert surface Id to path
            let path = match surface_id_to_path(db, &open.namespace) {
                Some(p) => p,
                None => {
                    // Empty path - this shouldn't happen with valid syntax
                    continue;
                }
            };

            // Resolve the namespace path against the parent resolver
            let candidates = resolve_path(db, stub_table, resolver, &path);

            if candidates.is_empty() {
                // Namespace not found
                errors.push(ElabError::NotInScope {
                    name: String::from_utf8_lossy(&open.namespace.value).to_string(),
                    span: None,
                });
                continue;
            }

            if candidates.len() > 1 {
                // Ambiguous namespace - use NotInScope as a placeholder
                errors.push(ElabError::NotInScope {
                    name: format!(
                        "Ambiguous: {}",
                        String::from_utf8_lossy(&open.namespace.value)
                    ),
                    span: None,
                });
                continue;
            }

            let target_ns = candidates[0];

            // Handle alias if present
            if let Some(ref alias_id) = open.as_alias {
                let alias_path = match surface_id_to_path(db, alias_id) {
                    Some(p) => p,
                    None => continue,
                };
                let alias_qname = block_resolver.qualify_path(db, &alias_path);

                // Add the alias to the scope
                block_resolver = match block_resolver.alias_namespace(alias_qname, target_ns) {
                    Ok(new_resolver) => new_resolver,
                    Err((OpenError::DuplicateOpen, resolver_back)) => {
                        errors.push(ElabError::NotInScope {
                            name: format!(
                                "Duplicate alias: {}",
                                String::from_utf8_lossy(&alias_id.value)
                            ),
                            span: None,
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
                            name: format!(
                                "Duplicate open: {}",
                                String::from_utf8_lossy(&open.namespace.value)
                            ),
                            span: None,
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
                        String::from_utf8_lossy(&open.namespace.value)
                    ),
                    span: None,
                });
                continue;
            }
        }
    }

    // Now elaborate the non-Open statements with the hoisted scope
    for stmt in statements {
        match stmt {
            Statement::Def(def) => {
                let qname = bytes_to_simple_qname(db, block_resolver.namespace(), &def.id.value);
                // Elaborate inside a block so `global` borrow ends before mutation.
                let result: Result<ConstantInfo<'db>, ElabError<'db>> = {
                    let mut state = SolverState::new();
                    let mut elab = Elaborator::new(
                        global,
                        ElabCtx::empty(),
                        &mut state,
                        &block_resolver,
                        stub_table,
                    );
                    elab::decl::elab_constant(db, &mut elab, def).and_then(|elaborated| {
                        zonk(&mut state)?;
                        let ty = substitute_metas_in_syntax(&elaborated.ty, &state);
                        let val = substitute_metas_in_syntax(&elaborated.value, &state);
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
            Statement::Prim(prim) => {
                let qname = bytes_to_simple_qname(db, block_resolver.namespace(), &prim.id.value);
                let result: Result<PrimitiveInfo<'db>, ElabError<'db>> = {
                    let mut state = SolverState::new();
                    let mut elab = Elaborator::new(
                        global,
                        ElabCtx::empty(),
                        &mut state,
                        &block_resolver,
                        stub_table,
                    );
                    use hwml_core::ty::Ty;
                    elab::expr::check(db, &mut elab, &prim.ty, Rc::new(Ty::UniverseType)).and_then(
                        |checked| {
                            zonk(&mut state)?;
                            let ty = substitute_metas_in_syntax(&checked.into_inner(), &state);
                            Ok(PrimitiveInfo::new(ty))
                        },
                    )
                };
                match result {
                    Ok(info) => {
                        global.add_primitive(qname, info.clone());
                        decls.push(ElaboratedDecl::Primitive { name: qname, info });
                    }
                    Err(e) => errors.push(e),
                }
            }
            Statement::Inductive(ind) => {
                let qname = bytes_to_simple_qname(db, block_resolver.namespace(), &ind.name.value);
                let result: Result<TypeConstructorInfo<'db>, ElabError<'db>> = {
                    let mut state = SolverState::new();
                    let mut elab = Elaborator::new(
                        global,
                        ElabCtx::empty(),
                        &mut state,
                        &block_resolver,
                        stub_table,
                    );
                    elab::decl::elab_inductive(db, &mut elab, ind).and_then(|elaborated| {
                        zonk(&mut state)?;
                        let num_params = elaborated.params.len();
                        let args: Vec<_> = elaborated
                            .params
                            .iter()
                            .chain(elaborated.indices.iter())
                            .map(|s| substitute_metas_in_syntax(s, &state))
                            .collect();
                        let universe_syn = substitute_metas_in_syntax(&elaborated.universe, &state);
                        let level = extract_universe_level(&universe_syn);
                        Ok(TypeConstructorInfo::new(
                            args,
                            num_params,
                            UniverseLevel::new(level),
                        ))
                    })
                };
                match result {
                    Ok(info) => {
                        global.add_type_constructor(qname, info.clone());
                        decls.push(ElaboratedDecl::TypeConstructor { name: qname, info });
                    }
                    Err(e) => errors.push(e),
                }
            }
            Statement::Namespace(ns) => {
                // Convert the namespace Id to a path
                let ns_path = match surface_id_to_path(db, &ns.name) {
                    Some(p) => p,
                    None => {
                        errors.push(ElabError::NotInScope {
                            name: "Invalid namespace name".to_string(),
                            span: None,
                        });
                        continue;
                    }
                };

                // Push a new namespace scope (functional style)
                let ns_resolver = block_resolver.push_namespace(db, &ns_path);

                // Recursively elaborate nested statements with the new resolver
                elab_statements(
                    db,
                    global,
                    &ns.statements,
                    &ns_resolver,
                    stub_table,
                    decls,
                    errors,
                );
            }
            Statement::Open(_) | Statement::Meta(_) => {}
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
