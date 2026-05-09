//! Three-Phase SCC-Based Elaboration
//!
//! This module implements library-wide elaboration using Strongly Connected Components (SCCs)
//! to support mutual recursion across files.
//!
//! ## Architecture
//!
//! Files have no semantic meaning in HWML - namespaces can span multiple files.
//! Therefore, we must compute SCCs at the library level, not per-file.
//!
//! ## Three Phases
//!
//! 1. **Header Phase**: Elaborate type signatures and type constructor headers
//! 2. **Hoist Phase**: Add all stubs to GlobalEnv simultaneously  
//! 3. **Body Phase**: Elaborate full definitions (can now reference each other)

use std::rc::Rc;

use hwml_core::{
    ty::{RcTy, Ty},
    val::{ConstantInfo, DataConstructorInfo, GlobalEnv, TypeConstructorInfo},
    QualifiedName, RcSyntax, Source, SourceRange, UniverseLevel,
};
use hwml_surface::{Def, Inductive, Statement};

use crate::{
    ctx::ElabCtx,
    elab::{self, Elaborator},
    error::ElabError,
    meta::MetaKind,
    resolver::Resolver,
    scc::{DeclInfo, Scc},
    state::SolverState,
    stub_table::StubTable,
    zonk::{substitute_metas_in_syntax, zonk},
};

// ─── Helper functions ─────────────────────────────────────────────────────────

/// Helper to create a SourceRange from a Def statement and its source.
fn def_span<'db>(source: Source<'db>, def: &Def) -> Option<SourceRange<'db>> {
    Some(SourceRange::new(source, def.loc.clone()))
}

/// Helper to create a SourceRange from an Inductive statement and its source.
fn ind_span<'db>(source: Source<'db>, ind: &Inductive) -> Option<SourceRange<'db>> {
    Some(SourceRange::new(source, ind.loc.clone()))
}

/// Helper to create a SourceRange from a Constructor and the inductive's source.
fn ctor_span<'db>(source: Source<'db>, ctor: &hwml_surface::Constructor) -> Option<SourceRange<'db>> {
    Some(SourceRange::new(source, ctor.loc.clone()))
}

/// Header information elaborated in Phase 1.
///
/// Stores both the elaborated type/signature AND the elaborated context (ElabCtx)
/// to ensure variable IDs remain consistent between Phase 1 and Phase 3.
#[derive(Debug, Clone)]
pub enum DeclHeader<'db> {
    TypeConstructor {
        qname: QualifiedName<'db>,
        params: Vec<RcSyntax<'db>>,
        indices: Vec<RcSyntax<'db>>,
        universe: RcSyntax<'db>,
        num_params: usize,
        /// The elaborated context after processing parameters+indices
        /// This is critical: Phase 3 MUST reuse this context to avoid variable ID mismatches
        param_ctx: crate::ctx::ElabCtx<'db>,
    },
    Constant {
        qname: QualifiedName<'db>,
        ty: RcSyntax<'db>,
        /// The elaborated context after processing the type signature's binders
        /// For simple constants this may be empty, for dependent functions it contains the parameters
        ty_ctx: crate::ctx::ElabCtx<'db>,
    },
    Primitive {
        qname: QualifiedName<'db>,
        ty: RcSyntax<'db>,
    },
}

/// Extract universe level from a `Syntax::UniverseCode(n)` node.
fn extract_universe_level(syn: &hwml_core::Syntax) -> usize {
    match syn {
        hwml_core::Syntax::UniverseCode(n) => *n,
        _ => 0,
    }
}

/// Phase 1: Elaborate headers for all declarations in an SCC.
///
/// For inductives: Elaborate parameters, indices, and universe.
/// For defs: Elaborate type signature (or create fresh metavariable if missing).
///
/// NOTE: The `resolver` parameter is no longer used - each declaration uses its own
/// file-local resolver stored in `DeclInfo`. This preserves file-local `open` statements.
pub fn elaborate_headers<'db, Db>(
    db: &'db Db,
    global: &GlobalEnv<'db>,
    state: &mut SolverState<'db>,
    _resolver: &Resolver<'db>, // Deprecated - kept for API compatibility
    stub_table: &StubTable<'db>,
    scc: &Scc,
    decls: &[DeclInfo<'db>],
) -> Result<Vec<DeclHeader<'db>>, ElabError<'db>>
where
    Db: salsa::Database,
{
    let mut headers = Vec::new();

    for &idx in &scc.indices {
        let decl_info = &decls[idx];

        // CRITICAL: Use the declaration's own resolver (file-local `open` statements)
        let decl_resolver = &decl_info.resolver;

        eprintln!(
            "[SCC_ELAB] Phase 1 (Header): Elaborating {}",
            decl_info.qualified_name.to_string(db)
        );

        match &decl_info.stmt {
            Statement::Inductive(ind) => {
                // Push the inductive's namespace for parameter/index elaboration
                // This ensures names resolve in the inductive's namespace context
                let ind_path = match crate::util::surface_id_to_path(db, &ind.name) {
                    Ok(p) if !p.is_empty() => p,
                    Ok(_) => {
                        return Err(ElabError::NotInScope {
                            name: format!("Inductive name '{}' is empty", ind.name.value),
                            span: ind_span(decl_info.source, ind),
                            elab_backtrace: Vec::new(),
                        });
                    }
                    Err(e) => {
                        return Err(ElabError::NotInScope {
                            name: format!("Invalid inductive name '{}': {}", ind.name.value, e),
                            span: ind_span(decl_info.source, ind),
                            elab_backtrace: Vec::new(),
                        });
                    }
                };
                let ind_resolver = decl_resolver.push_namespace(db, &ind_path);

                // Elaborate just the header: params, indices, universe
                let mut elab =
                    Elaborator::new(global, ElabCtx::empty(), state, &ind_resolver, stub_table, decl_info.source);

                // Elaborate parameters (returns both syntax and extended context)
                let (params, param_ctx) =
                    elab::decl::elab_telescope(db, &mut elab, &ind.parameters.groups)?;

                // Elaborate indices in the parameter context
                let (indices, param_idx_ctx) = {
                    let mut inner = Elaborator::new(
                        global,
                        param_ctx.clone(),
                        state,
                        &ind_resolver,
                        stub_table,
                        decl_info.source,
                    );
                    elab::decl::elab_telescope(db, &mut inner, &ind.indices.groups)?
                };

                // Elaborate universe in the param+index context
                let universe = {
                    let mut inner = Elaborator::new(
                        global,
                        param_idx_ctx.clone(),
                        state,
                        &ind_resolver,
                        stub_table,
                        decl_info.source,
                    );
                    elab::expr::check(db, &mut inner, &ind.universe, Rc::new(Ty::UniverseType))?
                        .into_inner()
                };

                headers.push(DeclHeader::TypeConstructor {
                    qname: decl_info.qualified_name,
                    params: params.clone(),
                    indices: indices.clone(),
                    universe,
                    num_params: params.len(),
                    param_ctx, // Store the parameter context for Phase 3!
                });
            }
            Statement::Def(def) => {
                // CRITICAL FIX FOR BUG #1: Build Pi Type in Phase 1
                //
                // For mutual recursion to work, other functions in the SCC must be able
                // to see the signature during Phase 2 hoisting. If we use a fresh meta,
                // the type is hidden as ?M and mutual calls fail!
                //
                // Strategy:
                // - If def has bindings, build the Pi type NOW (in Phase 1)
                // - Phase 3 will bidirectionally CHECK the Lambda body against this Pi type
                // - The check phase naturally handles variable bindings (no context cache needed)

                // CRITICAL: Use the file-local resolver as-is for type elaboration
                // The decl_resolver already has the correct namespace from the file/namespace block
                // For example, if elaborating `Std/Nat/add`, the resolver already has namespace `Std/Nat`
                // DON'T push the constant's own name onto the namespace!
                eprintln!(
                    "[SCC_ELAB] Phase 1: Using resolver with namespace {:?} for {}",
                    decl_resolver.namespace().map(|n| n.to_string(db)),
                    decl_info.qualified_name.to_string(db)
                );

                let mut elab =
                    Elaborator::new(global, ElabCtx::empty(), state, decl_resolver, stub_table, decl_info.source);

                let ty = if !def.bindings.groups.is_empty() {
                    // Has bindings like `def f (x : A) (y : B) : T`
                    // Build the Pi type: (x : A) -> (y : B) -> T
                    let typed_groups = elab::decl::collect_typed_groups(&def.bindings.groups);

                    if typed_groups.is_empty() {
                        // Only untyped binders - we need a type annotation
                        if let Some(ty_expr) = &def.ty {
                            elab::expr::check(db, &mut elab, ty_expr, Rc::new(Ty::UniverseType))?
                                .into_inner()
                        } else {
                            return Err(ElabError::CannotInfer {
                                span: def_span(decl_info.source, def),
                                elab_backtrace: elab.context.snapshot(),
                            });
                        }
                    } else {
                        // Build Pi type from typed bindings
                        let target = def
                            .ty
                            .as_ref()
                            .ok_or(ElabError::CannotInfer {
                                span: def_span(decl_info.source, def),
                                elab_backtrace: elab.context.snapshot(),
                            })?;
                        let pi = elab::decl::build_pi_expr(typed_groups, target);

                        elab::expr::check(
                            db,
                            &mut elab,
                            &hwml_surface::Expression::Pi(pi),
                            Rc::new(Ty::UniverseType),
                        )?
                        .into_inner()
                    }
                } else if let Some(ty_expr) = &def.ty {
                    // Simple case: `def name : Type = value` (no bindings)
                    elab::expr::check(db, &mut elab, ty_expr, Rc::new(Ty::UniverseType))?
                        .into_inner()
                } else {
                    // No annotation, no bindings: infer type from value in Phase 3
                    let depth = elab.kernel.ctx.depth();
                    let def_loc = def_span(decl_info.source, def);
                    let ty_meta = if let Some(loc) = def_loc {
                        elab.kernel.state.fresh_meta_with_provenance(
                            Rc::new(Ty::UniverseType),
                            depth,
                            MetaKind::UniverseLevel,
                            loc.clone(),
                            format!("unannotated definition '{:?}' at {:?}", decl_info.qualified_name, loc),
                        )
                    } else {
                        elab.kernel.state.fresh_meta(
                            Rc::new(Ty::UniverseType),
                            depth,
                            MetaKind::UniverseLevel,
                        )
                    };
                    elab.kernel.synth_meta(ty_meta)?.into_inner().0
                };

                headers.push(DeclHeader::Constant {
                    qname: decl_info.qualified_name,
                    ty,
                    ty_ctx: ElabCtx::empty(), // Not needed - Phase 3 checks against Pi type
                });
            }
            Statement::Prim(_) => {
                // Primitives don't participate in mutual recursion
                // We'll handle them separately
            }
            _ => {}
        }
    }

    Ok(headers)
}

/// Phase 2: Hoist all headers as stubs into the GlobalEnv.
///
/// This allows all declarations in the SCC to see each other's signatures.
pub fn hoist_headers<'db, Db>(
    db: &'db Db,
    global: &mut GlobalEnv<'db>,
    headers: &[DeclHeader<'db>],
) -> Result<(), ElabError<'db>>
where
    Db: salsa::Database,
{
    for header in headers {
        match header {
            DeclHeader::TypeConstructor {
                qname,
                params,
                indices,
                universe,
                num_params,
                param_ctx: _, // Ignore the cached context in Phase 2
            } => {
                eprintln!(
                    "[SCC_ELAB] Phase 2 (Hoist): Adding type constructor {}",
                    qname.to_string(db)
                );
                let mut args = params.clone();
                args.extend(indices.clone());
                let level = extract_universe_level(universe);
                let info = TypeConstructorInfo::new(args, *num_params, UniverseLevel::new(level));
                global.add_type_constructor(*qname, info);
                eprintln!(
                    "[SCC_ELAB] Phase 2 (Hoist): Verify - can we look it up? {:?}",
                    global.type_constructor(*qname)
                );
            }
            DeclHeader::Constant {
                qname,
                ty,
                ty_ctx: _,
            } => {
                // CRITICAL FIX: Create OPAQUE stub with dummy value
                // During mutual recursion, the evaluator will treat this as irreducible
                // to prevent infinite loops when type-checking the body
                let dummy_val = hwml_core::Syntax::constant_rc(*qname);
                let info = ConstantInfo::new_opaque(ty.clone(), dummy_val);
                global.add_constant(*qname, info);
            }
            DeclHeader::Primitive { qname, ty } => {
                let info = hwml_core::val::PrimitiveInfo::new(ty.clone());
                global.add_primitive(*qname, info);
            }
        }
    }

    Ok(())
}

/// Phase 3: Elaborate bodies for all declarations in an SCC.
///
/// The headers have already been hoisted, so declarations can reference each other.
///
/// NOTE: The `resolver` parameter is no longer used - each declaration uses its own
/// file-local resolver stored in `DeclInfo`. This preserves file-local `open` statements.
pub fn elaborate_bodies<'db, Db>(
    db: &'db Db,
    global: &mut GlobalEnv<'db>,
    state: &mut SolverState<'db>,
    _resolver: &Resolver<'db>, // Deprecated - kept for API compatibility
    stub_table: &StubTable<'db>,
    scc: &Scc,
    decls: &[DeclInfo<'db>],
    headers: &[DeclHeader<'db>],
) -> Result<Vec<(QualifiedName<'db>, DataConstructorInfo<'db>)>, ElabError<'db>>
where
    Db: salsa::Database,
{
    let mut data_constructors = Vec::new();

    for (header_idx, &decl_idx) in scc.indices.iter().enumerate() {
        let decl_info = &decls[decl_idx];
        let header = &headers[header_idx];

        // CRITICAL: Use the declaration's own resolver (file-local `open` statements)
        let decl_resolver = &decl_info.resolver;

        match (&decl_info.stmt, header) {
            (
                Statement::Inductive(ind),
                DeclHeader::TypeConstructor {
                    qname, param_ctx, ..
                },
            ) => {
                // CRITICAL FIX: Use the cached parameter context from Phase 1
                // This ensures variable IDs match between the signature and the body
                let mut elab =
                    Elaborator::new(global, param_ctx.clone(), state, decl_resolver, stub_table, decl_info.source);

                // Use lenient solver during mutual recursion
                let elaborated = elab::decl::elab_inductive_lenient(db, &mut elab, ind)?;

                // Process constructors
                for ctor in &elaborated.constructors {
                    let ctor_name_str = String::from_utf8_lossy(&ctor.name).into_owned();
                    let ctor_path = match crate::util::surface_id_to_path(
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
                                span: ind_span(decl_info.source, ind),
                                elab_backtrace: Vec::new(),
                            });
                        }
                        Err(e) => {
                            return Err(ElabError::NotInScope {
                                name: format!(
                                    "Invalid constructor name '{}': {}",
                                    ctor_name_str, e
                                ),
                                span: ind_span(decl_info.source, ind),
                                elab_backtrace: Vec::new(),
                            });
                        }
                    };

                    let ctor_qname = QualifiedName::qualify_path(db, Some(*qname), &ctor_path)
                        .ok_or_else(|| ElabError::NotInScope {
                            name: "Failed to qualify constructor name".to_string(),
                            span: ind_span(decl_info.source, ind),
                            elab_backtrace: Vec::new(),
                        })?;

                    let ctor_ty = substitute_metas_in_syntax(&ctor.result, state);
                    let dcon_info = DataConstructorInfo::new(ctor.params.clone(), ctor_ty);
                    data_constructors.push((ctor_qname, dcon_info));
                }
            }
            (Statement::Def(def), DeclHeader::Constant { qname, ty, ty_ctx }) => {
                // CRITICAL FIX: Use the cached type context from Phase 1
                // For most constants this will be empty, but for dependent functions
                // it contains the parameter bindings
                let mut elab =
                    Elaborator::new(global, ty_ctx.clone(), state, decl_resolver, stub_table, decl_info.source);

                // Use lenient solver during mutual recursion
                let elaborated = elab::decl::elab_constant_lenient(db, &mut elab, def)?;

                let val = substitute_metas_in_syntax(&elaborated.value, state);

                // Update the constant with the real value (automatically transparent)
                let info = ConstantInfo::new(ty.clone(), val);
                global.add_constant(*qname, info);
            }
            _ => {}
        }
    }

    Ok(data_constructors)
}
