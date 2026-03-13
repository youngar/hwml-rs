//! End-to-end elaboration pipeline from surface syntax to core IR.

use hwml_core::check::TCEnvironment;
use hwml_core::syn::Syntax;
use hwml_core::val::{Environment, GlobalEnv};
use hwml_support::SourceFile;
use hwml_surface::syntax as surface;
use std::rc::Rc;

use crate::elaborator::{check, synth, Diagnostic, ElaborationContext};
use crate::engine::{SingleThreadedExecutor, SolverEnvironment};
use crate::zonk::zonk;

pub struct ElaborationResult<'db> {
    pub term: Option<Rc<Syntax<'db>>>,
    pub diagnostics: Vec<Diagnostic>,
}

pub fn elaborate_expression<'db>(
    db: &'db dyn salsa::Database,
    source_file: SourceFile,
    expr: &surface::Expression,
) -> ElaborationResult<'db> {
    let global_env = GlobalEnv::new();
    let executor = SingleThreadedExecutor::new();
    let spawner = executor.spawner();

    let tc_env = TCEnvironment {
        db,
        values: Environment::new(&global_env),
        types: Vec::new(),
    };

    let solver = SolverEnvironment::new(tc_env, spawner);
    let mut ctx = ElaborationContext::new(db, Some(source_file), solver);

    let (term, _ty) = futures::executor::block_on(async { synth(&mut ctx, expr).await });

    ElaborationResult {
        term: Some(term.into_inner()),
        diagnostics: ctx.diagnostics().to_vec(),
    }
}

pub fn elaborate_program<'db>(
    db: &'db dyn salsa::Database,
    source_file: SourceFile,
    program: &surface::Program,
) -> Vec<ElaborationResult<'db>> {
    eprintln!(
        "[Pipeline] Elaborating program with {} statements",
        program.statements.len()
    );

    // First pass: collect all primitive declarations and build a shared context
    let global_env = GlobalEnv::new();
    let executor = SingleThreadedExecutor::new();
    let spawner = executor.spawner();

    let tc_env = TCEnvironment {
        db,
        values: hwml_core::val::Environment::new(&global_env),
        types: Vec::new(),
    };

    let solver = SolverEnvironment::new(tc_env, spawner.clone());
    let mut shared_ctx = ElaborationContext::new(db, Some(source_file), solver);

    // Process primitive declarations first
    for statement in &program.statements {
        if let surface::Statement::Prim(prim) = statement {
            eprintln!("[Pipeline] Processing primitive declaration");
            elaborate_prim_declaration(&mut shared_ctx, prim);
        }
    }

    // Second pass: elaborate all statements with primitives available
    program
        .statements
        .iter()
        .map(|statement| {
            eprintln!("[Pipeline] Processing statement: {:?}", statement);
            match statement {
                surface::Statement::Def(def) => {
                    eprintln!(
                        "[Pipeline] Def with {} binding groups",
                        def.bindings.groups.len()
                    );
                    elaborate_def_with_context(db, source_file, def, &shared_ctx)
                }
                surface::Statement::Meta(meta) => {
                    elaborate_meta_with_context(db, source_file, meta, &shared_ctx)
                }
                surface::Statement::Prim(_) => {
                    // Primitives were already processed in the first pass
                    ElaborationResult {
                        term: None,
                        diagnostics: Vec::new(),
                    }
                }
            }
        })
        .collect()
}

fn elaborate_def<'db>(
    db: &'db dyn salsa::Database,
    source_file: SourceFile,
    def: &surface::Def,
) -> ElaborationResult<'db> {
    // Desugar def with bindings and type annotation into a lambda with type checking.
    // For `def id (x : Bit) : Bit := x`, we want to:
    // 1. Build the expected type `Bit -> Bit` from bindings and return type
    // 2. Build the lambda `fun x => x` from bindings and body
    // 3. Check the lambda against the expected type

    eprintln!("[Pipeline] Elaborating def");
    let value_expr = desugar_bindings(&def.bindings, &def.value, &def.id.loc);
    eprintln!("[Pipeline] Desugared value: {:?}", value_expr);

    if let Some(ref return_ty) = def.ty {
        eprintln!("[Pipeline] Has return type annotation");
        // Build the expected type from bindings and return type
        let expected_ty_expr = build_pi_type(&def.bindings, return_ty, &def.id.loc);
        eprintln!("[Pipeline] Built Pi type: {:?}", expected_ty_expr);

        // Elaborate the expected type first to get a Value
        let global_env = GlobalEnv::new();
        let executor = SingleThreadedExecutor::new();
        let spawner = executor.spawner();

        let tc_env = TCEnvironment {
            db,
            values: Environment::new(&global_env),
            types: Vec::new(),
        };

        let solver = SolverEnvironment::new(tc_env, spawner.clone());
        let mut ctx = ElaborationContext::new(db, Some(source_file), solver);

        eprintln!("[Pipeline] Checking type against universe");
        // Check the type against a universe (Pi types need to be checked, not synthesized)
        let universe_ty = std::rc::Rc::new(hwml_core::val::Value::universe(
            hwml_core::common::UniverseLevel::new(0),
        ));
        let ty_term = futures::executor::block_on(async {
            check(&mut ctx, &expected_ty_expr, universe_ty).await
        });
        eprintln!("[Pipeline] Type checked");

        // Evaluate the type to get a Value
        let ty_value = hwml_core::eval::eval(&mut ctx.solver.tc_env.values, ty_term.as_inner())
            .unwrap_or_else(|e| {
                eprintln!("Failed to evaluate type: {}", e);
                std::rc::Rc::new(hwml_core::val::Value::universe(
                    hwml_core::common::UniverseLevel::new(0),
                ))
            });

        // Now check the value against the type
        let term =
            futures::executor::block_on(async { check(&mut ctx, &value_expr, ty_value).await });

        ElaborationResult {
            term: Some(term.into_inner()),
            diagnostics: ctx.diagnostics().to_vec(),
        }
    } else {
        // No type annotation, just synthesize
        elaborate_expression(db, source_file, &value_expr)
    }
}

fn elaborate_meta<'db>(
    db: &'db dyn salsa::Database,
    source_file: SourceFile,
    meta: &surface::Meta,
) -> ElaborationResult<'db> {
    let value_expr = desugar_bindings(&meta.bindings, &meta.value, &meta.id.loc);
    elaborate_expression(db, source_file, &value_expr)
}

// Convert typed bindings (x : Bit) into untyped bindings x for lambdas
fn desugar_bindings(
    bindings: &surface::Bindings,
    body: &surface::Expression,
    loc: &std::ops::Range<usize>,
) -> surface::Expression {
    let mut expr = body.clone();

    // Wrap the body in lambdas for each binding group (right to left)
    for group in bindings.groups.iter().rev() {
        let untyped_group = match group {
            surface::BindingGroup::Typed(typed) => {
                // Convert typed bindings to untyped
                // For now, just take the first binder (we'll handle multiple binders later)
                if let Some(first_binder) = typed.binders.first() {
                    surface::BindingGroup::Untyped(surface::UntypedBindingGroup::new(
                        first_binder.clone(),
                    ))
                } else {
                    continue;
                }
            }
            surface::BindingGroup::Untyped(untyped) => {
                surface::BindingGroup::Untyped(untyped.clone())
            }
        };

        expr = surface::Expression::Fun(surface::Fun::new(
            loc.clone(),
            surface::Bindings::new(vec![untyped_group]),
            Box::new(expr),
        ));
    }

    expr
}

// Build a Pi type from bindings and a return type
// For (x : Bit) with return type Bit, build Bit -> Bit
fn build_pi_type(
    bindings: &surface::Bindings,
    return_ty: &surface::Expression,
    loc: &std::ops::Range<usize>,
) -> surface::Expression {
    let mut ty = return_ty.clone();

    // Build Pi types for each binding group (right to left)
    for group in bindings.groups.iter().rev() {
        match group {
            surface::BindingGroup::Typed(typed) => {
                // Build a Pi type
                ty = surface::Expression::Pi(surface::Pi::new(
                    loc.clone(),
                    surface::TypedBindings::new(vec![typed.clone()]),
                    Box::new(ty),
                ));
            }
            surface::BindingGroup::Untyped(_) => {
                // Can't build a Pi type without type annotations
                // This is an error, but we'll let the elaborator handle it
            }
        }
    }

    ty
}

// Process a primitive declaration and register it in the context
fn elaborate_prim_declaration<'db, 'g>(
    ctx: &mut ElaborationContext<'db, 'g>,
    prim: &surface::Prim,
) {
    let name = std::str::from_utf8(&prim.id.value).unwrap_or("<invalid utf8>");
    eprintln!("[Pipeline] Registering primitive: {}", name);

    // Elaborate the type expression
    let (ty_term, _ty_ty) = futures::executor::block_on(async { synth(ctx, &prim.ty).await });

    // Evaluate the type to get a Value
    match ctx.eval(&ty_term) {
        Ok(ty_value) => {
            // Create the appropriate core term and type based on the primitive name.
            // For hardware types declared with Signal as their type, we automatically
            // lift them to the meta-level so they can be used in Pi types.
            let loc = ctx.convert_location(&prim.id.loc);
            let (term, actual_ty) = match name {
                "Bit" => {
                    // Bit : Signal, but we lift it to ^Bit : Universe(0) for use in Pi types
                    let bit_term = Syntax::bit_rc();
                    let lifted_bit = Syntax::lift_rc(bit_term);
                    let ty = std::rc::Rc::new(hwml_core::val::Value::universe(
                        hwml_core::common::UniverseLevel::new(0),
                    ));
                    (lifted_bit, ty)
                }
                "Signal" => {
                    let term = Syntax::signal_universe_rc();
                    let ty = std::rc::Rc::new(hwml_core::val::Value::universe(
                        hwml_core::common::UniverseLevel::new(0),
                    ));
                    (term, ty)
                }
                _ => {
                    // For unknown primitives, create a placeholder
                    // In a real implementation, this would be an error
                    eprintln!("[Pipeline] Warning: unknown primitive {}", name);
                    let term = Syntax::bit_rc();
                    (term, ty_value)
                }
            };

            ctx.register_primitive(
                name.to_string(),
                crate::elaborator::PrimitiveInfo {
                    ty: actual_ty,
                    term,
                },
            );
        }
        Err(e) => {
            eprintln!("[Pipeline] Failed to evaluate primitive type: {:?}", e);
        }
    }
}

// Elaborate a def statement with access to a shared context containing primitives
fn elaborate_def_with_context<'db>(
    db: &'db dyn salsa::Database,
    source_file: SourceFile,
    def: &surface::Def,
    shared_ctx: &ElaborationContext<'db, '_>,
) -> ElaborationResult<'db> {
    eprintln!("[Pipeline] Elaborating def");
    let value_expr = desugar_bindings(&def.bindings, &def.value, &def.id.loc);
    eprintln!("[Pipeline] Desugared value: {:?}", value_expr);

    if let Some(ref return_ty) = def.ty {
        eprintln!("[Pipeline] Has return type annotation");
        let expected_ty_expr = build_pi_type(&def.bindings, return_ty, &def.id.loc);
        eprintln!("[Pipeline] Built Pi type: {:?}", expected_ty_expr);

        // Create a new context with primitives copied from shared context
        let global_env = GlobalEnv::new();
        let executor = SingleThreadedExecutor::new();
        let spawner = executor.spawner();

        let tc_env = TCEnvironment {
            db,
            values: Environment::new(&global_env),
            types: Vec::new(),
        };

        let solver = SolverEnvironment::new(tc_env, spawner.clone());
        let mut ctx = ElaborationContext::new(db, Some(source_file), solver);

        // Copy primitives from shared context
        for (name, info) in shared_ctx.primitives() {
            ctx.register_primitive(name.clone(), info.clone());
        }

        eprintln!("[Pipeline] Checking type against universe");
        let universe_ty = std::rc::Rc::new(hwml_core::val::Value::universe(
            hwml_core::common::UniverseLevel::new(0),
        ));
        let ty_term = futures::executor::block_on(async {
            check(&mut ctx, &expected_ty_expr, universe_ty).await
        });
        eprintln!("[Pipeline] Type checked");

        match ctx.eval(&ty_term) {
            Ok(ty_value) => {
                eprintln!("[Pipeline] Checking value against type");
                let value_term = futures::executor::block_on(async {
                    check(&mut ctx, &value_expr, ty_value).await
                });

                let zonked_term = zonk(&*ctx.solver.state.borrow(), value_term.as_inner());

                ElaborationResult {
                    term: Some(zonked_term),
                    diagnostics: ctx.take_diagnostics(),
                }
            }
            Err(e) => {
                eprintln!("[Pipeline] Failed to evaluate type: {:?}", e);
                ctx.report_solver_error(format!("Failed to evaluate type: {:?}", e));
                ElaborationResult {
                    term: None,
                    diagnostics: ctx.take_diagnostics(),
                }
            }
        }
    } else {
        eprintln!("[Pipeline] No return type annotation, synthesizing");

        let global_env = GlobalEnv::new();
        let executor = SingleThreadedExecutor::new();
        let spawner = executor.spawner();

        let tc_env = TCEnvironment {
            db,
            values: Environment::new(&global_env),
            types: Vec::new(),
        };

        let solver = SolverEnvironment::new(tc_env, spawner);
        let mut ctx = ElaborationContext::new(db, Some(source_file), solver);

        // Copy primitives from shared context
        for (name, info) in shared_ctx.primitives() {
            ctx.register_primitive(name.clone(), info.clone());
        }

        let (term, _ty) = futures::executor::block_on(async { synth(&mut ctx, &value_expr).await });

        let zonked_term = zonk(&*ctx.solver.state.borrow(), term.as_inner());

        ElaborationResult {
            term: Some(zonked_term),
            diagnostics: ctx.take_diagnostics(),
        }
    }
}

// Elaborate a meta statement with access to a shared context containing primitives
fn elaborate_meta_with_context<'db>(
    db: &'db dyn salsa::Database,
    source_file: SourceFile,
    meta: &surface::Meta,
    shared_ctx: &ElaborationContext<'db, '_>,
) -> ElaborationResult<'db> {
    let global_env = GlobalEnv::new();
    let executor = SingleThreadedExecutor::new();
    let spawner = executor.spawner();

    let tc_env = TCEnvironment {
        db,
        values: Environment::new(&global_env),
        types: Vec::new(),
    };

    let solver = SolverEnvironment::new(tc_env, spawner);
    let mut ctx = ElaborationContext::new(db, Some(source_file), solver);

    // Copy primitives from shared context
    for (name, info) in shared_ctx.primitives() {
        ctx.register_primitive(name.clone(), info.clone());
    }

    let (term, _ty) = futures::executor::block_on(async { synth(&mut ctx, &meta.value).await });

    let zonked_term = zonk(&*ctx.solver.state.borrow(), term.as_inner());

    ElaborationResult {
        term: Some(zonked_term),
        diagnostics: ctx.take_diagnostics(),
    }
}
