use crate::*;

use anyhow::Result;
use hwml_core::common::*;
use hwml_core::declaration as decl;
use hwml_core::syn as core;
use hwml_surface::syntax as surface;

pub fn infer_app<'db>(
    db: &'db dyn salsa::Database,
    state: &mut State<'db>,
    app: surface::App,
) -> Result<(core::RcSyntax<'db>, core::RcSyntax<'db>)> {
    assert!(app.elements.len() >= 1);
    // Get the elaborated head of the term.
    let (mut fun_etm, mut fun_ety) = infer_type(db, state, *app.elements[0].clone())?;

    for arg in &app.elements[1..] {
        let domain = state.fresh_metavariable();
        state.extend_context_nameless(domain.clone());
        let codomain = state.fresh_metavariable();
        state.pop_context();
        let pi = core::Syntax::pi_rc(domain.clone(), codomain.clone());

        state.equality_constraint(
            fun_ety.clone(),
            pi.clone(),
            core::Syntax::universe_rc(UniverseLevel::new(0)),
        );

        // Check the type of the operand has the type of the domain.
        let arg_etm = check_type(db, state, *arg.clone(), domain.clone())?;

        // Create the core application
        let app_etm = core::Syntax::application_rc(fun_etm, arg_etm.clone());

        // Handoff for the next loop.
        fun_etm = app_etm;
        fun_ety = subst(codomain, Index::new(0), arg_etm);
    }
    // Wrap the operator in an annotation node.
    let eapp = core::Syntax::check_rc(fun_etm, fun_ety.clone());

    Ok((eapp, fun_ety))
}

pub fn infer_fun<'db>(
    db: &'db dyn salsa::Database,
    state: &mut State<'db>,
    fun: surface::Fun,
) -> Result<(core::RcSyntax<'db>, core::RcSyntax<'db>)> {
    let depth = state.depth();
    // let mut types = Vec::new();
    // for group in fun.bindings.groups {
    //     let ety = elab_type(state, *group.ty)?;
    //     for binder in group.binders {
    //         // TODO: we only support simple expressions here.
    //         let surface::Expression::Id(id) = *binder else {
    //             return Err(anyhow::anyhow!("unsupported binder"));
    //         };
    //         state.extend_context(id.value, ety.clone());
    //         types.push(ety.clone());
    //     }
    // }

    // Infer the type of the body under the extended context.
    let (body, codomain) = infer_type(db, state, *fun.expr)?;

    // Reset the context.
    state.truncate_context(depth);

    // Build the lambda.
    let etm = core::Syntax::lambda_rc(body);

    // Build the type of the lambda.
    let mut ety = codomain;
    // for ty in types.iter().rev() {
    //     ety = core::Syntax::pi_rc(ty.clone(), ety);
    // }
    Ok((etm, ety))
}

pub fn infer_paren<'db>(
    db: &'db dyn salsa::Database,
    state: &mut State<'db>,
    paren: surface::Paren,
) -> Result<(core::RcSyntax<'db>, core::RcSyntax<'db>)> {
    infer_type(db, state, *paren.expr)
}

pub fn infer_id<'db>(
    state: &mut State<'db>,
    id: surface::Id,
) -> Result<(core::RcSyntax<'db>, core::RcSyntax<'db>)> {
    println!("inferring id: {}", std::str::from_utf8(&id.value).unwrap());
    if *id.value == *b"Type" {
        return Ok((
            core::Syntax::universe_rc(UniverseLevel::new(0)),
            core::Syntax::universe_rc(UniverseLevel::new(1)),
        ));
    }
    if let Some(level) = state.lookup_local(&id.value) {
        let index = state.level_to_index(level);
        let ety = state.type_of(level);
        println!("found local: {:?} : {:?}", index, ety);
        return Ok((core::Syntax::variable_rc(index), ety));
    }
    todo!("global inference");
}

pub fn infer_type<'db>(
    db: &'db dyn salsa::Database,
    state: &mut State<'db>,
    term: surface::Expression,
) -> Result<(core::RcSyntax<'db>, core::RcSyntax<'db>)> {
    println!("inferring type: {:?}", term);
    match term {
        surface::Expression::Fun(fun) => infer_fun(db, state, fun),
        surface::Expression::Paren(paren) => infer_paren(db, state, paren),
        surface::Expression::Id(id) => infer_id(state, id),
        surface::Expression::Match(match_expr) => infer_match(db, state, match_expr),
        surface::Expression::Quote(quote) => infer_quote(db, state, quote),
        surface::Expression::Splice(splice) => infer_splice(db, state, splice),
        surface::Expression::Raise(raise) => infer_raise(db, state, raise),
        surface::Expression::App(app) => {
            let (etm, ety) = infer_app(db, state, app)?;
            Ok((etm, ety))
        }
        _ => todo!(),
    }
}

pub fn check_pi<'db>(
    _db: &'db dyn salsa::Database,
    _state: &mut State<'db>,
    _pi: surface::Pi,
    _ty: core::RcSyntax<'db>,
) -> Result<core::RcSyntax<'db>> {
    todo!()
}

pub fn check_arrow<'db>(
    _db: &'db dyn salsa::Database,
    _state: &mut State<'db>,
    _arrow: surface::Arrow,
    _ty: core::RcSyntax<'db>,
) -> Result<core::RcSyntax<'db>> {
    todo!()
}

pub fn check_fat_arrow<'db>(
    _db: &'db dyn salsa::Database,
    _state: &mut State<'db>,
    _fat_arrow: surface::FatArrow,
    _ty: core::RcSyntax<'db>,
) -> Result<core::RcSyntax<'db>> {
    todo!()
}

pub fn check_app<'db>(
    db: &'db dyn salsa::Database,
    state: &mut State<'db>,
    app: surface::App,
    ty: core::RcSyntax<'db>,
) -> Result<core::RcSyntax<'db>> {
    let (etm, ety) = infer_app(db, state, app)?;
    state.equality_constraint(ty, ety, core::Syntax::universe_rc(UniverseLevel::new(0)));
    Ok(etm)
}

pub fn check_fun<'db>(
    db: &'db dyn salsa::Database,
    state: &mut State<'db>,
    fun: surface::Fun,
    ty: core::RcSyntax<'db>,
) -> Result<core::RcSyntax<'db>> {
    let (etm, ety) = infer_fun(db, state, fun)?;
    state.equality_constraint(ty, ety, core::Syntax::universe_rc(UniverseLevel::new(0)));
    Ok(etm)
}

pub fn check_let_in<'db>(
    _db: &'db dyn salsa::Database,
    _state: &mut State<'db>,
    _let_in: surface::LetIn,
    _ty: core::RcSyntax<'db>,
) -> Result<core::RcSyntax<'db>> {
    todo!()
}

pub fn check_underscore<'db>(
    _db: &'db dyn salsa::Database,
    _state: &mut State<'db>,
    _underscore: surface::Underscore,
    _ty: core::RcSyntax<'db>,
) -> Result<core::RcSyntax<'db>> {
    todo!()
}

pub fn check_paren<'db>(
    db: &'db dyn salsa::Database,
    state: &mut State<'db>,
    paren: surface::Paren,
    ty: core::RcSyntax<'db>,
) -> Result<core::RcSyntax<'db>> {
    check_type(db, state, *paren.expr, ty)
}

pub fn check_num<'db>(
    _db: &'db dyn salsa::Database,
    _state: &mut State<'db>,
    _num: surface::Num,
    _ty: core::RcSyntax<'db>,
) -> Result<core::RcSyntax<'db>> {
    todo!()
}

pub fn check_str<'db>(
    _db: &'db dyn salsa::Database,
    _state: &mut State<'db>,
    _str: surface::Str,
    _ty: core::RcSyntax<'db>,
) -> Result<core::RcSyntax<'db>> {
    todo!()
}

pub fn check_id<'db>(
    db: &'db dyn salsa::Database,
    state: &mut State<'db>,
    id: surface::Id,
    ty: core::RcSyntax<'db>,
) -> Result<core::RcSyntax<'db>> {
    let (etm, ety) = infer_id(state, id)?;
    state.equality_constraint(ety, ty, core::Syntax::universe_rc(UniverseLevel::new(0)));
    Ok(etm)
}

pub fn check_type<'db>(
    db: &'db dyn salsa::Database,
    state: &mut State<'db>,
    term: surface::Expression,
    ty: core::RcSyntax<'db>,
) -> Result<core::RcSyntax<'db>> {
    match term {
        surface::Expression::Pi(pi) => check_pi(db, state, pi, ty),
        surface::Expression::Arrow(arrow) => check_arrow(db, state, arrow, ty),
        surface::Expression::FatArrow(fat_arrow) => check_fat_arrow(db, state, fat_arrow, ty),
        surface::Expression::App(app) => check_app(db, state, app, ty),
        surface::Expression::Fun(fun) => check_fun(db, state, fun, ty),
        surface::Expression::LetIn(let_in) => check_let_in(db, state, let_in, ty),
        surface::Expression::Underscore(underscore) => check_underscore(db, state, underscore, ty),
        surface::Expression::Paren(paren) => check_paren(db, state, paren, ty),
        surface::Expression::Num(num) => check_num(db, state, num, ty),
        surface::Expression::Str(str) => check_str(db, state, str, ty),
        surface::Expression::Id(id) => check_id(db, state, id, ty),
        surface::Expression::Match(match_expr) => check_match(db, state, match_expr, ty),
        surface::Expression::Quote(quote) => check_quote(db, state, quote, ty),
        surface::Expression::Splice(splice) => check_splice(db, state, splice, ty),
        surface::Expression::Raise(raise) => check_raise(db, state, raise, ty),
    }
}

pub fn elab_type<'db>(
    db: &'db dyn salsa::Database,
    state: &mut State<'db>,
    ty: surface::Expression,
) -> Result<core::RcSyntax<'db>> {
    check_type(
        db,
        state,
        ty,
        core::Syntax::universe_rc(UniverseLevel::new(0)),
    )
}

pub fn elab_def<'db>(
    db: &'db dyn salsa::Database,
    state: &mut State<'db>,
    def: surface::Def,
) -> Result<decl::Declaration<'db>> {
    let depth = state.depth();
    // A list of the elaborated types of all binders in scope.  This is used to
    // build the overall pi type of this definition.
    // let mut types = Vec::new();
    for group in def.bindings.groups {
        // Elaborate the type of the binder.
        // let ety = elab_type(state, *group.ty)?;
        // All binders in the group share the same type.
        // for binder in group.binders {
        //     // TODO: we only support simple expressions here.
        //     let surface::Expression::Id(id) = *binder else {
        //         return Err(anyhow::anyhow!("unsupported binder"));
        //     };
        //     state.extend_context(id.value, ety.clone());
        //     types.push(ety.clone());
        // }
    }
    // Elaborate the target type of the definition.
    let mut ety = match def.ty {
        Some(ty) => elab_type(db, state, *ty)?,
        None => {
            // If no type annotation is provided, we need to infer it
            // For now, we'll use a placeholder or error
            return Err(anyhow::anyhow!("type inference not yet implemented"));
        }
    };
    // Check the body of the definition.
    let mut etm = check_type(db, state, *def.value, ety.clone())?;

    // Reset the context.
    state.truncate_context(depth);

    // Build the Pi type and Lamba.
    // for ty in types.iter().rev() {
    //     ety = core::Syntax::pi_rc(ety.clone(), ty.clone());
    //     etm = core::Syntax::lambda_rc(etm);
    // }

    // TODO: !!! EXTEND CONTEXT WITH THE GLOBAL DEFINTION

    // Convert the surface ID to a string and then to a ConstantId
    let name_str = std::str::from_utf8(&def.id.value).unwrap();
    let name_id = core::ConstantId::from_str(db, name_str);

    Ok(decl::Declaration::constant(name_id, ety, etm))
}

pub fn go<'db>(
    db: &'db dyn salsa::Database,
    program: surface::Program,
) -> Result<decl::Module<'db>> {
    let mut state = State::new();

    let mut declarations = Vec::new();
    for stmt in program.statements {
        match stmt {
            surface::Statement::Def(def) => declarations.push(elab_def(db, &mut state, def)?),
            _ => {}
        }
    }

    for constraint in state.constraints {
        println!("constraint: {:?}", constraint);
    }
    Ok(decl::Module::from_declarations(declarations))
}

pub fn infer_match<'db>(
    db: &'db dyn salsa::Database,
    state: &mut State<'db>,
    match_expr: surface::Match,
) -> Result<(core::RcSyntax<'db>, core::RcSyntax<'db>)> {
    // 1. Infer the type of the scrutinee
    let (scrutinee, _scrutinee_type) = infer_type(db, state, *match_expr.scrutinee)?;

    // 2. Elaborate each clause into a case branch
    let mut branches: Vec<core::CaseBranch<'db>> = Vec::new();
    let mut result_type = None;

    for clause in match_expr.clauses {
        // For now, just infer the type of the clause body
        // In a full implementation, we would elaborate patterns properly
        let (body, body_type) = infer_type(db, state, *clause.body)?;

        // Check that all clause bodies have the same type
        match &result_type {
            None => result_type = Some(body_type),
            Some(expected_type) => {
                // In a full implementation, we would check type equality
                // For now, just use the first type
                let _ = expected_type;
            }
        }

        // Create a placeholder branch with constructor pattern
        // In a full implementation, we would elaborate the actual pattern
        let placeholder_constructor = core::ConstantId::from_str(db, "placeholder");
        branches.push(core::CaseBranch::new(placeholder_constructor, 0, body));
    }

    let result_type = result_type.unwrap_or_else(|| {
        // If no clauses, use a placeholder type
        core::Syntax::universe_rc(UniverseLevel::new(0))
    });

    // Create a case expression with the scrutinee
    //let case_expr = core::Syntax::case_rc(scrutinee, branches);
    //Ok((case_expr, result_type))
    todo!()
}

pub fn check_match<'db>(
    db: &'db dyn salsa::Database,
    state: &mut State<'db>,
    match_expr: surface::Match,
    ty: core::RcSyntax<'db>,
) -> Result<core::RcSyntax<'db>> {
    // 1. Infer the type of the scrutinee
    let (scrutinee, _scrutinee_type) = infer_type(db, state, *match_expr.scrutinee)?;

    // 2. Elaborate each clause into a case branch, checking against the expected type
    let mut branches: Vec<core::CaseBranch<'db>> = Vec::new();

    for clause in match_expr.clauses {
        // Check the clause body against the expected type
        let body = check_type(db, state, *clause.body, ty.clone())?;

        // Create a placeholder branch with constructor pattern
        // In a full implementation, we would elaborate the actual pattern
        let placeholder_constructor = core::ConstantId::from_str(db, "placeholder");
        branches.push(core::CaseBranch::new(placeholder_constructor, 0, body));
    }

    if branches.is_empty() {
        // No clauses - return a placeholder
        let meta = state.fresh_metavariable();
        Ok(meta)
    } else {
        // Create a case expression with the scrutinee
        //let case_expr = core::Syntax::case_rc(scrutinee, branches);
        //Ok(case_expr)
        todo!()
    }
}

pub fn infer_quote<'db>(
    db: &'db dyn salsa::Database,
    state: &mut State<'db>,
    quote: surface::Quote,
) -> Result<(core::RcSyntax<'db>, core::RcSyntax<'db>)> {
    // For now, we'll elaborate the inner expression as a hardware syntax term
    // In a full implementation, we would need to elaborate to HSyntax
    let (inner_term, _inner_type) = infer_type(db, state, *quote.expr)?;

    // Create a placeholder HSyntax term by splicing the inner term
    let hsyntax_term = core::HSyntax::splice_rc(inner_term);

    // Create the quote expression
    let quote_term = core::Syntax::quote_rc(hsyntax_term);

    // The type of a quote is a hardware arrow type (placeholder for now)
    // In a full implementation, this would be the proper hardware type
    let quote_type = state.fresh_metavariable();

    Ok((quote_term, quote_type))
}

pub fn check_quote<'db>(
    db: &'db dyn salsa::Database,
    state: &mut State<'db>,
    quote: surface::Quote,
    ty: core::RcSyntax<'db>,
) -> Result<core::RcSyntax<'db>> {
    let (etm, ety) = infer_quote(db, state, quote)?;
    state.equality_constraint(ty, ety, core::Syntax::universe_rc(UniverseLevel::new(0)));
    Ok(etm)
}

pub fn infer_splice<'db>(
    db: &'db dyn salsa::Database,
    state: &mut State<'db>,
    splice: surface::Splice,
) -> Result<(core::RcSyntax<'db>, core::RcSyntax<'db>)> {
    // Splice should only appear within quoted contexts
    // For now, we'll elaborate the inner expression and create a splice
    let (inner_term, inner_type) = infer_type(db, state, *splice.expr)?;

    // Create a splice HSyntax term
    let splice_hsyntax = core::HSyntax::splice_rc(inner_term);

    // For now, we'll wrap it in a quote to make it a regular syntax term
    // In a full implementation, this would be handled differently in quoted contexts
    let splice_term = core::Syntax::quote_rc(splice_hsyntax);

    Ok((splice_term, inner_type))
}

pub fn check_splice<'db>(
    db: &'db dyn salsa::Database,
    state: &mut State<'db>,
    splice: surface::Splice,
    ty: core::RcSyntax<'db>,
) -> Result<core::RcSyntax<'db>> {
    let (etm, ety) = infer_splice(db, state, splice)?;
    state.equality_constraint(ty, ety, core::Syntax::universe_rc(UniverseLevel::new(0)));
    Ok(etm)
}

pub fn infer_raise<'db>(
    db: &'db dyn salsa::Database,
    state: &mut State<'db>,
    raise: surface::Raise,
) -> Result<(core::RcSyntax<'db>, core::RcSyntax<'db>)> {
    // Raise (lift) takes a term and lifts it to the next stage
    let (inner_term, inner_type) = infer_type(db, state, *raise.expr)?;

    // Create a lift expression
    let lift_term = core::Syntax::lift_rc(inner_term);

    // The type of a lifted term is also lifted
    let lift_type = core::Syntax::lift_rc(inner_type);

    Ok((lift_term, lift_type))
}

pub fn check_raise<'db>(
    db: &'db dyn salsa::Database,
    state: &mut State<'db>,
    raise: surface::Raise,
    ty: core::RcSyntax<'db>,
) -> Result<core::RcSyntax<'db>> {
    let (etm, ety) = infer_raise(db, state, raise)?;
    state.equality_constraint(ty, ety, core::Syntax::universe_rc(UniverseLevel::new(0)));
    Ok(etm)
}
