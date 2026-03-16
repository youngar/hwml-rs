use crate::*;
use hwml_core::*;
use hwml_support::*;
use hwml_surface as surface;

/// A pattern from the surface AST, used in pattern matching compilation.
#[derive(Clone, Debug)]
pub enum Pat {
    /// Variable pattern: binds the scrutinee to a name
    Var(String),
    /// Constructor pattern: matches a specific constructor with sub-patterns
    Constructor(ConstantId<'static>, Vec<Pat>),
    /// Wildcard pattern: matches anything without binding
    Wildcard,
}

/// A single row in the pattern matrix.
/// Represents one clause from the user's match expression.
#[derive(Clone, Debug)]
pub struct Clause {
    /// The patterns for this clause (one per scrutinee)
    pub patterns: Vec<Pat>,
    /// The body expression to evaluate if this clause matches
    pub body: Box<surface::Expression>,
}

/// The pattern matrix: a collection of clauses being compiled.
#[derive(Clone, Debug)]
pub struct Matrix {
    /// The rows of the matrix
    pub rows: Vec<Clause>,
}

impl Matrix {
    /// Create a new empty matrix
    pub fn new() -> Self {
        Matrix { rows: Vec::new() }
    }

    /// Check if the first row consists only of variables and wildcards
    pub fn is_pure_variable_row(&self, row_idx: usize) -> bool {
        if row_idx >= self.rows.len() {
            return false;
        }
        self.rows[row_idx]
            .patterns
            .iter()
            .all(|p| matches!(p, Pat::Var(_) | Pat::Wildcard))
    }
}

/// Elaborate a match expression into a case tree with transport.
/// This is the main entry point for pattern matching elaboration.
#[async_recursion::async_recursion(?Send)]
async fn check_match<'db, 'g>(
    ctx: &mut ElaborationContext<'db, 'g>,
    match_expr: &surface::Match,
    expected_ty: RcValue<'db>,
) -> TrustedSyntax<'db> {
    let loc = ctx.expr_location(&surface::Expression::Match(match_expr.clone()));

    // Step 1: Infer the scrutinee and bind it to a rigid variable
    let scrutinee_result = synth(ctx, &match_expr.scrutinee).await;
    let scrutinee_term = Trusted(scrutinee_result.subject.clone());
    let scrutinee_ty = scrutinee_result.ty.clone();

    // Generate a fresh name for the scrutinee variable
    let scrutinee_var_name = ctx.fresh_var_name("scrut", 0);

    // Step 2: Generate the equality proof variable name
    let proof_var_name = ctx.fresh_var_name("p_eq", 0);

    // Step 3: Synthesize the motive
    let motive = match ctx.synthesize_motive(&expected_ty, &scrutinee_term) {
        Ok(m) => m,
        Err(e) => {
            return ctx.error(
                loc,
                format!("Failed to synthesize motive: {}", e),
                expected_ty,
            );
        }
    };

    // Step 4: Build the pattern matrix from the surface clauses
    let mut matrix_rows = Vec::new();
    for clause in &match_expr.clauses {
        // Parse the pattern
        let pattern = match ctx.parse_pattern(&clause.pattern) {
            Ok(p) => p,
            Err(e) => {
                ctx.diagnostics.push(Diagnostic {
                    location: loc,
                    message: format!("Invalid pattern: {}", e),
                    expected_type: None,
                });
                continue;
            }
        };

        matrix_rows.push(Clause {
            patterns: vec![pattern],
            body: clause.body.clone(),
        });
    }

    let matrix = Matrix { rows: matrix_rows };

    // Step 5: Push the scrutinee binding
    ctx.push_binding(scrutinee_var_name.clone(), scrutinee_ty.clone());
    let scrutinee_var = Syntax::variable_rc(Index::from(0));

    // Step 6: Push the proof binding (p : Eq scrutinee_ty scrutinee scrutinee = refl)
    // For now, we create a simple proof type
    let proof_ty_syntax_rc = Syntax::eq_rc(
        type_quote(ctx.solver.tc_env.values.global, ctx.depth(), &scrutinee_ty)
            .unwrap_or_else(|_| Syntax::universe_rc(UniverseLevel::new(0))),
        scrutinee_term.view().clone().into(),
        scrutinee_var.clone(),
    );
    let proof_ty = Trusted(proof_ty_syntax_rc.clone());
    let proof_ty_val = ctx
        .eval(&proof_ty)
        .unwrap_or_else(|_| Rc::new(Value::universe(UniverseLevel::new(0))));
    ctx.push_binding(proof_var_name.clone(), proof_ty_val);

    // Step 7: Run the pattern matrix compiler
    let decision_tree = match compile_matrix(
        ctx,
        vec![scrutinee_var.clone()],
        matrix,
        &motive,
        &proof_var_name,
        &expected_ty,
    )
    .await
    {
        Ok(tree) => tree,
        Err(e) => {
            ctx.pop_binding(); // Pop proof
            ctx.pop_binding(); // Pop scrutinee
            return ctx.error(
                loc,
                format!("Pattern compilation failed: {}", e),
                expected_ty,
            );
        }
    };

    // Pop the bindings
    ctx.pop_binding(); // Pop proof
    ctx.pop_binding(); // Pop scrutinee

    // Step 8: Wrap in let bindings for the scrutinee and proof
    // let p = refl in decision_tree
    let refl_proof = Trusted(Syntax::refl_rc());
    let with_proof = crate::rules::form_let(Trusted(proof_ty_syntax_rc), refl_proof, decision_tree);

    // let scrut = scrutinee_term in with_proof
    let scrutinee_ty_syntax =
        type_quote(ctx.solver.tc_env.values.global, ctx.depth(), &scrutinee_ty)
            .unwrap_or_else(|_| Syntax::universe_rc(UniverseLevel::new(0)));
    crate::rules::form_let(Trusted(scrutinee_ty_syntax), scrutinee_term, with_proof)
}

/// Group matrix rows by their outer constructor in the first column.
/// Returns a list of (constructor, arity, specialized_matrix) tuples.
fn group_by_constructor<'db, 'g>(
    ctx: &ElaborationContext<'db, 'g>,
    matrix: &Matrix,
) -> Result<Vec<(ConstantId<'db>, usize, Matrix)>, String> {
    let mut groups: HashMap<String, Vec<Clause>> = HashMap::new();

    for clause in &matrix.rows {
        if clause.patterns.is_empty() {
            continue;
        }

        match &clause.patterns[0] {
            Pat::Constructor(ctor_id, sub_pats) => {
                let ctor_name = ctor_id.name(ctx.solver.tc_env.db).to_string();

                // Specialize this row: replace the constructor pattern with its sub-patterns
                let mut new_patterns = sub_pats.clone();
                new_patterns.extend_from_slice(&clause.patterns[1..]);

                let specialized_clause = Clause {
                    patterns: new_patterns,
                    body: clause.body.clone(),
                };

                groups
                    .entry(ctor_name)
                    .or_insert_with(Vec::new)
                    .push(specialized_clause);
            }
            Pat::Var(_) | Pat::Wildcard => {
                // Variable/wildcard patterns match all constructors
                // We need to handle this by duplicating the row for each constructor
                // For now, we'll skip this and handle it in a more complete implementation
                return Err(
                    "Variable/wildcard patterns in non-final position not yet supported"
                        .to_string(),
                );
            }
        }
    }

    // Convert groups to the result format
    let mut result = Vec::new();
    for (ctor_name, clauses) in groups {
        let ctor_id: ConstantId<'db> = ConstantId::from_with_db(ctx.solver.tc_env.db, &ctor_name);
        let arity = ctx.get_constructor_arity(ctor_id)?;
        let specialized_matrix = Matrix { rows: clauses };
        result.push((ctor_id, arity, specialized_matrix));
    }

    Ok(result)
}

/// The core pattern matrix compilation algorithm.
/// Recursively compiles a pattern matrix into a case tree.
#[async_recursion::async_recursion(?Send)]
async fn compile_matrix<'db, 'g>(
    ctx: &mut ElaborationContext<'db, 'g>,
    scrutinees: Vec<Rc<Syntax<'db>>>,
    matrix: Matrix,
    motive: &Closure<'db>,
    proof_var_name: &str,
    expected_ty: &RcValue<'db>,
) -> Result<TrustedSyntax<'db>, String> {
    // BASE CASE 1: Empty matrix (inexhaustive match)
    if matrix.rows.is_empty() {
        let loc = Location::UNKNOWN;
        ctx.diagnostics.push(Diagnostic {
            location: loc,
            message: "Inexhaustive pattern match".to_string(),
            expected_type: None,
        });
        return Ok(ctx.fresh_poisoned_meta(expected_ty.clone(), loc));
    }

    // BASE CASE 2: Pure variable row (all patterns are variables/wildcards)
    if matrix.is_pure_variable_row(0) {
        let winning_clause = &matrix.rows[0];

        // Bind the pattern variables to the scrutinees
        for (pat, _scrutinee_term) in winning_clause.patterns.iter().zip(scrutinees.iter()) {
            if let Pat::Var(name) = pat {
                // Get the type of the scrutinee
                // For now, we'll use a placeholder type
                // TODO: Track scrutinee types properly
                let scrutinee_ty = Rc::new(Value::universe(UniverseLevel::new(0)));

                ctx.push_binding(name.clone(), scrutinee_ty);
            }
        }

        // Elaborate the body
        let core_body = check(ctx, &winning_clause.body, expected_ty.clone()).await;

        // Pop the bindings
        let var_count = winning_clause
            .patterns
            .iter()
            .filter(|p| matches!(p, Pat::Var(_)))
            .count();
        for _ in 0..var_count {
            ctx.pop_binding();
        }

        // Wrap in transport
        let _loc = Location::UNKNOWN;
        let proof_var = Trusted(Syntax::variable_rc(Index::from(
            ctx.lookup_var(proof_var_name).unwrap_or(0),
        )));

        return Ok(crate::rules::form_transport(
            motive.clone(),
            proof_var,
            core_body,
        ));
    }

    // INDUCTIVE CASE: Split on the first scrutinee
    if scrutinees.is_empty() {
        return Err("No scrutinees left to split on".to_string());
    }

    let current_scrutinee = &scrutinees[0];
    let remaining_scrutinees = &scrutinees[1..];

    // Group rows by constructor
    let groups = group_by_constructor(ctx, &matrix)?;

    let mut core_branches = Vec::new();

    for (ctor_id, arity, specialized_matrix) in groups {
        // Generate fresh variables for the constructor arguments
        let mut fresh_vars = Vec::new();
        for i in 0..arity {
            let var_name = ctx.fresh_var_name("arg", i);
            let var_ty = Rc::new(Value::universe(UniverseLevel::new(0))); // TODO: Get actual type
            ctx.push_binding(var_name.clone(), var_ty);

            let var_index = Index::from(0); // Most recently bound
            fresh_vars.push(Syntax::variable_rc(var_index));
        }

        // Build the new scrutinee list: [fresh_vars..., remaining_scrutinees...]
        let mut next_scrutinees = fresh_vars.clone();
        next_scrutinees.extend_from_slice(remaining_scrutinees);

        // Recurse
        let branch_body = compile_matrix(
            ctx,
            next_scrutinees,
            specialized_matrix,
            motive,
            proof_var_name,
            expected_ty,
        )
        .await?;

        // Pop the fresh variable bindings
        for _ in 0..arity {
            ctx.pop_binding();
        }

        // Create the case branch - need to extract the Rc<Syntax> from TrustedSyntax
        core_branches.push(CaseBranch::new(
            ctor_id,
            DynBinding::new(arity, branch_body.as_inner().clone()),
        ));
    }

    // Build the case expression
    // The scrutinee must be a variable, so extract its index
    let scrutinee_var = match current_scrutinee.as_ref() {
        Syntax::Variable(var) => var.clone(),
        _ => return Err("Scrutinee must be a variable in core case expression".to_string()),
    };

    let _loc = Location::UNKNOWN;
    Ok(Trusted(Syntax::case_rc(scrutinee_var.index, core_branches)))
}

/// Parse a surface expression as a pattern
fn parse_pattern(&self, expr: &surface::Expression) -> Result<Pat, String> {
    use surface::Expression;
    match expr {
        // Variable pattern: any identifier
        Expression::Id(id) => {
            let name = std::str::from_utf8(&id.value)
                .map_err(|_| "Invalid UTF-8 in pattern variable")?
                .to_string();

            // Check if this is a constructor (starts with @) or a variable
            if name.starts_with('@') {
                // Constructor with no arguments
                // SAFETY: We're creating a ConstantId with 'static lifetime because
                // patterns need to outlive the elaboration context. The string is
                // interned in the database which has a 'static lifetime.
                let ctor_id: ConstantId<'static> = unsafe {
                    std::mem::transmute(ConstantId::from_with_db(self.solver.tc_env.db, &name[1..]))
                };
                Ok(Pat::Constructor(ctor_id, Vec::new()))
            } else {
                Ok(Pat::Var(name))
            }
        }
        // Wildcard pattern
        Expression::Underscore(_) => Ok(Pat::Wildcard),
        // Constructor application: @Cons x xs
        Expression::App(app) => {
            if app.elements.is_empty() {
                return Err("Empty application in pattern".to_string());
            }

            // First element should be a constructor
            let ctor_pat = self.parse_pattern(&app.elements[0])?;
            match ctor_pat {
                Pat::Constructor(ctor_id, inner_pats) => {
                    if !inner_pats.is_empty() {
                        return Err("Nested constructor in pattern head".to_string());
                    }
                    // Parse the rest as sub-patterns
                    let mut sub_pats = Vec::new();
                    for elem in &app.elements[1..] {
                        sub_pats.push(self.parse_pattern(elem)?);
                    }
                    Ok(Pat::Constructor(ctor_id, sub_pats))
                }
                _ => Err("Pattern application must start with a constructor".to_string()),
            }
        }
        Expression::Paren(paren) => self.parse_pattern(&paren.expr),
        _ => Err(format!("Invalid pattern: {:?}", expr)),
    }
}

/// Synthesize a motive for pattern matching by abstracting the expected type
/// over the scrutinee variable.
///
/// Given an expected type and a scrutinee term, this creates a closure
/// that abstracts over the scrutinee: λz. expected_type[scrutinee := z]
fn synthesize_motive<'db>(
    ctx: &ElaborationContext,
    expected_ty: &RcValue<'db>,
    _scrutinee: &TrustedSyntax<'db>,
) -> Result<Closure<'db>, String> {
    // Quote the expected type to syntax
    let expected_ty_syntax =
        type_quote(self.solver.tc_env.values.global, self.depth(), expected_ty)
            .map_err(|e| format!("Failed to quote expected type: {:?}", e))?;

    // For now, we create a simple closure that just returns the expected type
    // TODO: In a full implementation, we would need to:
    // 1. Identify occurrences of the scrutinee in the expected type
    // 2. Replace them with variable 0 (the bound variable in the closure)
    // 3. Properly handle dependent types
    //
    // For simple cases where the expected type doesn't depend on the scrutinee,
    // this is sufficient: λz. expected_ty
    Ok(Closure::new(
        hwml_core::val::LocalEnv::new(),
        expected_ty_syntax,
    ))
}
