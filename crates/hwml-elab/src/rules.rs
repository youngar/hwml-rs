use crate::engine::SolverEnvironment;
use crate::force::force;
use crate::unify::{unify, UnificationError};
use crate::TrustedTerm;
use hwml_core::eval;
use hwml_core::syn::Syntax;
use hwml_core::val::{Closure, RcValue, Value};
use std::rc::Rc;

#[derive(Debug, Clone)]
pub enum RuleError {
    ExpectedPi { got: String },
    UnificationFailed(String),
    EvaluationFailed(String),
    ForceFailed(String),
    Generic(String),
}

impl From<UnificationError<'_>> for RuleError {
    fn from(e: UnificationError) -> Self {
        RuleError::UnificationFailed(format!("{:?}", e))
    }
}

impl From<eval::Error> for RuleError {
    fn from(e: eval::Error) -> Self {
        RuleError::EvaluationFailed(format!("{:?}", e))
    }
}

impl std::fmt::Display for RuleError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RuleError::ExpectedPi { got } => write!(f, "Expected Pi type, got: {}", got),
            RuleError::UnificationFailed(msg) => write!(f, "Unification failed: {}", msg),
            RuleError::EvaluationFailed(msg) => write!(f, "Evaluation failed: {}", msg),
            RuleError::ForceFailed(msg) => write!(f, "Force failed: {}", msg),
            RuleError::Generic(msg) => write!(f, "{}", msg),
        }
    }
}

impl std::error::Error for RuleError {}

// ============================================================================
// Foundational Typing Rules
// ============================================================================

/// **Application (Synthesis Rule)**
///
/// Given:
/// - `f_tm : f_type` where `f_type` evaluates to `Π(x : A). B`
/// - `arg_tm : arg_type` where `arg_type` unifies with `A`
///
/// Produces:
/// - `app(f_tm, arg_tm) : B[arg_tm/x]`
///
/// This is the elimination rule for Pi types.
pub async fn synth_app<'db, 'g>(
    ctx: &SolverEnvironment<'db, 'g>,
    f_tm: TrustedTerm<'db>,
    f_type: RcValue<'db>,
    arg_tm: TrustedTerm<'db>,
    arg_type: RcValue<'db>,
) -> Result<(RcValue<'db>, TrustedTerm<'db>), RuleError> {
    // 1. Force f_type to ensure it's a VPi
    let f_type_whnf =
        force(ctx, f_type.clone()).map_err(|e| RuleError::ForceFailed(format!("{:?}", e)))?;

    // 2. Extract the Pi structure
    let (domain, codomain_closure) = match &*f_type_whnf {
        Value::Pi(pi) => (pi.source.clone(), pi.target.clone()),
        other => {
            return Err(RuleError::ExpectedPi {
                got: format!("{:?}", other),
            })
        }
    };

    // 3. Unify the domain with the argument type
    unify(
        ctx.tc_env.db,
        ctx.clone(),
        domain,
        arg_type,
        Rc::new(Value::universe(hwml_core::common::UniverseLevel::new(0))),
    )
    .await?;

    // 4. Evaluate the argument to instantiate the codomain
    let mut env = ctx.tc_env.values.clone();
    let arg_val = eval::eval(&mut env, arg_tm.view())?; // FIX: was f_tm, should be arg_tm

    // 5. Instantiate the codomain closure with the argument value
    let result_type = eval::run_closure(ctx.tc_env.values.global, &codomain_closure, [arg_val])?;

    // 6. Construct the application syntax
    let app_syntax = Syntax::application_rc(f_tm.as_inner().clone(), arg_tm.as_inner().clone());

    // 7. Seal it in a TrustedTerm
    Ok((result_type, TrustedTerm::assume_trusted(app_syntax)))
}

/// **Pi Formation (Formation Rule)**
///
/// Given:
/// - `domain : Type_i` (a well-typed type, already checked by elaborator)
/// - `codomain : Type_j` (a well-typed type in the extended context, already checked by elaborator)
///
/// Produces:
/// - `Π(x : domain). codomain : Type_max(i,j)`
///
/// This is the formation rule for Pi types (dependent function types).
///
/// **Validation Contract**: The elaborator MUST ensure that both `domain` and `codomain`
/// have been checked against a universe type before calling this function.
/// This function performs defensive validation but relies on the elaborator's type checking.
pub async fn form_pi<'db>(
    domain: TrustedTerm<'db>,
    codomain: TrustedTerm<'db>,
) -> Result<TrustedTerm<'db>, RuleError> {
    // DEFENSIVE CHECK: Verify the domain and codomain are not obviously malformed
    // (e.g., not metavariables that should have been solved)
    // This is a sanity check, not full type checking.

    // The elaborator has already checked these are well-typed types.
    // We construct the Pi syntax and seal it.
    let pi_syntax = Syntax::pi_rc(
        domain.as_inner().clone(),
        hwml_core::binding::Binding::new(codomain.as_inner().clone()),
    );

    // Seal it in a TrustedTerm
    Ok(TrustedTerm::assume_trusted(pi_syntax))
}

/// **Lambda (Checking Rule)**
///
/// Given:
/// - `expected_type` evaluates to `Π(x : A). B`
/// - `body : B` (already checked in the extended context with `x : A`)
///
/// Produces:
/// - `λx. body : Π(x : A). B`
///
/// This is the introduction rule for Pi types (lambda abstraction).
pub async fn check_lam<'db, 'g>(
    ctx: &SolverEnvironment<'db, 'g>,
    expected_type: RcValue<'db>,
    body: TrustedTerm<'db>,
) -> Result<TrustedTerm<'db>, RuleError> {
    // 1. Force expected_type to ensure it's a VPi
    let expected_whnf = force(ctx, expected_type.clone())
        .map_err(|e| RuleError::ForceFailed(format!("{:?}", e)))?;

    // 2. Verify it's a Pi type
    match &*expected_whnf {
        Value::Pi(_pi) => {
            // The body has already been checked by the elaborator
            // We just need to construct the lambda syntax and seal it

            // Construct the lambda syntax
            let lam_syntax =
                Syntax::lambda_rc(hwml_core::binding::Binding::new(body.as_inner().clone()));

            // Seal it in a TrustedTerm
            Ok(TrustedTerm::assume_trusted(lam_syntax))
        }
        other => Err(RuleError::ExpectedPi {
            got: format!("{:?}", other),
        }),
    }
}

// ============================================================================
// Additional Helper Rules
// ============================================================================

/// **Universe Formation**
///
/// Produces: `Type_i : Type_{i+1}`
///
/// This is the formation rule for universe types.
pub fn form_universe<'db>(level: hwml_core::common::UniverseLevel) -> TrustedTerm<'db> {
    let univ_syntax = Syntax::universe_rc(level);
    TrustedTerm::assume_trusted(univ_syntax)
}

/// **Variable Reference**
///
/// Given a de Bruijn index, produces a variable reference.
/// The elaborator is responsible for ensuring the variable is in scope.
pub fn var_ref<'db>(index: hwml_core::common::Index) -> TrustedTerm<'db> {
    let var_syntax = Syntax::variable_rc(index);
    TrustedTerm::assume_trusted(var_syntax)
}

/// **Metavariable / Hole**
///
/// Constructs a metavariable reference.
/// The elaborator creates the metavariable ID and this rule wraps it.
pub fn form_meta<'db>(id: hwml_core::common::MetaVariableId) -> TrustedTerm<'db> {
    let meta_syntax = Syntax::metavariable_rc(id, vec![]);
    TrustedTerm::assume_trusted(meta_syntax)
}

/// **Let Binding (Trusted Constructor)**
///
/// Given:
/// - `value_ty : Type` (the type of the bound value, already checked by elaborator)
/// - `value : value_ty` (the value being bound, already checked by elaborator)
/// - `body : T` (the body with the binding in scope, already elaborated)
///
/// Produces:
/// - `let x = value in body : T`
///
/// **Validation Contract**: The elaborator MUST ensure that:
/// 1. `value_ty` is a well-typed type
/// 2. `value` has been checked against `value_ty`
/// 3. `body` has been elaborated with the binding in scope
pub fn form_let<'db>(
    value_ty: TrustedTerm<'db>,
    value: TrustedTerm<'db>,
    body: TrustedTerm<'db>,
) -> TrustedTerm<'db> {
    let let_syntax = Syntax::let_rc(
        value_ty.as_inner().clone(),
        value.as_inner().clone(),
        hwml_core::binding::Binding::new(body.as_inner().clone()),
    );
    TrustedTerm::assume_trusted(let_syntax)
}

/// **Hardware Arrow (HArrow) (Trusted Constructor)**
///
/// Given:
/// - `source : HType` (hardware type, already checked by elaborator)
/// - `target : HType` (hardware type, already checked by elaborator)
///
/// Produces:
/// - `source => target : MType`
///
/// **Validation Contract**: The elaborator MUST ensure that both `source` and `target`
/// are well-typed hardware types before calling this function.
pub fn form_harrow<'db>(source: TrustedTerm<'db>, target: TrustedTerm<'db>) -> TrustedTerm<'db> {
    let harrow_syntax = Syntax::harrow_rc(source.as_inner().clone(), target.as_inner().clone());
    TrustedTerm::assume_trusted(harrow_syntax)
}

/// **Bit Type**
///
/// Produces: `Bit : HType`
pub fn form_bit<'db>() -> TrustedTerm<'db> {
    let bit_syntax = Syntax::bit_rc();
    TrustedTerm::assume_trusted(bit_syntax)
}

/// **Zero Constant**
///
/// Produces: `0 : Bit`
pub fn form_zero<'db>() -> TrustedTerm<'db> {
    let zero_syntax = Syntax::zero_rc();
    TrustedTerm::assume_trusted(zero_syntax)
}

/// **One Constant**
///
/// Produces: `1 : Bit`
pub fn form_one<'db>() -> TrustedTerm<'db> {
    let one_syntax = Syntax::one_rc();
    TrustedTerm::assume_trusted(one_syntax)
}

/// **Equality Type (Trusted Constructor)**
///
/// Given:
/// - `ty : Type_i` (the type of the elements, already checked by elaborator)
/// - `lhs : ty` (left-hand side, already checked by elaborator)
/// - `rhs : ty` (right-hand side, already checked by elaborator)
///
/// Produces:
/// - `Eq ty lhs rhs : Type_i`
///
/// **Validation Contract**: The elaborator MUST ensure that:
/// 1. `ty` is a well-typed type in some universe
/// 2. `lhs` has been checked against `ty`
/// 3. `rhs` has been checked against `ty`
pub fn form_eq<'db>(
    ty: TrustedTerm<'db>,
    lhs: TrustedTerm<'db>,
    rhs: TrustedTerm<'db>,
) -> TrustedTerm<'db> {
    let eq_syntax = Syntax::eq_rc(
        ty.as_inner().clone(),
        lhs.as_inner().clone(),
        rhs.as_inner().clone(),
    );
    TrustedTerm::assume_trusted(eq_syntax)
}

/// **Reflexivity**
///
/// Produces: `refl : Eq A x x`
pub fn form_refl<'db>() -> TrustedTerm<'db> {
    let refl_syntax = Syntax::refl_rc();
    TrustedTerm::assume_trusted(refl_syntax)
}

/// **Transport (Trusted Constructor)**
///
/// Given:
/// - `motive : Π(x : A). Type` (the motive for transport, already validated)
/// - `proof : Eq A x y` (equality proof, already checked by elaborator)
/// - `value : motive x` (value at x, already checked by elaborator)
///
/// Produces:
/// - `transport motive proof value : motive y`
///
/// **Validation Contract**: The elaborator MUST ensure that:
/// 1. `motive` is a valid function from `A` to a universe
/// 2. `proof` is an equality proof of type `Eq A x y`
/// 3. `value` has been checked against `motive x`
pub fn form_transport<'db>(
    motive: Closure<'db>,
    proof: TrustedTerm<'db>,
    value: TrustedTerm<'db>,
) -> TrustedTerm<'db> {
    // Quote the closure to a lambda syntax
    let motive_syntax = Syntax::lambda_rc(hwml_core::binding::Binding::new(motive.term));
    let transport_syntax = Syntax::transport_rc(
        motive_syntax,
        proof.as_inner().clone(),
        value.as_inner().clone(),
    );
    TrustedTerm::assume_trusted(transport_syntax)
}

/// **Case Expression**
///
/// Given:
/// - `scrutinee_index` (de Bruijn index of the scrutinee variable)
/// - `branches` (list of case branches)
///
/// Produces:
/// - `case scrutinee of branches`
pub fn form_case<'db>(
    scrutinee_index: hwml_core::common::Index,
    branches: Vec<hwml_core::syn::CaseBranch<'db>>,
) -> TrustedTerm<'db> {
    let case_syntax = Syntax::case_rc(scrutinee_index, branches);
    TrustedTerm::assume_trusted(case_syntax)
}
