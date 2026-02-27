//! Lambda Saturation Lowering Pass
//!
//! This module implements the lambda saturation pass for 2LTT (Two-Level Type Theory).
//! The key transformation is beta-reducing `HApplication` values where the module is
//! a concrete `Module` closure, effectively inlining hardware lambdas at their call sites.
//!
//! In 2LTT, hardware-level functions cannot be treated as first-class values - they
//! must be inlined at their call sites. This pass ensures all `HApplication` values
//! where the module is a concrete `Module` closure are reduced.
//!
//! **Important**: This pass operates on already-normalized values. It does NOT call
//! `eval` - the input is assumed to be fully evaluated. The pass only performs
//! beta-reduction for hardware-level applications.

use crate::{
    eval::run_closure,
    quote,
    syn::RcSyntax,
    val::{self, Closure, GlobalEnv, Value},
};
use std::rc::Rc;

/// Errors that can occur during lowering.
#[derive(Debug, Clone)]
pub enum Error<'db> {
    /// Closure evaluation failed during beta-reduction.
    ClosureError(crate::eval::Error),
    /// Quotation failed during lowering.
    QuoteError(quote::Error<'db>),
}

impl<'db> From<crate::eval::Error> for Error<'db> {
    fn from(e: crate::eval::Error) -> Self {
        Error::ClosureError(e)
    }
}

impl<'db> From<quote::Error<'db>> for Error<'db> {
    fn from(e: quote::Error<'db>) -> Self {
        Error::QuoteError(e)
    }
}

type Result<'db, T> = std::result::Result<T, Error<'db>>;

/// Main entry point: saturate all hardware lambdas in a value.
///
/// This traverses the value tree and beta-reduces any `HApplication` where
/// the module is a concrete `Module` closure. The input is assumed to be
/// already normalized - no evaluation is performed.
///
/// Returns a saturated value where all reducible HApplications have been
/// beta-reduced.
pub fn saturate_value<'db>(
    global: &GlobalEnv<'db>,
    value: &Value<'db>,
) -> Result<'db, Rc<Value<'db>>> {
    match value {
        // The key case: HApplication - try to beta-reduce
        Value::HApplication(happ) => saturate_happlication(global, happ),

        // Closures need special handling - we saturate their bodies
        Value::Lambda(lam) => saturate_lambda(global, lam),
        Value::Pi(pi) => saturate_pi(global, pi),
        Value::Module(module) => saturate_module(global, module),
        Value::HArrow(harrow) => saturate_harrow(global, harrow),

        // Recursive cases with subvalues
        Value::Lift(lift) => {
            let new_ty = saturate_value(global, &lift.ty)?;
            Ok(Rc::new(Value::lift(new_ty)))
        }
        Value::SLift(slift) => {
            let new_ty = saturate_value(global, &slift.ty)?;
            Ok(Rc::new(Value::slift(new_ty)))
        }
        Value::MLift(mlift) => {
            let new_ty = saturate_value(global, &mlift.ty)?;
            Ok(Rc::new(Value::mlift(new_ty)))
        }
        Value::TypeConstructor(tc) => {
            let new_args = tc
                .arguments
                .iter()
                .map(|arg| saturate_value(global, arg))
                .collect::<Result<'db, Vec<_>>>()?;
            Ok(Rc::new(Value::type_constructor(tc.constructor, new_args)))
        }
        Value::DataConstructor(dc) => {
            let new_args = dc
                .arguments
                .iter()
                .map(|arg| saturate_value(global, arg))
                .collect::<Result<'db, Vec<_>>>()?;
            Ok(Rc::new(Value::data_constructor(dc.constructor, new_args)))
        }
        Value::Rigid(rigid) => saturate_rigid(global, rigid),
        Value::Flex(flex) => saturate_flex(global, flex),

        // Base cases: no subvalues to traverse
        Value::Universe(_)
        | Value::HardwareUniverse(_)
        | Value::SignalUniverse(_)
        | Value::ModuleUniverse(_)
        | Value::Bit(_)
        | Value::Zero(_)
        | Value::One(_)
        | Value::Prim(_)
        | Value::Constant(_) => Ok(Rc::new(value.clone())),
    }
}

/// Saturate an HApplication value.
///
/// If the module is a concrete `Module` closure, we perform beta-reduction
/// by running the closure with the argument. Otherwise, we recursively
/// saturate the subterms.
fn saturate_happlication<'db>(
    global: &GlobalEnv<'db>,
    happ: &val::HApplication<'db>,
) -> Result<'db, Rc<Value<'db>>> {
    // First saturate the argument (always needed)
    let saturated_arg = saturate_value(global, &happ.argument)?;

    // Check if the module is already a concrete Module - if so, beta-reduce directly
    // without saturating the module (which would unnecessarily process the closure body)
    match happ.module.as_ref() {
        Value::Module(module) => {
            // Beta-reduce: run the module's body with the saturated argument
            let result = run_closure(global, &module.body, [saturated_arg])?;
            // Recursively saturate in case the result contains more HApplications
            saturate_value(global, &result)
        }
        _ => {
            // Not a concrete Module - saturate the module and keep as HApplication
            let saturated_module = saturate_value(global, &happ.module)?;

            // Check again after saturation (the module might have become concrete)
            match &*saturated_module {
                Value::Module(module) => {
                    let result = run_closure(global, &module.body, [saturated_arg])?;
                    saturate_value(global, &result)
                }
                _ => {
                    let saturated_ty = saturate_value(global, &happ.module_ty)?;
                    Ok(Rc::new(Value::happlication(
                        saturated_module,
                        saturated_ty,
                        saturated_arg,
                    )))
                }
            }
        }
    }
}

/// Saturate a closure by instantiating it with a fresh variable and saturating the body.
fn saturate_closure<'db>(
    global: &GlobalEnv<'db>,
    closure: &Closure<'db>,
    var_ty: Rc<Value<'db>>,
) -> Result<'db, Closure<'db>> {
    // Create a fresh variable at the closure's depth
    let depth = closure.local.depth();
    let var = Rc::new(Value::variable(crate::common::Level::new(depth), var_ty));

    // Run the closure with the fresh variable to get the body
    let body = run_closure(global, closure, [var.clone()])?;

    // Saturate the body
    let saturated_body = saturate_value(global, &body)?;

    // Quote the saturated body back to syntax to create a new closure
    let new_syntax = quote::quote(
        global,
        depth + 1,
        &saturated_body,
        &Rc::new(Value::universe(crate::common::UniverseLevel::new(0))),
    )?;

    // Create a new closure with the saturated body
    Ok(Closure::new(closure.local.clone(), new_syntax))
}

// ============================================================================
// Binder Saturation Functions (Value-based)
// ============================================================================

fn saturate_lambda<'db>(
    global: &GlobalEnv<'db>,
    lam: &val::Lambda<'db>,
) -> Result<'db, Rc<Value<'db>>> {
    // Use a placeholder type for the bound variable
    let placeholder_ty = Rc::new(Value::universe(crate::common::UniverseLevel::new(0)));
    let new_body = saturate_closure(global, &lam.body, placeholder_ty)?;
    Ok(Rc::new(Value::lambda(new_body)))
}

fn saturate_pi<'db>(global: &GlobalEnv<'db>, pi: &val::Pi<'db>) -> Result<'db, Rc<Value<'db>>> {
    let new_source = saturate_value(global, &pi.source)?;
    let new_target = saturate_closure(global, &pi.target, new_source.clone())?;
    Ok(Rc::new(Value::pi(new_source, new_target)))
}

fn saturate_module<'db>(
    global: &GlobalEnv<'db>,
    module: &val::Module<'db>,
) -> Result<'db, Rc<Value<'db>>> {
    // Use Bit as placeholder type for module argument
    let placeholder_ty = Rc::new(Value::bit());
    let new_body = saturate_closure(global, &module.body, placeholder_ty)?;
    Ok(Rc::new(Value::module(new_body)))
}

fn saturate_harrow<'db>(
    global: &GlobalEnv<'db>,
    harrow: &val::HArrow<'db>,
) -> Result<'db, Rc<Value<'db>>> {
    let new_source = saturate_value(global, &harrow.source)?;
    let new_target = saturate_closure(global, &harrow.target, new_source.clone())?;
    Ok(Rc::new(Value::harrow(new_source, new_target)))
}

// ============================================================================
// Neutral Term Saturation
// ============================================================================

fn saturate_rigid<'db>(
    global: &GlobalEnv<'db>,
    rigid: &val::Rigid<'db>,
) -> Result<'db, Rc<Value<'db>>> {
    let new_ty = saturate_value(global, &rigid.ty)?;
    let new_spine = saturate_spine(global, &rigid.spine)?;
    Ok(Rc::new(Value::Rigid(val::Rigid {
        head: rigid.head.clone(),
        ty: new_ty,
        spine: new_spine,
    })))
}

fn saturate_flex<'db>(
    global: &GlobalEnv<'db>,
    flex: &val::Flex<'db>,
) -> Result<'db, Rc<Value<'db>>> {
    let new_ty = saturate_value(global, &flex.ty)?;
    let new_spine = saturate_spine(global, &flex.spine)?;
    Ok(Rc::new(Value::Flex(val::Flex {
        head: flex.head.clone(),
        ty: new_ty,
        spine: new_spine,
    })))
}

fn saturate_spine<'db>(
    global: &GlobalEnv<'db>,
    spine: &val::Spine<'db>,
) -> Result<'db, val::Spine<'db>> {
    let new_eliminators = spine
        .iter()
        .map(|elim| saturate_eliminator(global, elim))
        .collect::<Result<'db, Vec<_>>>()?;
    Ok(val::Spine::new(new_eliminators))
}

fn saturate_eliminator<'db>(
    global: &GlobalEnv<'db>,
    elim: &val::Eliminator<'db>,
) -> Result<'db, val::Eliminator<'db>> {
    match elim {
        val::Eliminator::Application(app) => {
            let new_value = saturate_value(global, &app.argument.value)?;
            let new_ty = saturate_value(global, &app.argument.ty)?;
            Ok(val::Eliminator::application(val::Normal {
                value: new_value,
                ty: new_ty,
            }))
        }
        val::Eliminator::Case(case) => {
            let new_params = case
                .parameters
                .iter()
                .map(|p| saturate_value(global, p))
                .collect::<Result<'db, Vec<_>>>()?;
            // For now, keep motive and branches as-is since saturating closures is complex
            Ok(val::Eliminator::case(
                case.type_constructor,
                new_params,
                case.motive.clone(),
                case.branches.clone(),
            ))
        }
    }
}

// ============================================================================
// Convenience Functions
// ============================================================================

/// Saturate a value and quote it back to syntax.
///
/// This is the main entry point for the CIRCT translation pipeline.
/// It takes a normalized value, saturates all HApplications, and
/// quotes the result back to syntax.
pub fn saturate_and_quote<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    value: &Value<'db>,
    ty: &Value<'db>,
) -> Result<'db, RcSyntax<'db>> {
    let saturated = saturate_value(global, value)?;
    let quoted = quote::quote(global, depth, &saturated, &Rc::new(ty.clone()))?;
    Ok(quoted)
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::syn::{print::print_syntax_to_string, Syntax};
    use crate::val::LocalEnv;
    use crate::Database;
    use hwml_support::salsa::IntoWithDb;

    /// Test that a simple value without HApplication passes through unchanged.
    #[test]
    fn test_saturate_no_happlication() {
        let global = GlobalEnv::new();

        // Simple value: One
        let value = Value::one();
        let result = saturate_value(&global, &value).expect("should saturate");

        // Should be the same value
        assert!(matches!(&*result, Value::One(_)));
    }

    /// Test that HApplication with a concrete Module is beta-reduced.
    #[test]
    fn test_saturate_happlication_with_module() {
        let db = Database::default();
        let global = GlobalEnv::new();

        // Create a Module closure that returns its argument (identity)
        // mod %0 - the body just refers to the bound variable
        let module_body = Syntax::variable_rc(crate::common::Index(0));
        let module_closure = Closure::new(LocalEnv::new(), module_body);
        let module = Value::module(module_closure);

        // The type: Bit → Bit
        let module_ty = Value::harrow(
            Rc::new(Value::bit()),
            Closure::new(LocalEnv::new(), Syntax::bit_rc()),
        );

        // The argument: One
        let arg = Rc::new(Value::one());

        // The HApplication: module<ty>(arg)
        let happ = Value::happlication(Rc::new(module), Rc::new(module_ty), arg);

        let result = saturate_value(&global, &happ).expect("should saturate");

        // After saturation, this should be: One
        assert!(matches!(&*result, Value::One(_)));
    }

    /// Test that HApplication with a non-Module (constant) is preserved.
    #[test]
    fn test_saturate_happlication_with_constant() {
        let db = Database::default();
        let global = GlobalEnv::new();

        // Create an HApplication where the module is a constant
        let constant = Value::Constant("myModule".into_with_db(&db));
        let module_ty = Value::harrow(
            Rc::new(Value::bit()),
            Closure::new(LocalEnv::new(), Syntax::bit_rc()),
        );
        let arg = Rc::new(Value::one());

        let happ = Value::happlication(Rc::new(constant), Rc::new(module_ty), arg);

        let result = saturate_value(&global, &happ).expect("should saturate");

        // Should preserve the HApplication since constant can't be reduced
        assert!(matches!(&*result, Value::HApplication(_)));
    }

    /// Test that nested HApplications are saturated correctly.
    #[test]
    fn test_saturate_nested_happlication() {
        let global = GlobalEnv::new();

        // Inner module: mod 0 (ignores argument, returns Zero)
        let inner_module_body = Syntax::zero_rc();
        let inner_closure = Closure::new(LocalEnv::new(), inner_module_body);
        let inner_module = Value::module(inner_closure);

        let inner_ty = Value::harrow(
            Rc::new(Value::bit()),
            Closure::new(LocalEnv::new(), Syntax::bit_rc()),
        );

        // Inner HApplication: (mod 0)<Bit→Bit>(One) which should reduce to Zero
        let inner_happ = Value::happlication(
            Rc::new(inner_module),
            Rc::new(inner_ty.clone()),
            Rc::new(Value::one()),
        );

        // Outer module: mod %0 (identity - returns argument)
        let outer_module_body = Syntax::variable_rc(crate::common::Index(0));
        let outer_closure = Closure::new(LocalEnv::new(), outer_module_body);
        let outer_module = Value::module(outer_closure);

        let outer_ty = Value::harrow(
            Rc::new(Value::bit()),
            Closure::new(LocalEnv::new(), Syntax::bit_rc()),
        );

        // Outer HApplication: (mod %0)<Bit→Bit>((mod 0)<Bit→Bit>(One))
        // Should reduce to: Zero (from inner application, passed through outer identity)
        let outer_happ = Value::happlication(
            Rc::new(outer_module),
            Rc::new(outer_ty),
            Rc::new(inner_happ),
        );

        let result = saturate_value(&global, &outer_happ).expect("should saturate");

        // After saturation, this should be: Zero
        assert!(matches!(&*result, Value::Zero(_)));
    }

    /// Test saturate_and_quote convenience function.
    #[test]
    fn test_saturate_and_quote() {
        let db = Database::default();
        let global = GlobalEnv::new();

        // Create a simple HApplication that reduces to One
        let module_body = Syntax::one_rc(); // mod that ignores arg and returns 1
        let module_closure = Closure::new(LocalEnv::new(), module_body);
        let module = Value::module(module_closure);

        let module_ty = Value::harrow(
            Rc::new(Value::bit()),
            Closure::new(LocalEnv::new(), Syntax::bit_rc()),
        );

        let happ = Value::happlication(Rc::new(module), Rc::new(module_ty), Rc::new(Value::zero()));

        // Saturate and quote
        let result = saturate_and_quote(&global, 0, &happ, &Value::bit()).expect("should saturate");

        // The result should be the syntax for "1"
        let printed = print_syntax_to_string(&db, &result);
        assert_eq!(printed, "1");
    }
}
