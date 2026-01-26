//! Translation from HWML AST to CIRCT IR (using raw MLIR C API).
//!
//! This module handles the translation of HWML's core IR to CIRCT's hardware dialects.
//! The translation process involves:
//!
//! 1. **Type Translation**: Convert HWML types to CIRCT hardware types
//! 2. **Declaration Translation**: Convert HWML declarations to CIRCT operations
//! 3. **Expression Translation**: Convert HWML expressions to CIRCT operations
//!
//! # Translation Strategy
//!
//! HWML uses a dependently-typed core language, while CIRCT uses MLIR's type system.
//! The translation needs to:
//!
//! - Map HWML's type constructors to CIRCT's hardware types (e.g., Bit, UInt, SInt)
//! - Map HWML's data constructors to CIRCT operations (e.g., wire assignments, gates)
//! - Handle HWML's module system and map it to CIRCT's hw.module operations

use crate::{
    context::CirctContext,
    dialects,
    error::{Error, Result},
};
use hwml_circt_sys::{
    create_named_attribute, operation_result, MlirAttributeWrapper, MlirBlockWrapper,
    MlirLocationWrapper, MlirModuleWrapper, MlirRegionWrapper, MlirTypeWrapper, MlirValueWrapper,
    OperationBuilder,
};
use hwml_core::{
    declaration::Module,
    syn::{Syntax, RcSyntax},
};

/// Translation context that tracks state during translation.
pub struct TranslationContext<'c> {
    /// The CIRCT context
    circt_ctx: &'c CirctContext,
    /// The current MLIR location (for error reporting)
    location: MlirLocationWrapper,
}

impl<'c> TranslationContext<'c> {
    /// Create a new translation context.
    pub fn new(circt_ctx: &'c CirctContext) -> Self {
        let location = circt_ctx.unknown_location();
        TranslationContext {
            circt_ctx,
            location,
        }
    }

    /// Get the CIRCT context.
    pub fn circt_context(&self) -> &'c CirctContext {
        self.circt_ctx
    }

    /// Get the current location.
    pub fn location(&self) -> MlirLocationWrapper {
        self.location
    }
}

/// Translate an HWML module to CIRCT IR.
///
/// For each top-level hardware constant (a constant whose type is a lifted hardware type ^HWType),
/// this creates a CIRCT HW module with:
/// - One input port for each argument in the constant's type
/// - One output port for the result
///
/// This function type-checks all declarations and builds the GlobalEnv before translation.
pub fn translate_module<'c, 'db>(
    ctx: &'c CirctContext,
    db: &'db dyn salsa::Database,
    hwml_module: &Module<'db>,
) -> Result<MlirModuleWrapper> {
    use hwml_core::val::GlobalEnv;

    // Start with an empty global environment
    let initial_env = GlobalEnv::new();

    // Type-check all declarations and build the global environment
    let checked = hwml_core::check_module::check_module(hwml_module, initial_env).map_err(|e| {
        Error::UnsupportedConstruct(format!("Module type-checking failed: {:?}", e))
    })?;

    // Translate using the checked module
    translate_checked_module(ctx, db, hwml_module, &checked)
}

/// Translate an HWML module that has already been type-checked.
///
/// This is useful when you want to type-check separately (e.g., to report errors)
/// and then translate.
pub fn translate_checked_module<'c, 'db>(
    ctx: &'c CirctContext,
    db: &'db dyn salsa::Database,
    hwml_module: &Module<'db>,
    checked: &hwml_core::check_module::CheckedModule<'db>,
) -> Result<MlirModuleWrapper> {
    let location = ctx.unknown_location();
    let mlir_module = ctx.create_module(location);

    // Translate each hardware constant to a HW module
    for &hw_const_name in &checked.hardware_constants {
        // First, try to find a HardwareConstant declaration.
        if let Some(hconst) = hwml_module.declarations.iter().find_map(|decl| {
            if let hwml_core::declaration::Declaration::HardwareConstant(hc) = decl {
                if hc.name == hw_const_name {
                    return Some(hc);
                }
            }
            None
        }) {
            use hwml_core::{eval, quote, val};

            // Evaluate the hardware term in an empty hardware and meta
            // environment, but with the checked global environment so that
            // splices (~t) can refer to meta-level constants.
            let mut henv = val::HEnvironment::new();
            let mut meta_env = val::Environment::new(&checked.global_env);
            let Value =
                eval::eval_hardware(&mut henv, &mut meta_env, &hconst.value).map_err(|e| {
                    Error::UnsupportedConstruct(format!(
                        "Failed to evaluate hardware constant {}: {:?}",
                        hconst.name.name(db),
                        e
                    ))
                })?;

            // Evaluate the hardware type to a semantic value so we can use
            // the *lifted* type-directed quotation (`^ht`). The type of an
            // `hconst` is a hardware type (Bit or HArrow ...), not a lifted
            // meta-level type, so we wrap it in `Lift` before quoting.
            let mut type_env = val::Environment::new(&checked.global_env);
            let hw_ty_value = eval::eval(&mut type_env, &hconst.ty).map_err(|e| {
                Error::UnsupportedConstruct(format!(
                    "Failed to evaluate hardware constant type {}: {:?}",
                    hconst.name.name(db),
                    e
                ))
            })?;

            let lifted_ty = val::Value::lift(hw_ty_value.clone());
            let fake_value = val::Value::quote(Value.clone());

            // Read the evaluated hardware value back to Syntax using the
            // core lifted-type quotation. This ultimately dispatches to
            // `quote_Value`, which will apply any hardware lambdas to fresh
            // variables and, via `run_hclosure`, evaluate splices inside
            // those lambdas.
            let syntax = quote::quote(db, &checked.global_env, 0, &lifted_ty, &fake_value)
                .map_err(|e| {
                    Error::UnsupportedConstruct(format!(
                        "Failed to quote hardware constant {}: {:?}",
                        hconst.name.name(db),
                        e
                    ))
                })?;

            let hsyntax = extract_hsyntax_from_syntax(&syntax).ok_or_else(|| {
                Error::UnsupportedConstruct(format!(
                    "Failed to extract hardware syntax from quoted value for {}",
                    hconst.name.name(db)
                ))
            })?;

            // Extract input types from the constant's (hardware) type.
            let input_types = extract_hardware_input_types(&hconst.ty);

            // Translate this hardware constant to a HW module
            translate_constant_to_module(
                ctx,
                db,
                &mlir_module,
                location,
                &hconst.name,
                &input_types,
                &hsyntax,
            )?;
            continue;
        }

        // Fall back to regular Constant with quoted type
        let constant = hwml_module
            .declarations
            .iter()
            .find_map(|decl| {
                if let hwml_core::declaration::Declaration::Constant(c) = decl {
                    if c.name == hw_const_name {
                        return Some(c);
                    }
                }
                None
            })
            .ok_or_else(|| {
                Error::UnsupportedConstruct(format!(
                    "HardwareUniverse constant {} not found in declarations",
                    hw_const_name.name(db)
                ))
            })?;

        // Get the constant info from the global environment
        let constant_info = checked.global_env.constant(hw_const_name).map_err(|e| {
            Error::UnsupportedConstruct(format!("Constant not found in environment: {:?}", e))
        })?;

        // Evaluate the constant's syntax to get a value
        let mut eval_env = hwml_core::val::Environment::new(&checked.global_env);
        let constant_value =
            hwml_core::eval::eval(&mut eval_env, &constant_info.value).map_err(|e| {
                Error::UnsupportedConstruct(format!("Failed to evaluate constant: {}", e))
            })?;

        // Extract Syntax from the evaluated value
        if let Some(hsyntax) =
            extract_hsyntax_from_value(db, &checked.global_env, &constant.ty, &constant_value)
        {
            // Extract input types from the constant's type (Pi types)
            let input_types = extract_input_types(&constant.ty);

            // Translate this constant to a HW module
            translate_constant_to_module(
                ctx,
                db,
                &mlir_module,
                location,
                &constant.name,
                &input_types,
                &hsyntax,
            )?;
        }
    }

    Ok(mlir_module)
}

/// Extract Syntax from a *meta-level* value whose type is (up to Pis)
/// a lifted hardware type, by quoting it back to syntax and then
/// pulling out the inner `Syntax` from a `Quote` node.
///
/// This is used for constants like:
///
///   const @Queue0Q : ^($Bit → $Bit → $Bit) = ...
///   const @QueueGen : ∀ (%n : #[@Nat]) → ^($Bit → $Bit → $Bit) = ...
///
/// We always use the *type-directed* `quote` function from hwml-core,
/// relying on the fact that `check_module` has ensured the value has the
/// given type. For a value of type `^ht`, this reduces to
/// `quote_lift_instance`, which in turn uses `quote_Value` and therefore
/// fully evaluates any hardware closures (running splices) before
/// producing `Syntax`.
fn extract_hsyntax_from_value<'db>(
    db: &'db dyn salsa::Database,
    global_env: &hwml_core::val::GlobalEnv<'db>,
    ty: &hwml_core::syn::RcSyntax<'db>,
    value: &hwml_core::val::Value<'db>,
) -> Option<RcSyntax<'db>> {
    use hwml_core::{eval, quote};

    // First evaluate the (meta-level) type syntax to a semantic type.
    let mut env = hwml_core::val::Environment::new(global_env);
    let ty_value = eval::eval(&mut env, ty).ok()?;

    // Quote the value at this type back to syntax, then extract the
    // inner `Syntax` from the resulting `Quote` node.
    let syntax = quote::quote(db, global_env, 0, &ty_value, value).ok()?;
    extract_hsyntax_from_syntax(&syntax)
}

/// Extract Syntax from a Syntax node if it's a Quote node.
/// This function recursively searches through Lambda nodes to find the innermost Quote.
fn extract_hsyntax_from_syntax<'db>(
    syntax: &hwml_core::syn::RcSyntax<'db>,
) -> Option<RcSyntax<'db>> {
    use hwml_core::syn::Syntax;

    match &**syntax {
        // Direct quote
        Syntax::Quote(quote) => Some(quote.tm.clone()),

        // Lambda with a body - recurse into the body.  This is how we
        // handle generators like `QueueGen :  n. ^ht`, where normalisation
        // yields a lambda whose body is a quote.
        Syntax::Lambda(lambda) => extract_hsyntax_from_syntax(&lambda.body),

        // Check node - recurse into the term
        Syntax::Check(check) => extract_hsyntax_from_syntax(&check.term),

        // For now we do not try to peer inside applications or other
        // eliminators here; if quotation produced anything other than a
        // lambda/quote tower ending in a quote, we give up.
        _ => None,
    }
}

/// Extract *hardware* input types from the type of a constant whose
/// result is a lifted hardware type, e.g.
///
///   ^($Bit → $Bit → $Bit)
///   ∀ (%n : #[@Nat]) → ^($Bit → $Bit → $Bit)
///
/// We ignore outer Pi-binders (meta-level parameters) and then look for a
/// `Lift ht` in the result, where `ht` is a hardware arrow type. The
/// returned vector contains the argument types from that HArrow chain.
fn extract_input_types<'db>(
    ty: &hwml_core::syn::RcSyntax<'db>,
) -> Vec<hwml_core::syn::RcSyntax<'db>> {
    use hwml_core::syn::Syntax;

    // Strip off outer Pi binders – these are meta-level parameters, not
    // hardware ports.
    let mut current = ty;
    loop {
        match &**current {
            Syntax::Pi(pi) => {
                current = &pi.target;
            }
            _ => break,
        }
    }

    // At this point we expect a lifted hardware type. If so, delegate to
    // the HArrow helper to extract the actual hardware argument types.
    match &**current {
        Syntax::Lift(lift) => extract_hardware_input_types(&lift.tm),
        _ => Vec::new(),
    }
}

/// Extract input types from a hardware arrow type structure (HArrow).
/// Returns a vector of type syntax nodes representing the input types.
fn extract_hardware_input_types<'db>(
    ty: &hwml_core::syn::RcSyntax<'db>,
) -> Vec<hwml_core::syn::RcSyntax<'db>> {
    use hwml_core::syn::Syntax;

    let mut types = Vec::new();
    let mut current = ty;

    // Traverse nested HArrow types to collect all input types
    loop {
        match &**current {
            Syntax::HArrow(arrow) => {
                types.push(arrow.source.clone());
                current = &arrow.target;
            }
            _ => break,
        }
    }

    types
}

/// Unwrap nested Module nodes to get the innermost body expression.
/// Returns the body and the count of lambdas unwrapped.
fn unwrap_Modules<'a, 'db>(expr: &'a RcSyntax<'db>) -> (&'a RcSyntax<'db>, usize) {
    let mut current = expr;
    let mut count = 0;

    loop {
        match &**current {
            Syntax::Module(lambda) => {
                current = &lambda.body;
                count += 1;
            }
            _ => break,
        }
    }

    (current, count)
}

/// Translate a hardware constant to a CIRCT HW module.
fn translate_constant_to_module<'c, 'db>(
    ctx: &'c CirctContext,
    db: &'db dyn salsa::Database,
    mlir_module: &MlirModuleWrapper,
    location: MlirLocationWrapper,
    name: &hwml_core::syn::ConstantId<'db>,
    input_types: &[hwml_core::syn::RcSyntax<'db>],
    body: &RcSyntax<'db>,
) -> Result<()> {
    use hwml_core::syn::Syntax;

    // Get the module name from the constant name
    let module_name = name.name(db);

    // Unwrap Module nodes to get the actual body expression
    // Each Module corresponds to one input type
    let (actual_body, lambda_count) = unwrap_Modules(body);

    // Verify that the number of lambdas matches the number of input types
    if lambda_count != input_types.len() {
        return Err(Error::UnsupportedConstruct(format!(
            "Mismatch between lambda count ({}) and input types ({})",
            lambda_count,
            input_types.len()
        )));
    }

    // Convert input types to CIRCT types
    // For now, we only support $Bit types (possibly wrapped in Lift)
    let mut input_ports = Vec::new();
    for (i, input_ty) in input_types.iter().enumerate() {
        // Unwrap Lift if present, then check if this is a Bit type
        let inner_ty = match &**input_ty {
            Syntax::Lift(lift) => &lift.tm,
            other => other,
        };

        if !matches!(inner_ty, Syntax::Bit(_)) {
            return Err(Error::UnsupportedConstruct(format!(
                "Only $Bit (or ^$Bit) input types are currently supported, got: {:?}",
                input_ty
            )));
        }

        let bit_type = dialects::hw::bit_type(ctx.context());
        let port_name = MlirAttributeWrapper::string(ctx.context(), &format!("in{}", i));

        input_ports.push(hwml_circt_sys::HWModulePort {
            name: port_name.as_raw(),
            type_: bit_type.as_raw(),
            dir: hwml_circt_sys::HWModulePortDirection_Input,
        });
    }

    // Create output port
    let bit_type = dialects::hw::bit_type(ctx.context());
    let output_port_name = MlirAttributeWrapper::string(ctx.context(), "out");
    let output_port = hwml_circt_sys::HWModulePort {
        name: output_port_name.as_raw(),
        type_: bit_type.as_raw(),
        dir: hwml_circt_sys::HWModulePortDirection_Output,
    };

    // Combine input and output ports
    let mut all_ports = input_ports;
    all_ports.push(output_port);

    // Create the module type
    let module_universe = unsafe {
        let raw_type = hwml_circt_sys::hwModuleTypeGet(
            ctx.context().as_raw(),
            all_ports.len() as isize,
            all_ports.as_ptr(),
        );
        MlirTypeWrapper::from_raw(raw_type)
    };

    // Create the module body
    let region = MlirRegionWrapper::new();

    // Create block with input arguments
    let input_arg_types: Vec<MlirTypeWrapper> = (0..input_types.len())
        .map(|_| dialects::hw::bit_type(ctx.context()))
        .collect();
    let block = unsafe {
        let arg_types_raw: Vec<_> = input_arg_types.iter().map(|t| t.as_raw()).collect();
        // Create locations for each argument
        let arg_locs: Vec<_> = (0..input_types.len()).map(|_| location.as_raw()).collect();
        let raw_block = hwml_circt_sys::mlirBlockCreate(
            arg_types_raw.len() as isize,
            arg_types_raw.as_ptr(),
            arg_locs.as_ptr(),
        );
        MlirBlockWrapper::from_raw(raw_block)
    };

    // Translate the body expression (with lambdas unwrapped)
    let result_value = translate_hsyntax_expr(ctx, db, location, &block, actual_body)?;

    // Create hw.output operation
    let output_op = OperationBuilder::new("hw.output", location)
        .add_operands(&[result_value])
        .build()
        .map_err(|e| Error::MlirOperation(e))?;
    block.append_operation(output_op);

    region.append_block(block.as_raw());

    // Create an empty parameters array (no module parameters)
    let empty_params = MlirAttributeWrapper::array(ctx.context(), &[]);

    // Create the hw.module operation
    let module_op = OperationBuilder::new("hw.module", location)
        .add_attributes(vec![
            create_named_attribute(
                ctx.context(),
                "sym_name",
                MlirAttributeWrapper::string(ctx.context(), module_name),
            ),
            create_named_attribute(
                ctx.context(),
                "module_universe",
                MlirAttributeWrapper::type_attr(module_universe),
            ),
            create_named_attribute(ctx.context(), "parameters", empty_params),
        ])
        .add_regions(vec![region])
        .build()
        .map_err(|e| Error::MlirOperation(e))?;

    // Add the module to the MLIR module
    unsafe {
        let module_body = hwml_circt_sys::mlirModuleGetBody(mlir_module.as_raw());
        hwml_circt_sys::mlirBlockAppendOwnedOperation(module_body, module_op);
    }

    Ok(())
}

/// Translate an Syntax expression to a CIRCT HW module named "Top".
///
/// This is a simplified entry point for translating hardware-level expressions
/// directly to CIRCT without going through the full module system.
pub fn translate_hsyntax_to_top<'c, 'db>(
    ctx: &'c CirctContext,
    db: &'db dyn salsa::Database,
    expr: &RcSyntax<'db>,
) -> Result<MlirModuleWrapper> {
    let location = ctx.unknown_location();
    let mlir_module = ctx.create_module(location);

    // Get the bit type
    let bit_type = dialects::hw::bit_type(ctx.context());

    // Create the Top module with one output
    // Build hw.module @Top() -> (out: i1) { ... }
    let region = MlirRegionWrapper::new();
    let block = MlirBlockWrapper::new();

    // Translate the expression to get the result value
    let result_value = translate_hsyntax_expr(ctx, db, location, &block, expr)?;

    // Create hw.output operation
    let output_op = OperationBuilder::new("hw.output", location)
        .add_operands(&[result_value])
        .build()
        .map_err(|e| Error::MlirOperation(e))?;
    block.append_operation(output_op);

    region.append_block(block.as_raw());

    // Create the hw.module operation
    // We need to create a module type with one output port
    let output_port_name = MlirAttributeWrapper::string(ctx.context(), "out");

    let output_port = hwml_circt_sys::HWModulePort {
        name: output_port_name.as_raw(),
        type_: bit_type.as_raw(),
        dir: hwml_circt_sys::HWModulePortDirection_Output,
    };

    let module_universe = unsafe {
        let raw_type = hwml_circt_sys::hwModuleTypeGet(
            ctx.context().as_raw(),
            1, // one port
            &output_port as *const _,
        );
        MlirTypeWrapper::from_raw(raw_type)
    };

    // Create an empty parameters array (no module parameters)
    let empty_params = MlirAttributeWrapper::array(ctx.context(), &[]);

    let module_op = OperationBuilder::new("hw.module", location)
        .add_attributes(vec![
            create_named_attribute(
                ctx.context(),
                "sym_name",
                MlirAttributeWrapper::string(ctx.context(), "Top"),
            ),
            create_named_attribute(
                ctx.context(),
                "module_universe",
                MlirAttributeWrapper::type_attr(module_universe),
            ),
            create_named_attribute(ctx.context(), "parameters", empty_params),
        ])
        .add_regions(vec![region])
        .build()
        .map_err(|e| Error::MlirOperation(e))?;

    unsafe {
        let module_body = hwml_circt_sys::mlirModuleGetBody(mlir_module.as_raw());
        hwml_circt_sys::mlirBlockAppendOwnedOperation(module_body, module_op);
    }

    // Debug: print the MLIR module
    eprintln!("Generated MLIR:");
    unsafe {
        let module_op = hwml_circt_sys::mlirModuleGetOperation(mlir_module.as_raw());
        hwml_circt_sys::mlirOperationDump(module_op);
    }

    Ok(mlir_module)
}

/// Translate an Syntax expression to a CIRCT value.
fn translate_hsyntax_expr<'c, 'db>(
    ctx: &'c CirctContext,
    db: &'db dyn salsa::Database,
    location: MlirLocationWrapper,
    block: &MlirBlockWrapper,
    expr: &RcSyntax<'db>,
) -> Result<MlirValueWrapper> {
    let mlir_ctx = ctx.context();
    let bit_type = dialects::hw::bit_type(mlir_ctx);

    match &**expr {
        Syntax::Zero(_) => {
            // Create hw.constant 0 : i1
            let zero_attr = MlirAttributeWrapper::integer(bit_type, 0);
            let const_op = OperationBuilder::new("hw.constant", location)
                .add_attributes(vec![create_named_attribute(mlir_ctx, "value", zero_attr)])
                .add_results(&[bit_type])
                .build()
                .map_err(|e| Error::MlirOperation(e))?;
            block.append_operation(const_op);
            operation_result(const_op, 0).map_err(|e| Error::MlirOperation(e))
        }
        Syntax::One(_) => {
            // Create hw.constant 1 : i1
            let one_attr = MlirAttributeWrapper::integer(bit_type, 1);
            let const_op = OperationBuilder::new("hw.constant", location)
                .add_attributes(vec![create_named_attribute(mlir_ctx, "value", one_attr)])
                .add_results(&[bit_type])
                .build()
                .map_err(|e| Error::MlirOperation(e))?;
            block.append_operation(const_op);
            operation_result(const_op, 0).map_err(|e| Error::MlirOperation(e))
        }
        Syntax::HApplication(app) => {
            // Check if this is a binary operation application
            // Pattern: ((Op arg1) arg2)
            if let Syntax::HApplication(inner_app) = &*app.function {
                // Check if the inner function is a primitive
                if let Syntax::HPrim(prim) = &*inner_app.function {
                    let prim_name = prim.name.name(db);

                    // Handle $reg specially - it generates seq.compreg
                    if prim_name == "reg" {
                        // $reg clk input -> seq.compreg input, clk
                        // First argument (inner_app.argument) is the clock
                        // Second argument (app.argument) is the data input
                        let clk_i1 =
                            translate_hsyntax_expr(ctx, db, location, block, &inner_app.argument)?;
                        let input =
                            translate_hsyntax_expr(ctx, db, location, block, &app.argument)?;

                        // Convert i1 clock to !seq.clock type using seq.to_clock
                        let clock_type = dialects::seq::clock_type(mlir_ctx);
                        let to_clock_op = OperationBuilder::new("seq.to_clock", location)
                            .add_operands(&[clk_i1])
                            .add_results(&[clock_type])
                            .build()
                            .map_err(|e| Error::MlirOperation(e))?;
                        block.append_operation(to_clock_op);
                        let clk = operation_result(to_clock_op, 0)
                            .map_err(|e| Error::MlirOperation(e))?;

                        // Create seq.compreg operation with proper operandSegmentSizes
                        // seq.compreg has segments: [input, clk, reset, resetValue, initialValue]
                        // For a simple register without reset: [1, 1, 0, 0, 0]
                        let operand_sizes =
                            MlirAttributeWrapper::dense_i32_array(mlir_ctx, &[1, 1, 0, 0, 0]);
                        let reg_op = OperationBuilder::new("seq.compreg", location)
                            .add_operands(&[input, clk])
                            .add_results(&[bit_type])
                            .add_attributes(vec![create_named_attribute(
                                mlir_ctx,
                                "operandSegmentSizes",
                                operand_sizes,
                            )])
                            .build()
                            .map_err(|e| Error::MlirOperation(e))?;
                        block.append_operation(reg_op);
                        return operation_result(reg_op, 0).map_err(|e| Error::MlirOperation(e));
                    }

                    // Handle combinational binary operations
                    let op_name = match prim_name {
                        "and" => "comb.and",
                        "or" => "comb.or",
                        "xor" => "comb.xor",
                        _ => {
                            return Err(Error::UnsupportedConstruct(format!(
                                "Unsupported binary primitive: {}",
                                prim_name
                            )))
                        }
                    };

                    // Translate both arguments
                    let arg1 =
                        translate_hsyntax_expr(ctx, db, location, block, &inner_app.argument)?;
                    let arg2 = translate_hsyntax_expr(ctx, db, location, block, &app.argument)?;

                    // Create the operation
                    let bin_op = OperationBuilder::new(op_name, location)
                        .add_operands(&[arg1, arg2])
                        .add_results(&[bit_type])
                        .build()
                        .map_err(|e| Error::MlirOperation(e))?;
                    block.append_operation(bin_op);
                    return operation_result(bin_op, 0).map_err(|e| Error::MlirOperation(e));
                }

                return Err(Error::UnsupportedConstruct(format!(
                    "Unsupported nested application: {:?}",
                    inner_app.function
                )));
            } else if let Syntax::HPrim(prim) = &*app.function {
                let prim_name = prim.name.name(db);
                if prim_name == "not" {
                    // Unary NOT operation
                    let arg = translate_hsyntax_expr(ctx, db, location, block, &app.argument)?;

                    // NOT is implemented as XOR with 1
                    let one_attr = MlirAttributeWrapper::integer(bit_type, 1);
                    let const_op = OperationBuilder::new("hw.constant", location)
                        .add_attributes(vec![create_named_attribute(
                            ctx.context(),
                            "value",
                            one_attr,
                        )])
                        .add_results(&[bit_type])
                        .build()
                        .map_err(|e| Error::MlirOperation(e))?;
                    block.append_operation(const_op);
                    let one_val =
                        operation_result(const_op, 0).map_err(|e| Error::MlirOperation(e))?;

                    let xor_op = OperationBuilder::new("comb.xor", location)
                        .add_operands(&[arg, one_val])
                        .add_results(&[bit_type])
                        .build()
                        .map_err(|e| Error::MlirOperation(e))?;
                    block.append_operation(xor_op);
                    return operation_result(xor_op, 0).map_err(|e| Error::MlirOperation(e));
                }

                return Err(Error::UnsupportedConstruct(format!(
                    "Unsupported unary primitive: {}",
                    prim_name
                )));
            } else {
                Err(Error::UnsupportedConstruct(format!(
                    "Unsupported application: {:?}",
                    app
                )))
            }
        }
        Syntax::HVariable(var) => {
            // Get the block argument corresponding to this variable
            // Variables are indexed from the end (De Bruijn indices)
            let num_args = unsafe { hwml_circt_sys::mlirBlockGetNumArguments(block.as_raw()) };
            let var_index: usize = var.index.into();

            // De Bruijn index 0 is the most recently bound variable
            // which corresponds to the last block argument
            if var_index >= num_args as usize {
                return Err(Error::UnsupportedConstruct(format!(
                    "Variable index {} out of range (have {} arguments)",
                    var_index, num_args
                )));
            }

            // Convert De Bruijn index to block argument index
            // De Bruijn 0 -> last argument, De Bruijn 1 -> second-to-last, etc.
            let arg_index = (num_args as usize) - 1 - var_index;

            let arg_value = unsafe {
                let raw_value =
                    hwml_circt_sys::mlirBlockGetArgument(block.as_raw(), arg_index as isize);
                MlirValueWrapper::from_raw(raw_value)
            };

            Ok(arg_value)
        }
        Syntax::Splice(splice) => {
            // A splice ~t evaluates the meta-level term t and extracts the hardware value
            // In our case, t should be a Variable that refers to a lambda parameter
            // which is bound to a quoted hardware value
            use hwml_core::syn::Syntax;

            match &*splice.term {
                Syntax::Variable(var) => {
                    // The variable refers to a lambda parameter
                    // We need to get the corresponding block argument
                    let num_args =
                        unsafe { hwml_circt_sys::mlirBlockGetNumArguments(block.as_raw()) };
                    let var_index: usize = var.index.into();

                    if var_index >= num_args as usize {
                        return Err(Error::UnsupportedConstruct(format!(
                            "Splice variable index {} out of range (have {} arguments)",
                            var_index, num_args
                        )));
                    }

                    // Convert De Bruijn index to block argument index
                    let arg_index = (num_args as usize) - 1 - var_index;

                    let arg_value = unsafe {
                        let raw_value = hwml_circt_sys::mlirBlockGetArgument(
                            block.as_raw(),
                            arg_index as isize,
                        );
                        MlirValueWrapper::from_raw(raw_value)
                    };

                    Ok(arg_value)
                }
                _ => Err(Error::UnsupportedConstruct(format!(
                    "Unsupported splice term: {:?}",
                    splice.term
                ))),
            }
        }
        _ => Err(Error::UnsupportedConstruct(format!(
            "Unsupported Syntax variant: {:?}",
            expr
        ))),
    }
}
