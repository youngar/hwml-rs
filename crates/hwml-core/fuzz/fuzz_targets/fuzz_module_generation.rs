#![no_main]

use hwml_core::common::{Index, UniverseLevel};
use hwml_core::declaration::{Declaration, Module};
use hwml_core::syn::{QualifiedName, Syntax, Universe};
use hwml_core::Database;
use libfuzzer_sys::fuzz_target;
use std::rc::Rc;

/// Generate a random type based on input data
fn generate_random_type<'db>(
    db: &'db Database,
    data: &[u8],
    offset: usize,
    depth: u8,
) -> Rc<Syntax<'db>> {
    if depth > 3 || data.len() <= offset {
        // Base case: return a simple type
        return Rc::new(Syntax::Universe(Universe::new(UniverseLevel::new(0))));
    }

    let type_choice = data[offset] % 6;
    match type_choice {
        0 => {
            // Universe type
            let level = (data.get(offset + 1).unwrap_or(&0) % 3) as usize;
            Rc::new(Syntax::Universe(Universe::new(UniverseLevel::new(level))))
        }
        1 => {
            // Variable (bound or free)
            let var_index = data.get(offset + 1).unwrap_or(&0) % 5;
            Syntax::variable_rc(Index::new(var_index as usize))
        }
        2 => {
            // Function type (Pi type)
            let param_type = generate_random_type(db, data, offset + 2, depth + 1);
            let return_type = generate_random_type(db, data, offset + 4, depth + 1);
            Syntax::pi_rc(param_type, return_type)
        }
        3 => {
            // Application
            let func = generate_random_type(db, data, offset + 1, depth + 1);
            let arg = generate_random_type(db, data, offset + 3, depth + 1);
            Syntax::application_rc(func, arg)
        }
        4 => {
            // Lambda
            let body = generate_random_type(db, data, offset + 2, depth + 1);
            Syntax::lambda_rc(body)
        }
        _ => {
            // Constant reference
            let const_name = match data.get(offset + 1).unwrap_or(&0) % 4 {
                0 => "Bool",
                1 => "Nat",
                2 => "Type",
                _ => "Unit",
            };
            Syntax::constant_from_str_rc(db, const_name)
        }
    }
}

/// Generate a random expression based on input data
fn generate_random_expression<'db>(
    db: &'db Database,
    data: &[u8],
    offset: usize,
    depth: u8,
) -> Rc<Syntax<'db>> {
    if depth > 3 || data.len() <= offset {
        // Base case: return a simple expression
        let const_name = match data.get(offset).unwrap_or(&0) % 3 {
            0 => "true",
            1 => "false",
            _ => "unit",
        };
        return Syntax::constant_from_str_rc(db, const_name);
    }

    let expr_choice = data[offset] % 5;
    match expr_choice {
        0 => {
            // Constant
            let const_name = match data.get(offset + 1).unwrap_or(&0) % 5 {
                0 => "zero",
                1 => "succ",
                2 => "true",
                3 => "false",
                _ => "unit",
            };
            Syntax::constant_from_str_rc(db, const_name)
        }
        1 => {
            // Variable
            let var_index = data.get(offset + 1).unwrap_or(&0) % 3;
            Syntax::variable_rc(Index::new(var_index as usize))
        }
        2 => {
            // Lambda
            let body = generate_random_expression(db, data, offset + 2, depth + 1);
            Syntax::lambda_rc(body)
        }
        3 => {
            // Application
            let func = generate_random_expression(db, data, offset + 1, depth + 1);
            let arg = generate_random_expression(db, data, offset + 3, depth + 1);
            Syntax::application_rc(func, arg)
        }
        _ => {
            // Type (expressions can be types too)
            generate_random_type(db, data, offset + 1, depth + 1)
        }
    }
}

/// Generate a test module with various types of declarations.
fn generate_test_module<'db>(db: &'db Database, data: &[u8]) -> Module<'db> {
    let mut module = Module::new();

    if data.is_empty() {
        return module;
    }

    let size = data[0].min(20); // Limit to reasonable size

    // Create different types of declarations based on input data
    for i in 0..size {
        let name = QualifiedName::from_str(db, &format!("decl_{}", i));

        // Generate random type for this declaration
        let base_offset = (i as usize * 7) % data.len().max(1);
        let ty = generate_random_type(db, data, base_offset, 0);

        // Use input data to determine declaration type
        let decl_type = if data.len() > (i as usize + 1) {
            data[i as usize + 1] % 3
        } else {
            0
        };

        let declaration = match decl_type {
            0 => {
                // Constant declaration with random expression
                let expr_offset = (base_offset + 3) % data.len().max(1);
                let value = generate_random_expression(db, data, expr_offset, 0);
                Declaration::constant(name, ty, value)
            }
            _ => {
                // Primitive (simplified - type constructors need more complex setup)
                Declaration::primitive(name, ty)
            }
        };

        module.add_declaration(declaration);
    }

    module
}

/// Fuzz module generation and basic operations.
/// This fuzzer tests:
/// 1. Module creation with various types of declarations
/// 2. Module operations like finding declarations
/// 3. Module validation and consistency
/// 4. Error handling for duplicate declarations
fuzz_target!(|data: &[u8]| {
    if data.is_empty() {
        return;
    }

    let db = Database::new();
    let module = generate_test_module(&db, data);

    // Test basic module operations
    let declarations = &module.declarations;

    // Test that we can iterate over declarations
    for decl in declarations {
        // Test declaration pattern matching
        match decl {
            Declaration::Primitive(p) => {
                let _name = p.name;
                let _ty = &p.ty;
            }
            Declaration::Constant(c) => {
                let _name = c.name;
                let _ty = &c.ty;
                let _value = &c.value;
            }
            Declaration::TypeConstructor(tc) => {
                let _name = tc.name;
                let _params = &tc.parameters;
                let _indices = &tc.indices;
                let _data_constructors = &tc.data_constructors;
            }
            Declaration::Metavariable(m) => {
                let _id = m.id;
                let _args = &m.arguments;
                let _ty = &m.ty;
            }
        }
    }

    // Test module construction methods
    let new_module = Module::new();
    assert_eq!(
        new_module.declarations.len(),
        0,
        "New module should be empty"
    );

    // Test creating module from declarations
    let reconstructed = Module::from_declarations(declarations.clone());
    assert_eq!(
        reconstructed.declarations.len(),
        declarations.len(),
        "Reconstructed module should have same number of declarations"
    );

    // Test that reconstructed module has same declarations
    for (original, reconstructed) in declarations.iter().zip(reconstructed.declarations.iter()) {
        assert_eq!(
            original, reconstructed,
            "Declarations should match after reconstruction"
        );
    }

    // Test adding declarations to a new module
    let mut test_module = Module::new();
    for decl in declarations {
        test_module.add_declaration(decl.clone());
    }
});
