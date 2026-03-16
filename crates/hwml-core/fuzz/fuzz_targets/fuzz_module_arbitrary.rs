#![no_main]

use arbitrary::Arbitrary;
use hwml_core::common::{Index, UniverseLevel};
use hwml_core::declaration::{Declaration, Module};
use hwml_core::syn::{Application, Lambda, Pi, QualifiedName, Syntax, Universe, Variable};
use hwml_core::Database;
use libfuzzer_sys::fuzz_target;
use std::rc::Rc;

/// Generate a module using automatic Arbitrary derivation for the components that support it.
/// This approach uses Arbitrary for the basic building blocks and manually constructs
/// the types that contain QualifiedName.
#[derive(Arbitrary, Debug)]
struct FuzzInput {
    // Use arbitrary generation for types that support it
    variables: Vec<Variable>,
    universes: Vec<Universe>,
    indices: Vec<Index>,
    universe_levels: Vec<UniverseLevel>,

    // Raw data for manual generation
    data: Vec<u8>,
}

impl FuzzInput {
    fn generate_constant_id<'db>(&self, db: &'db Database, index: usize) -> QualifiedName<'db> {
        let names = [
            "Bool", "Nat", "Type", "Unit", "List", "Vec", "Option", "Result", "zero", "succ",
            "true", "false", "nil", "cons", "some", "none", "left", "right", "pair", "fst", "snd",
            "id", "const", "comp", "x", "y", "z", "f", "g", "h", "a", "b", "c", "n", "m", "k",
        ];
        let name_index = self.data.get(index).unwrap_or(&0) % names.len() as u8;
        QualifiedName::from_str(db, names[name_index as usize])
    }

    fn generate_syntax<'db>(&self, db: &'db Database, index: usize, depth: u8) -> Rc<Syntax<'db>> {
        if depth > 3 || index >= self.data.len() {
            // Base case: return a simple type
            let universe = self
                .universes
                .get(index % self.universes.len().max(1))
                .cloned()
                .unwrap_or_else(|| Universe::new(UniverseLevel::new(0)));
            return Rc::new(Syntax::Universe(universe));
        }

        let choice = self.data.get(index).unwrap_or(&0) % 6;
        match choice {
            0 => {
                // Universe
                let universe = self
                    .universes
                    .get(index % self.universes.len().max(1))
                    .cloned()
                    .unwrap_or_else(|| Universe::new(UniverseLevel::new(0)));
                Rc::new(Syntax::Universe(universe))
            }
            1 => {
                // Variable
                let variable = self
                    .variables
                    .get(index % self.variables.len().max(1))
                    .cloned()
                    .unwrap_or_else(|| Variable::new(Index::new(0)));
                Rc::new(Syntax::Variable(variable))
            }
            2 => {
                // Pi type
                let source = self.generate_syntax(db, index + 1, depth + 1);
                let target = self.generate_syntax(db, index + 2, depth + 1);
                Rc::new(Syntax::Pi(Pi::new(source, target)))
            }
            3 => {
                // Lambda
                let body = self.generate_syntax(db, index + 1, depth + 1);
                Rc::new(Syntax::Lambda(Lambda::new(body)))
            }
            4 => {
                // Application
                let function = self.generate_syntax(db, index + 1, depth + 1);
                let argument = self.generate_syntax(db, index + 2, depth + 1);
                Rc::new(Syntax::Application(Application::new(function, argument)))
            }
            _ => {
                // Constant
                let constant_id = self.generate_constant_id(db, index);
                Syntax::constant_rc(constant_id)
            }
        }
    }

    fn generate_module<'db>(&self, db: &'db Database) -> Module<'db> {
        let mut module = Module::new();
        let size = (self.data.get(0).unwrap_or(&5) % 10).max(1) as usize;

        for i in 0..size {
            let name = self.generate_constant_id(db, i);
            let ty = self.generate_syntax(db, i * 3, 0);

            let decl_type = self.data.get(i + 100).unwrap_or(&0) % 2;
            let declaration = match decl_type {
                0 => {
                    // Constant
                    let value = self.generate_syntax(db, i * 3 + 1, 0);
                    Declaration::constant(name, ty, value)
                }
                _ => {
                    // Primitive
                    Declaration::primitive(name, ty)
                }
            };

            module.add_declaration(declaration);
        }

        module
    }
}

fuzz_target!(|input: FuzzInput| {
    let db = Database::new();
    let module = input.generate_module(&db);

    // Test module operations
    let declarations = &module.declarations;

    // Test accessing declarations
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
            }
            Declaration::Metavariable(m) => {
                let _id = m.id;
                let _ty = &m.ty;
            }
        }
    }

    // Test module reconstruction
    let new_module = Module::from_declarations(declarations.clone());
    assert_eq!(new_module.declarations.len(), declarations.len());

    // Test iteration consistency
    let count1 = module.declarations.len();
    let count2 = module.declarations.len();
    assert_eq!(count1, count2);
});
