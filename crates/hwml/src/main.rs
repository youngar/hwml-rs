use clap::Parser;
use std::fs;
use std::path::PathBuf;

#[derive(Parser, Debug)]
#[clap(author = "Andrew Young", version, about)]
/// Application configuration
struct Args {
    /// Whether to be verbose.
    #[arg(short = 'v')]
    verbose: bool,

    /// Whether to run in "core mode" or "surface mode".
    #[arg(short = 'c', long = "core")]
    core: bool,

    /// Emit MLIR IR (requires --core and CIRCT feature).
    #[arg(long = "emit-mlir")]
    emit_mlir: bool,

    /// Emit Verilog (requires --core and CIRCT feature).
    #[arg(long = "emit-verilog")]
    emit_verilog: bool,

    /// Skip type checking in core mode.
    #[arg(long = "skip-check")]
    skip_check: bool,

    /// Input file to read.
    #[arg(short = 'f', long = "file")]
    file: PathBuf,
}

fn main() {
    let args = Args::parse();
    if args.verbose {
        println!("DEBUG {args:?}");
    }

    if args.core {
        return run_core(args);
    }

    let path = args.file.canonicalize().unwrap();
    let contents = fs::read_to_string(&path).expect("Should have been able to read the file");
    let parse_result = hwml_surface::parsing::parse(contents.as_bytes());

    let Some(program) = parse_result else {
        println!("Failed to parse");
        return;
    };

    println!("=========================");
    println!("AST");
    println!("=========================");
    println!("{program:#?}");

    let db = hwml_core::Database::new();

    let global_env = match hwml_elab::elab_program(&db, &program) {
        Ok(g) => g,
        Err(e) => {
            println!("Failed to elaborate: {:#?}", e);
            return;
        }
    };

    // println!("=========================");
    // println!("Elaborated");
    // println!("=========================");
    // for decl in module.declarations() {
    //     println!("{decl:?}");
    // }
}

fn run_core(args: Args) {
    let path = args.file.canonicalize().unwrap();
    let input = fs::read_to_string(&path).expect("Should have been able to read the file");

    let db = hwml_core::Database::new();

    // Parse as a module instead of a single expression
    let module = match hwml_core::syn::parse_module(&db, &input) {
        Ok(m) => m,
        Err(e) => {
            println!("parse error: {:#?}", e);
            return;
        }
    };

    if args.verbose {
        println!(
            "Parsed module with {} declarations:",
            module.declarations.len()
        );
        for decl in &module.declarations {
            match decl {
                hwml_core::declaration::Declaration::Primitive(p) => {
                    println!("  - prim {}: {:?}", p.name.name(&db), p.ty);
                }
                hwml_core::declaration::Declaration::Constant(c) => {
                    println!("  - const {}: {:?} = {:?}", c.name.name(&db), c.ty, c.value);
                }
                hwml_core::declaration::Declaration::TypeConstructor(tc) => {
                    println!(
                        "  - tcon {} with {} data constructors",
                        tc.name.name(&db),
                        tc.data_constructors.len()
                    );
                }
            }
        }
    }

    // Display the parsed module
    println!("Module:");
    for decl in &module.declarations {
        match decl {
            hwml_core::declaration::Declaration::Primitive(p) => {
                print!("  prim ${} : ", p.name.name(&db));
                hwml_core::syn::dump_syntax(&db, &p.ty);
            }
            hwml_core::declaration::Declaration::Constant(c) => {
                print!("  const @{} : ", c.name.name(&db));
                hwml_core::syn::dump_syntax(&db, &c.ty);
            }
            hwml_core::declaration::Declaration::TypeConstructor(tc) => {
                print!("  tcon @{} : ", tc.name.name(&db));
                hwml_core::syn::dump_syntax(&db, &tc.universe);

                // Print data constructors
                for dcon in &tc.data_constructors {
                    print!("    dcon @{} : ", dcon.name.name(&db));
                    hwml_core::syn::dump_syntax(&db, &dcon.full_type());
                }
            }
        }
    }

    // If CIRCT emission is requested, emit all hardware constants as HW modules
    #[cfg(feature = "circt")]
    if args.emit_mlir || args.emit_verilog {
        emit_circt_module(&db, &module, args.emit_mlir, args.emit_verilog);
    }
}

#[cfg(feature = "circt")]
fn emit_circt_module(
    db: &hwml_core::Database,
    module: &hwml_core::declaration::Module,
    emit_mlir: bool,
    emit_verilog: bool,
) {
    // Create CIRCT context
    let ctx = match hwml_circt::CirctContext::new() {
        Ok(c) => c,
        Err(e) => {
            eprintln!("Error: Failed to create CIRCT context: {}", e);
            std::process::exit(1);
        }
    };

    // Translate the entire module to MLIR
    // This will create a HW module for each hardware constant
    let mlir_module = match hwml_circt::translate::translate_module(&ctx, db, module) {
        Ok(m) => m,
        Err(e) => {
            eprintln!("Error: Failed to translate module to MLIR: {}", e);
            std::process::exit(1);
        }
    };

    // Verify the module
    if !mlir_module.verify() {
        eprintln!("Error: Generated MLIR module failed verification");
        std::process::exit(1);
    }

    println!("Generated MLIR:");
    println!("{}", mlir_module.to_string());

    // Emit MLIR if requested
    if emit_mlir {
        println!("╔════════════════════════════════════════════════════════════╗");
        println!("║    MLIR IR                                                 ║");
        println!("╚════════════════════════════════════════════════════════════╝");
        println!();
        println!("{}", mlir_module.to_string());
        println!();
    }

    // Emit Verilog if requested
    if emit_verilog {
        // Use lower_and_export_verilog to handle seq dialect lowering automatically
        match hwml_circt::export::lower_and_export_verilog(&mlir_module) {
            Ok(verilog) => {
                println!("╔════════════════════════════════════════════════════════════╗");
                println!("║    Verilog                                                 ║");
                println!("╚════════════════════════════════════════════════════════════╝");
                println!();
                println!("{}", verilog);
            }
            Err(e) => {
                eprintln!("Error: Failed to export Verilog: {}", e);
                std::process::exit(1);
            }
        }
    }
}
