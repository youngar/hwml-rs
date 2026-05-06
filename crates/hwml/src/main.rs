use clap::Parser;
use hwml_db::CompilerSession;
use hwml_vfs::{OsVfs, Vfs};
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
    #[arg(long = "skip-chec")]
    skip_check: bool,

    /// Use workspace mode with hwml.toml manifest.
    /// If set, loads entire workspace including dependencies.
    /// If not set, processes single file.
    #[arg(short = 'w', long = "workspace")]
    workspace: Option<PathBuf>,

    /// Input file to read (required if --workspace not specified).
    #[arg(short = 'f', long = "file")]
    file: Option<PathBuf>,
}

fn main() {
    let args = Args::parse();
    if args.verbose {
        println!("DEBUG {args:?}");
    }

    if args.core {
        run_core(args);
        return;
    }

    // Workspace mode or single-file mode
    if let Some(ref manifest_path) = args.workspace.clone() {
        run_workspace(args, manifest_path.clone());
    } else if let Some(ref file_path) = args.file.clone() {
        run_single_file(args, file_path.clone());
    } else {
        eprintln!("Error: Either --file or --workspace must be specified");
        std::process::exit(1);
    }
}

/// Run in workspace mode (loads entire workspace from hwml.toml)
fn run_workspace(args: Args, manifest_path: PathBuf) {
    if args.verbose {
        println!("Loading workspace from: {}", manifest_path.display());
    }

    // Load workspace declarations

    // Create Salsa database for workspace aggregation
    let mut workspace_db = hwml_db::HwmlDatabase::new();

    // Create ManifestPath Salsa input
    let manifest_path_input = hwml_db::ManifestPath::new(&mut workspace_db, manifest_path.clone());

    // Load entire workspace including dependencies
    // Returns both the stub table AND the file map with SourceFile instances
    let (workspace_decls, source_files) =
        hwml_db::workspace_declarations(&workspace_db, manifest_path_input);

    if args.verbose {
        println!("\nPhase 1: Workspace loaded");
        println!("  Total declarations: {}", workspace_decls.len());
        println!("  Source files cached: {}", source_files.len());
    }

    // Print all definitions
    println!("\nWorkspace Definitions:");
    println!("==================================================");
    for (name, stub) in workspace_decls.stubs() {
        println!("  {} ({:?})", name.to_string(&workspace_db), stub.kind);
    }

    // Elaborate with global stub table

    if args.verbose {
        println!("\nPhase 2: Elaboration (using global stub table)");
    }

    // Debug: Print database pointer and stub table
    eprintln!(
        "\n[DEBUG] Database pointer in Phase 1: {:p}",
        &workspace_db as *const _
    );

    // Test: Verify Word interning works
    let word1 = hwml_core::Word::new(&workspace_db, "Nat");
    let word2 = hwml_core::Word::new(&workspace_db, "Nat");
    eprintln!(
        "[DEBUG] Word interning test: Word::new('Nat') twice = {:?} and {:?}, equal: {}",
        word1,
        word2,
        word1 == word2
    );

    eprintln!("[DEBUG] STUB TABLE BEFORE ELABORATION:");
    eprintln!("[DEBUG] Total entries: {}", workspace_decls.len());
    for (name, stub) in workspace_decls.stubs() {
        let segments = name.segments(&workspace_db);
        eprintln!(
            "[DEBUG]   {:?} = {} ({:?}), segments: {:?}",
            name,
            name.to_string(&workspace_db),
            stub.kind,
            segments
                .iter()
                .map(|n| n.to_string(&workspace_db))
                .collect::<Vec<_>>()
        );
    }

    eprintln!("\n[DEBUG] CACHED SOURCE FILES:");
    for (path, sf) in source_files.iter().take(3) {
        eprintln!("[DEBUG]   SourceFile({:?}) -> {}", sf, path.display());
    }
    eprintln!(
        "[DEBUG] Total: {} cached source files\n",
        source_files.len()
    );

    // Load workspace to get access to files
    let workspace = match hwml_workspace::Workspace::load(manifest_path) {
        Ok(ws) => ws,
        Err(e) => {
            eprintln!("Error loading workspace: {}", e);
            std::process::exit(1);
        }
    };

    // Use the same database for elaboration as we used for harvesting!
    // This is critical - interned types (QualifiedName, etc.) must come from the same database
    let mut global_env = hwml_core::val::GlobalEnv::new();

    let mut total_elaborated = 0;
    let mut total_errors = 0;

    // Process each library in topological order
    for lib_name in &workspace.topo_order {
        let lib_manifest = &workspace.libraries[lib_name];

        if args.verbose {
            println!("\n  Elaborating library '{}'...", lib_name);
        }

        // LIBRARY-WIDE AGGREGATION: Collect all programs from all files in this library
        // This is CRITICAL for correct cross-file mutual recursion and SCC analysis
        let mut library_programs = Vec::new();

        for source_path in &lib_manifest.source_files {
            // Get the SAME SourceFile instance that was used during harvesting!
            // This is CRITICAL - using a new SourceFile would create new interned Names
            let source_file = match source_files.get(source_path) {
                Some(sf) => {
                    eprintln!(
                        "[DEBUG] Found cached SourceFile({:?}) for {}",
                        sf,
                        source_path.display()
                    );
                    *sf
                }
                None => {
                    eprintln!(
                        "    Warning: SourceFile not found for {}",
                        source_path.display()
                    );
                    continue;
                }
            };

            // Parse using the Salsa-tracked query - this returns the SAME Program instance
            // that was used during harvesting, with the SAME interned Names!
            let program = match hwml_db::parse_surface_program(&workspace_db, source_file) {
                Some(p) => p,
                None => {
                    eprintln!("    Warning: Failed to parse {}", source_path.display());
                    continue;
                }
            };

            library_programs.push((source_path.clone(), program));
        }

        // Elaborate the entire library at once with cross-file SCC analysis
        eprintln!(
            "[DEBUG] Elaborating library '{}' with {} files",
            lib_name,
            library_programs.len()
        );

        // Convert Vec<(PathBuf, Program)> to Vec<(PathBuf, &Program)>
        let library_programs_refs: Vec<(std::path::PathBuf, &hwml_surface::Program)> =
            library_programs
                .iter()
                .map(|(path, prog)| (path.clone(), prog))
                .collect();

        let result = hwml_elab::program::elab_library_with_sccs(
            &workspace_db,
            &mut global_env,
            &library_programs_refs,
            &workspace_decls,
        );

        total_elaborated += result.decls.len();
        total_errors += result.errors.len();

        if args.verbose && !result.decls.is_empty() {
            println!(
                "    Library '{}' - {} declarations elaborated",
                lib_name,
                result.decls.len()
            );
        }

        // Show errors (they already include file paths from the elaborator)
        for err in &result.errors {
            eprintln!("    Error: {:?}", err);
        }
    }

    // Phase 3: Summary
    // ================

    println!("\n");
    println!("Workspace compilation complete!");
    println!("================================");
    println!("  Libraries processed: {}", workspace.topo_order.len());
    println!("  Declarations elaborated: {}", total_elaborated);

    if total_errors > 0 {
        println!("  Errors: {}", total_errors);
        std::process::exit(1);
    } else {
        println!("  Errors: 0");
        println!("\nReady for Verilog emission.");
    }
}

/// Run in single-file mode (legacy behavior)
fn run_single_file(args: Args, file_path: PathBuf) {
    if args.verbose {
        println!("Processing single file: {}", file_path.display());
    }

    let path = file_path.canonicalize().unwrap();

    // Use VFS to load the file
    let session = CompilerSession::new();
    let mut vfs = OsVfs::new();
    let source_file = vfs
        .get_or_create_file(&session.db, &path)
        .expect("Failed to load file");
    let contents = source_file.text(&session.db);

    let parse_result = hwml_surface::parsing::parse(contents.as_bytes());

    let Some(program) = parse_result else {
        println!("Failed to parse");
        return;
    };

    // Create Salsa database
    let db = hwml_db::HwmlDatabase::new();

    let mut global = hwml_core::val::GlobalEnv::new();
    let result = hwml_elab::program::elab_program(&db, &mut global, &program);

    for decl in &result.decls {
        match decl {
            hwml_elab::program::ElaboratedDecl::Constant { name, info } => {
                println!("def {}:", name.to_string(&db));
                println!(
                    "  type:  {}",
                    hwml_core::syn::print::print_syntax_to_string(&db, &info.ty)
                );
                println!(
                    "  value: {}",
                    hwml_core::syn::print::print_syntax_to_string(&db, &info.value)
                );
            }
            hwml_elab::program::ElaboratedDecl::Primitive { name, info } => {
                println!("prim {}:", name.to_string(&db));
                println!(
                    "  type: {}",
                    hwml_core::syn::print::print_syntax_to_string(&db, &info.ty)
                );
            }
            hwml_elab::program::ElaboratedDecl::TypeConstructor { name, info } => {
                println!("inductive {} (level {})", name.to_string(&db), info.level);
            }
        }
    }

    for err in &result.errors {
        eprintln!("error: {:?}", err);
    }
}

fn run_core(args: Args) {
    let Some(file_path) = args.file else {
        eprintln!("Error: --file required for core mode");
        std::process::exit(1);
    };
    let path = file_path.canonicalize().unwrap();

    // Use VFS to load the file
    let session = CompilerSession::new();
    let mut vfs = OsVfs::new();
    let source_file = vfs
        .get_or_create_file(&session.db, &path)
        .expect("Failed to load file");
    let input = source_file.text(&session.db);

    let db = hwml_db::HwmlDatabase::new();

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
                hwml_core::syn::declaration::Declaration::PrimitiveDecl(p) => {
                    println!("  - prim {}: {:?}", p.name.name(&db).to_string(&db), p.ty);
                }
                hwml_core::syn::declaration::Declaration::ConstantDecl(c) => {
                    println!(
                        "  - const {}: {:?} = {:?}",
                        c.name.name(&db).to_string(&db),
                        c.ty,
                        c.value
                    );
                }
                hwml_core::syn::declaration::Declaration::TypeConstructorDecl(tc) => {
                    println!(
                        "  - tcon {} with {} data constructors",
                        tc.name.name(&db).to_string(&db),
                        tc.data_constructors.len()
                    );
                }
                hwml_core::syn::declaration::Declaration::MetavariableDecl(m) => {
                    println!("  - meta ?{}: {:?}", m.id.local_index, m.ty);
                }
            }
        }
    }

    // Display the parsed module
    println!("Module:");
    for decl in &module.declarations {
        match decl {
            hwml_core::syn::declaration::Declaration::PrimitiveDecl(p) => {
                print!("  prim ${} : ", p.name.name(&db).to_string(&db));
                hwml_core::syn::dump_syntax(&db, &p.ty);
            }
            hwml_core::syn::declaration::Declaration::ConstantDecl(c) => {
                print!("  const @{} : ", c.name.name(&db).to_string(&db));
                hwml_core::syn::dump_syntax(&db, &c.ty);
            }
            hwml_core::syn::declaration::Declaration::TypeConstructorDecl(tc) => {
                print!("  tcon @{} : ", tc.name.name(&db).to_string(&db));
                hwml_core::syn::dump_syntax(&db, &tc.universe);

                // Print data constructors
                for dcon in &tc.data_constructors {
                    print!("    dcon @{} : ", dcon.name.name(&db).to_string(&db));
                    hwml_core::syn::dump_syntax(&db, &dcon.full_type());
                }
            }
            hwml_core::syn::declaration::Declaration::MetavariableDecl(m) => {
                print!("  meta ?{} : ", m.id.local_index);
                hwml_core::syn::dump_syntax(&db, &m.ty);
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
    db: &hwml_db::HwmlDatabase,
    module: &hwml_core::syn::declaration::CompilationUnit,
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
