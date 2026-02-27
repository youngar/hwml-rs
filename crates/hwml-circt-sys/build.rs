use std::env;
use std::path::PathBuf;
use std::process::Command;

fn main() {
    println!("cargo:rerun-if-env-changed=CIRCT_SYS_PREFIX");
    println!("cargo:rerun-if-env-changed=CIRCT_SYS_LIB_PREFIX");
    println!("cargo:rerun-if-env-changed=MLIR_SYS_PREFIX");
    println!("cargo:rerun-if-changed=wrapper.h");

    let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());

    // Determine CIRCT installation path using priority order:
    // 1. CIRCT_SYS_PREFIX (Nix or manual override)
    // 2. llvm-config (Homebrew/system package manager)
    // 3. Common installation paths
    // 4. Build from source (if feature enabled)
    let circt_root = find_circt_installation();

    // Configure linking (may use separate lib directory in Nix)
    configure_linking(&circt_root);

    // Generate Rust bindings
    generate_bindings(&circt_root, &out_dir);
}

fn find_circt_installation() -> PathBuf {
    // Priority 1: Explicit CIRCT_SYS_PREFIX (Nix or manual)
    if let Ok(prefix) = env::var("CIRCT_SYS_PREFIX") {
        println!(
            "cargo:warning=Using CIRCT from CIRCT_SYS_PREFIX: {}",
            prefix
        );
        return PathBuf::from(prefix);
    }

    // Priority 2: Try llvm-config (common with Homebrew)
    if let Some(llvm_prefix) = try_llvm_config() {
        let circt_path = llvm_prefix.join("include/circt");
        if circt_path.exists() {
            println!(
                "cargo:warning=Found CIRCT via llvm-config: {}",
                llvm_prefix.display()
            );
            return llvm_prefix;
        }
    }

    // Priority 3: Check common installation paths
    let common_paths = [
        "/opt/homebrew", // Homebrew on Apple Silicon
        "/usr/local",    // Homebrew on Intel Mac / Linux
        "/usr",          // System package manager
    ];

    for path in &common_paths {
        let circt_include = PathBuf::from(path).join("include/circt-c");
        if circt_include.exists() {
            println!("cargo:warning=Found CIRCT at: {}", path);
            return PathBuf::from(path);
        }
    }

    // Priority 4: Build from source (if feature enabled)
    #[cfg(feature = "build-from-source")]
    {
        println!(
            "cargo:warning=CIRCT not found. Building from source (this will take 30+ minutes)..."
        );
        return build_from_source();
    }

    #[cfg(not(feature = "build-from-source"))]
    {
        panic!(
            "CIRCT not found!\n\
            \n\
            Please install CIRCT using one of these methods:\n\
            \n\
            1. Homebrew (macOS/Linux):\n\
               brew install llvm circt\n\
            \n\
            2. Nix:\n\
               nix develop\n\
            \n\
            3. Manual installation:\n\
               Set CIRCT_SYS_PREFIX=/path/to/circt\n\
            \n\
            4. Build from source:\n\
               cargo build --features build-from-source\n\
               (Warning: 30+ minute build time)\n"
        );
    }
}

fn try_llvm_config() -> Option<PathBuf> {
    // Try llvm-config to find LLVM installation
    let output = Command::new("llvm-config").arg("--prefix").output().ok()?;

    if output.status.success() {
        let prefix = String::from_utf8(output.stdout).ok()?;
        Some(PathBuf::from(prefix.trim()))
    } else {
        None
    }
}

#[cfg(feature = "build-from-source")]
fn build_from_source() -> PathBuf {
    // Build CIRCT from git submodule using CMake
    cmake::Config::new("../../external/circt")
        .define("CIRCT_INCLUDE_TOOLS", "ON")
        .define("MLIR_ENABLE_BINDINGS_PYTHON", "OFF")
        .build()
}

fn configure_linking(circt_root: &PathBuf) {
    // In Nix, libraries may be in a separate output (CIRCT_SYS_LIB_PREFIX)
    // Otherwise, they're in circt_root/lib
    let lib_dir = if let Ok(lib_prefix) = env::var("CIRCT_SYS_LIB_PREFIX") {
        PathBuf::from(lib_prefix).join("lib")
    } else {
        circt_root.join("lib")
    };

    println!("cargo:rustc-link-search=native={}", lib_dir.display());

    // Also add MLIR and LLVM library paths if they're separate (Nix case)
    // Try MLIR_SYS_LIB_PREFIX first, fall back to MLIR_SYS_PREFIX/lib
    if let Ok(mlir_lib_prefix) = env::var("MLIR_SYS_LIB_PREFIX") {
        let mlir_lib = PathBuf::from(mlir_lib_prefix).join("lib");
        if mlir_lib.exists() {
            println!("cargo:rustc-link-search=native={}", mlir_lib.display());
        }
    } else if let Ok(mlir_prefix) = env::var("MLIR_SYS_PREFIX") {
        let mlir_lib = PathBuf::from(mlir_prefix).join("lib");
        if mlir_lib.exists() {
            println!("cargo:rustc-link-search=native={}", mlir_lib.display());
        }
    }

    // Try LLVM_SYS_LIB_PREFIX first, fall back to LLVM_SYS_PREFIX/lib
    if let Ok(llvm_lib_prefix) = env::var("LLVM_SYS_LIB_PREFIX") {
        let llvm_lib = PathBuf::from(llvm_lib_prefix).join("lib");
        if llvm_lib.exists() {
            println!("cargo:rustc-link-search=native={}", llvm_lib.display());
        }
    } else if let Ok(llvm_prefix) = env::var("LLVM_SYS_PREFIX") {
        let llvm_lib = PathBuf::from(llvm_prefix).join("lib");
        if llvm_lib.exists() {
            println!("cargo:rustc-link-search=native={}", llvm_lib.display());
        }
    }

    // CIRCT from Nix provides static libraries (.a files)
    // We need to link the specific CAPI libraries we use
    // Note: Order matters for static linking - dependencies must come after dependents

    // Core CIRCT C API libraries we need
    let circt_libs = [
        "CIRCTCAPIExportVerilog", // For Verilog export
        "CIRCTCAPIConversion",    // Conversion passes C API (LowerSeqToSV, etc.)
        "CIRCTCAPIHW",            // HW dialect C API
        "CIRCTCAPIComb",          // Comb dialect C API
        "CIRCTCAPISeq",           // Seq dialect C API
        "CIRCTCAPISupport",       // CIRCT support
        // Core CIRCT dialect libraries (needed for dialect constructors and operations)
        "CIRCTExportVerilog",
        "CIRCTSeqToSV",       // Seq to SV lowering
        "CIRCTSeqTransforms", // Seq transforms
        "CIRCTHW",
        "CIRCTComb",
        "CIRCTSeq",
        "CIRCTSV",    // SystemVerilog dialect
        "CIRCTLTL",   // LTL dialect
        "CIRCTEmit",  // Emit dialect
        "CIRCTVerif", // Verification dialect
        "CIRCTOM",    // Object Model dialect
        "CIRCTDebug", // Debug dialect
        "CIRCTSupport",
    ];

    for lib in &circt_libs {
        println!("cargo:rustc-link-lib=static={}", lib);
    }

    // Link MLIR libraries that our C++ code depends on
    // These are needed because our C++ wrappers use MLIR/LLVM APIs
    // Based on Moore project's linking approach
    let mlir_libs = [
        "MLIRCAPIIR",                          // MLIR C API
        "MLIRSupport",                         // MLIR support
        "MLIRIR",                              // MLIR IR
        "MLIRParser",                          // MLIR parser
        "MLIRPass",                            // Pass infrastructure
        "MLIRRewrite",                         // MLIR rewrite patterns
        "MLIRTransforms",                      // MLIR transforms (for ConversionTarget, etc.)
        "MLIRTransformUtils",                  // Transform utilities
        "MLIRAnalysis",                        // MLIR analysis
        "MLIRArithDialect",                    // Arithmetic dialect
        "MLIRArithValueBoundsOpInterfaceImpl", // Arith value bounds
        "MLIRFuncDialect",                     // Function dialect
        "MLIRFunctionInterfaces",              // Function interfaces
        "MLIRInferTypeOpInterface",            // Type inference interface
        "MLIRInferIntRangeInterface",          // Integer range inference
        "MLIRInferIntRangeCommon",             // Integer range inference common
        "MLIRPDLDialect",                      // PDL dialect
        "MLIRPDLInterpDialect",                // PDL interpreter dialect
        "MLIRPDLToPDLInterp",                  // PDL to PDL interp conversion
        "MLIRRewritePDL",                      // PDL rewrite support
        "MLIRSideEffectInterfaces",            // Side effect interfaces
        "MLIRCallInterfaces",                  // Call interfaces
        "MLIRControlFlowInterfaces",           // Control flow interfaces (RegionBranchOpInterface)
        "MLIRBytecodeOpInterface",             // Bytecode op interface
        "MLIRBytecodeReader",                  // Bytecode reader
        "MLIRBytecodeWriter",                  // Bytecode writer
        "MLIRAsmParser",                       // ASM parser
    ];

    for lib in &mlir_libs {
        println!("cargo:rustc-link-lib=static={}", lib);
    }

    // Link LLVM libraries
    let llvm_libs = [
        "LLVMSupport",
        "LLVMDemangle",
        "LLVMCore",
        "LLVMBinaryFormat",
        "LLVMBitstreamReader",
        "LLVMRemarks",
        "LLVMTargetParser",
    ];

    for lib in &llvm_libs {
        println!("cargo:rustc-link-lib=static={}", lib);
    }

    // Link C++ standard library (needed for C++ code)
    if cfg!(target_os = "macos") {
        println!("cargo:rustc-link-lib=dylib=c++");
    } else if cfg!(target_os = "linux") {
        println!("cargo:rustc-link-lib=dylib=stdc++");
    }

    // On macOS, we may need to set rpath for any dynamic dependencies
    if cfg!(target_os = "macos") {
        println!("cargo:rustc-link-arg=-Wl,-rpath,{}", lib_dir.display());
    }
}

fn generate_bindings(circt_root: &PathBuf, out_dir: &PathBuf) {
    let mut include_dirs = vec![];

    // Add CIRCT includes
    // Note: Nix CIRCT dev output has a nested include/include structure
    let circt_include = circt_root.join("include");
    if circt_include.join("include").exists() {
        // Nix structure: include/include/circt-c/
        include_dirs.push(circt_include.join("include"));
    } else if circt_include.exists() {
        // Standard structure: include/circt-c/
        include_dirs.push(circt_include);
    }

    // Add MLIR includes if available (from MLIR_SYS_PREFIX)
    if let Ok(mlir_prefix) = env::var("MLIR_SYS_PREFIX") {
        let mlir_include = PathBuf::from(mlir_prefix).join("include");
        if mlir_include.exists() {
            include_dirs.push(mlir_include);
        }
    }

    // Add LLVM includes if available (from LLVM_SYS_PREFIX)
    if let Ok(llvm_prefix) = env::var("LLVM_SYS_PREFIX") {
        let llvm_include = PathBuf::from(llvm_prefix).join("include");
        if llvm_include.exists() {
            include_dirs.push(llvm_include);
        }
    }

    // Build bindgen with all include paths
    let mut builder = bindgen::Builder::default().header("wrapper.h");

    for dir in &include_dirs {
        println!("cargo:warning=Adding include path: {}", dir.display());
        builder = builder.clang_arg(format!("-I{}", dir.display()));
    }

    let bindings = builder
        // Parse MLIR/CIRCT types
        .allowlist_type("Mlir.*")
        .allowlist_type("CIRCT.*")
        .allowlist_type("HW.*") // HW dialect types
        .allowlist_function("mlir.*")
        .allowlist_function("circt.*")
        .allowlist_function("hw.*") // HW dialect functions
        .allowlist_function("seq.*") // Seq dialect functions (clock types, etc.)
        // Generate bindings
        .parse_callbacks(Box::new(bindgen::CargoCallbacks::new()))
        .generate()
        .expect("Unable to generate CIRCT bindings");

    bindings
        .write_to_file(out_dir.join("bindings.rs"))
        .expect("Couldn't write bindings!");
}
