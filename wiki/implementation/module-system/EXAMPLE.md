# Workspace Aggregation Example

**Date:** 2026-05-04  
**Purpose:** Complete working example of the workspace aggregation system

This document shows a complete, realistic example of using HWML's workspace aggregation.

---

## 📁 **Project Structure**

```
example-project/
├── hwml.toml                    # Main project manifest
├── src/
│   ├── main.hwml                # Entry point
│   ├── uart.hwml                # UART implementation
│   └── util.hwml                # Utilities
│
├── deps/
│   ├── hwml-fifo/               # Dependency 1
│   │   ├── hwml.toml
│   │   └── src/
│   │       └── fifo.hwml
│   │
│   └── hwml-common/             # Dependency 2
│       ├── hwml.toml
│       └── src/
│           └── types.hwml
│
└── tests/
    └── test_main.rs             # Rust test using the workspace
```

---

## 📝 **File Contents**

### **Main Project: `hwml.toml`**

```toml
[library]
name = "example_project"
edition = 1

[dependencies]
fifo = { path = "deps/hwml-fifo" }
common = { path = "deps/hwml-common" }
```

### **Main Project: `src/main.hwml`**

```hwml
// No imports needed! All dependencies are globally visible

namespace Main {
    // Use types from common library
    open Common.Types
    
    // Use FIFO from fifo library
    // Explicit monomorphization: we name the concrete Verilog module
    def MyFifo_32 = Fifo.Fifo_32
    
    // Our main module
    def TopLevel : Bit8 -> Bit8 = input =>
        // Process through UART
        let uart_out = Uart.Tx input in
        uart_out
}
```

### **Main Project: `src/uart.hwml`**

```hwml
namespace Uart {
    // Parametric definition (compile-time only, NOT Verilog)
    def UartConfig (baudRate : Nat) = {
        baud = baudRate,
        bits = 8
    }
    
    // Concrete configurations (WILL be lowered to Verilog)
    def Config_9600 = UartConfig 9600
    def Config_115200 = UartConfig 115200
    
    // UART transmitter (concrete, WILL be Verilog)
    def Tx : Bit8 -> Bit8 = input =>
        // ... implementation ...
        input
}
```

### **Main Project: `src/util.hwml`**

```hwml
namespace Main.Util {
    // Helper functions
    def clamp : Nat -> Nat -> Nat = min => max => value =>
        if value < min then min
        else if value > max then max
        else value
}
```

### **Dependency 1: `deps/hwml-fifo/hwml.toml`**

```toml
[library]
name = "fifo"
edition = 1
```

### **Dependency 1: `deps/hwml-fifo/src/fifo.hwml`**

```hwml
namespace Fifo {
    // Parametric FIFO (compile-time only)
    def Fifo (width : Nat) (depth : Nat) = {
        dataWidth = width,
        fifoDepth = depth,
        // ... implementation ...
    }
    
    // Concrete FIFOs (lowered to Verilog)
    def Fifo_8 = Fifo 8 16
    def Fifo_16 = Fifo 16 32
    def Fifo_32 = Fifo 32 64
}
```

### **Dependency 2: `deps/hwml-common/hwml.toml`**

```toml
[library]
name = "common"
edition = 1
```

### **Dependency 2: `deps/hwml-common/src/types.hwml`**

```hwml
namespace Common.Types {
    // Common type definitions
    def Bit8 : Type = ...
    def Bit16 : Type = ...
    def Bit32 : Type = ...
    
    // Standard widths
    def Width8 : Nat = 8
    def Width16 : Nat = 16
    def Width32 : Nat = 32
}
```

---

## 🦀 **Rust Test Code**

### **File: `tests/test_main.rs`**

```rust
use hwml_db::{workspace_declarations, HwmlDatabase};
use std::path::PathBuf;

#[test]
fn test_workspace_loading() {
    let db = HwmlDatabase::new();
    
    // Load entire workspace from manifest
    let manifest_path = PathBuf::from("example-project/hwml.toml");
    let workspace_decls = workspace_declarations(&db, manifest_path);
    
    // Verify we loaded declarations from all libraries
    assert!(workspace_decls.len() > 0, "Should have loaded declarations");
    
    // Count concrete vs parametric
    let concrete_count = workspace_decls.concrete_definitions().count();
    let parametric_count = workspace_decls.parametric_definitions().count();
    
    println!("Loaded workspace:");
    println!("  Concrete definitions (Verilog): {}", concrete_count);
    println!("  Parametric definitions (compile-time): {}", parametric_count);
    
    // Expected concrete definitions:
    // - Main.MyFifo_32 (from main.hwml)
    // - Main.TopLevel (from main.hwml)
    // - Uart.Config_9600 (from uart.hwml)
    // - Uart.Config_115200 (from uart.hwml)
    // - Uart.Tx (from uart.hwml)
    // - Fifo.Fifo_8 (from fifo library)
    // - Fifo.Fifo_16 (from fifo library)
    // - Fifo.Fifo_32 (from fifo library)
    // - Common.Types.* (from common library)
    
    assert!(concrete_count >= 8, "Expected at least 8 concrete definitions");
}

#[test]
fn test_incremental_compilation() {
    use hwml_db::{file_declarations, SourceFile};
    use std::sync::Arc;

    let db = HwmlDatabase::new();

    // Create a source file
    let path = PathBuf::from("src/uart.hwml");
    let text = "def Uart : Bit = i1".to_string();
    let source_file = SourceFile::new(&db, path.clone(), text);

    // First harvest
    let decls1 = file_declarations(&db, source_file);

    // Second harvest (same file, should be cached)
    let decls2 = file_declarations(&db, source_file);

    // Verify caching via Arc pointer equality
    assert!(Arc::ptr_eq(&decls1, &decls2), "Should be cached");

    // "Edit" the file
    let text2 = "def Uart : Bit = i0".to_string();  // Changed!
    let source_file2 = SourceFile::new(&db, path, text2);

    // Third harvest (different text, should NOT be cached)
    let decls3 = file_declarations(&db, source_file2);

    // Verify NOT cached (different Arc)
    assert!(!Arc::ptr_eq(&decls1, &decls3), "Should NOT be cached");
}

#[test]
fn test_concrete_vs_parametric() {
    use hwml_db::{library_declarations, SourceFile, VfsFileMap};
    use std::collections::HashMap;
    use std::sync::Arc;

    let db = HwmlDatabase::new();

    // Create a file with both parametric and concrete definitions
    let path = PathBuf::from("src/fifo.hwml");
    let text = r#"
        def Fifo (width : Nat) = ...     // Parametric
        def Fifo_32 = Fifo 32             // Concrete
    "#.to_string();
    let source_file = SourceFile::new(&db, path.clone(), text);

    let mut files = HashMap::new();
    files.insert(path, source_file);
    let vfs_map = VfsFileMap::new(&db, Arc::new(files));

    // Harvest
    let decls = library_declarations(&db, vfs_map);

    // Check concrete definitions
    let concrete: Vec<_> = decls.concrete_definitions().collect();
    println!("Concrete definitions:");
    for (name, stub) in &concrete {
        println!("  {:?}", name);
    }

    // Check parametric definitions
    let parametric: Vec<_> = decls.parametric_definitions().collect();
    println!("Parametric definitions:");
    for (name, stub) in &parametric {
        println!("  {:?}", name);
    }

    // Fifo_32 should be concrete, Fifo should be parametric
    assert!(concrete.len() >= 1, "Should have at least 1 concrete definition");
    assert!(parametric.len() >= 1, "Should have at least 1 parametric definition");
}
```

---

## 🔄 **Compilation Flow**

### **Step-by-Step Execution**

1. **Load Workspace**
   ```rust
   let workspace_decls = workspace_declarations(&db, manifest_path);
   ```
   - Parses `hwml.toml`
   - Discovers dependencies: `fifo`, `common`
   - Processes in topological order:
     1. `common` (no dependencies)
     2. `fifo` (no dependencies)
     3. `example_project` (depends on fifo, common)

2. **For Each Library**
   ```rust
   let lib_decls = library_declarations(&db, vfs_map);
   ```
   - Discovers all `.hwml` files
   - Creates `SourceFile` for each
   - Calls `file_declarations()` for each file (cached!)
   - Merges into library `StubTable`
   - Checks for collisions within library

3. **For Each File**
   ```rust
   let file_decls = file_declarations(&db, source_file);
   ```
   - Parses file with `parse_surface_program()` (cached!)
   - Harvests declarations into vector
   - Returns `Arc<Vec<(QualifiedName, Stub)>>`

4. **Merge All Libraries**
   - Combine all library `StubTable`s
   - Check for cross-library collisions
   - Return global `Arc<StubTable>`

---

## 📊 **Expected Results**

### **Declarations from Each Library**

**common library:**
- `Common.Types.Bit8` (concrete)
- `Common.Types.Bit16` (concrete)
- `Common.Types.Bit32` (concrete)
- `Common.Types.Width8` (concrete)
- `Common.Types.Width16` (concrete)
- `Common.Types.Width32` (concrete)

**fifo library:**
- `Fifo.Fifo` (parametric - compile-time only)
- `Fifo.Fifo_8` (concrete - Verilog module)
- `Fifo.Fifo_16` (concrete - Verilog module)
- `Fifo.Fifo_32` (concrete - Verilog module)

**example_project library:**
- `Main.MyFifo_32` (concrete - Verilog module)
- `Main.TopLevel` (concrete - Verilog module)
- `Main.Util.clamp` (concrete)
- `Uart.UartConfig` (parametric - compile-time only)
- `Uart.Config_9600` (concrete - Verilog module)
- `Uart.Config_115200` (concrete - Verilog module)
- `Uart.Tx` (concrete - Verilog module)

### **Total:**
- **Concrete:** ~14 definitions (will be lowered to Verilog)
- **Parametric:** ~2 definitions (compile-time only)

---

## 🎓 **Key Takeaways**

1. **No Imports Needed** - All files and dependencies are globally visible
2. **Namespace Organization** - Use namespaces to organize and avoid collisions
3. **Explicit Monomorphization** - Users explicitly name concrete Verilog modules
4. **Incremental by Default** - Salsa caches at every level automatically
5. **Dependency Resolution** - `hwml.toml` handles all dependencies
6. **Collision Detection** - Hard errors prevent Verilog linker issues

---

## 🚀 **Next Steps**

After loading the workspace declarations:

1. **Elaboration** - Type check each concrete definition
2. **Lowering** - Convert concrete definitions to MLIR/Verilog
3. **Code Generation** - Emit Verilog modules for each concrete definition

```rust
// Future compilation pipeline
let workspace_decls = workspace_declarations(&db, manifest);

for (name, stub) in workspace_decls.concrete_definitions() {
    // Elaborate (type check)
    let elaborated = elaborate(&db, &workspace_decls, stub)?;

    // Lower to MLIR
    let mlir = lower_to_mlir(&db, &elaborated)?;

    // Emit Verilog
    let verilog = mlir_to_verilog(&mlir)?;

    // Write file: {name}.v
    std::fs::write(format!("{}.v", name), verilog)?;
}
```

---

## 📚 **See Also**

- `USAGE-GUIDE.md` - Complete API reference
- `IMPLEMENTATION-PLAN.md` - How it was built
- `ADR-011-module-resolution-file-discovery.md` - Architecture decisions
- `MODULE-SYSTEM-STATUS.md` - Current progress

