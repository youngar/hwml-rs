# Workspace Aggregation Usage Guide

**Date:** 2026-05-04  
**Status:** Reference Documentation

This guide explains how to use the workspace aggregation infrastructure in HWML.

---

## 🎯 **Overview**

HWML uses **library-level aggregation** where all `.hwml` files in a library are automatically pooled into a single global namespace. This eliminates the need for explicit imports and matches the mental model of hardware engineering.

### **Key Concepts**

1. **Library = Compilation Unit** - All files in `hwml.toml` are treated as one logical unit
2. **Global Visibility** - All symbols from all files and dependencies are visible
3. **Explicit Monomorphization** - Users explicitly name concrete Verilog modules
4. **Incremental Compilation** - Salsa caches results at file, library, and workspace levels

---

## 📚 **API Reference**

### **Three Query Levels**

```rust
use hwml_db::{
    file_declarations,        // Per-file harvesting
    library_declarations,     // Single library aggregation
    workspace_declarations,   // Full workspace with dependencies
    HwmlDatabase, SourceFile, VfsFileMap
};
use std::path::PathBuf;
use std::collections::HashMap;
use std::sync::Arc;
```

#### **Level 1: `file_declarations()`**

Harvest declarations from a single file.

```rust
let db = HwmlDatabase::new();

// Create a source file
let path = PathBuf::from("src/fifo.hwml");
let text = "def Fifo_32 = ...".to_string();
let source_file = SourceFile::new(&db, path, text);

// Harvest this file only
let decls = file_declarations(&db, source_file);

// Returns Arc<Vec<(QualifiedName, Stub)>>
for (name, stub) in decls.iter() {
    println!("Found: {:?} (concrete: {})", name, stub.is_concrete);
}
```

**When to use:**
- Testing single-file parsing
- Building custom pipelines
- Understanding what one file contributes

---

#### **Level 2: `library_declarations()`**

Aggregate all files in a single library.

```rust
let db = HwmlDatabase::new();

// Create a VfsFileMap with multiple files
let mut files = HashMap::new();
files.insert(
    PathBuf::from("src/fifo.hwml"),
    SourceFile::new(&db, PathBuf::from("src/fifo.hwml"), "def Fifo_32 = ...".to_string())
);
files.insert(
    PathBuf::from("src/uart.hwml"),
    SourceFile::new(&db, PathBuf::from("src/uart.hwml"), "def Uart_9600 = ...".to_string())
);

let vfs_map = VfsFileMap::new(&db, Arc::new(files));

// Harvest all files
let all_decls = library_declarations(&db, vfs_map);

// Returns Arc<StubTable>
println!("Total declarations: {}", all_decls.len());

// Iterate over concrete definitions (those lowered to Verilog)
for (name, stub) in all_decls.concrete_definitions() {
    println!("Verilog module: {:?}", name);
}
```

**When to use:**
- Single-library projects
- Testing without dependencies
- Building tools that work on one library

---

#### **Level 3: `workspace_declarations()`**

Load entire workspace including all dependencies.

```rust
let db = HwmlDatabase::new();

// Point to a hwml.toml manifest
let manifest_path = PathBuf::from("myproject/hwml.toml");

// Load workspace (parses hwml.toml, loads dependencies, aggregates all)
let workspace_decls = workspace_declarations(&db, manifest_path);

// Returns Arc<StubTable> with EVERYTHING
println!("Total workspace declarations: {}", workspace_decls.len());

// Separate concrete from parametric
let concrete_count = workspace_decls.concrete_definitions().count();
let parametric_count = workspace_decls.parametric_definitions().count();

println!("Concrete (Verilog): {}", concrete_count);
println!("Parametric (compile-time): {}", parametric_count);
```

**When to use:**
- Production compilation
- Multi-library projects
- When you need dependency resolution

---

## 📁 **Project Structure**

### **Example `hwml.toml`**

```toml
[library]
name = "my_hardware"
edition = 1

[dependencies]
fifo = { path = "../hwml-fifo" }
axi = { path = "../hwml-axi" }

# Optional: explicit file list (otherwise auto-discovers *.hwml)
[sources]
files = ["src/main.hwml", "src/util.hwml"]
```

### **Directory Structure**

```
myproject/
├── hwml.toml
├── src/
│   ├── main.hwml        # Entry point
│   ├── fifo.hwml        # Fifo implementations
│   └── util.hwml        # Utilities
└── deps/
    ├── hwml-fifo/
    │   ├── hwml.toml
    │   └── src/
    │       └── fifo.hwml
    └── hwml-axi/
        ├── hwml.toml
        └── src/
            └── axi.hwml
```

---

## 🔄 **Incremental Compilation**

### **How It Works**

The workspace aggregation uses a three-tier Salsa caching system:

```
User edits fifo.hwml:
  ↓
SourceFile.text changed
  ↓
parse_surface_program(fifo.hwml) invalidates → re-parses ONLY fifo.hwml
  ↓
file_declarations(fifo.hwml) invalidates → re-harvests ONLY fifo.hwml
  ↓
library_declarations() invalidates → re-aggregates
  ↓
BUT: file_declarations(uart.hwml, axi.hwml, ...) use CACHED results! ✨
  ↓
workspace_declarations() invalidates → re-aggregates
  ↓
BUT: Dependency libraries use CACHED library_declarations()! 🚀
  ↓
RESULT: Only fifo.hwml was re-parsed and re-harvested
```

### **Cache Verification**

You can verify caching with Arc pointer equality:

```rust
let db = HwmlDatabase::new();
let source_file = SourceFile::new(&db, path, text);

// First call
let decls1 = file_declarations(&db, source_file);

// Second call (same file, unchanged)
let decls2 = file_declarations(&db, source_file);

// Verify it's the SAME Arc (pointer equality = cached!)
assert!(Arc::ptr_eq(&decls1, &decls2));
```

---

## 🏗️ **Integration with Elaborator**

### **Current Pattern (Single File)**

The elaborator currently works on single files:

```rust
use hwml_elab::program::elab_program;
use hwml_surface::parsing::parse;
use hwml_core::val::GlobalEnv;

let program = parse(source.as_bytes()).unwrap();
let mut global = GlobalEnv::new();
let result = elab_program(&db, &mut global, &program);
```

### **Future Pattern (Workspace-Aware)**

With workspace declarations, the pipeline becomes:

```rust
use hwml_db::workspace_declarations;
use hwml_elab::program::elab_program;
use hwml_core::val::GlobalEnv;

// 1. Load entire workspace
let manifest = PathBuf::from("hwml.toml");
let global_stubs = workspace_declarations(&db, manifest);

// 2. Elaborate only concrete definitions (those lowered to Verilog)
let mut global = GlobalEnv::new();
for (name, stub) in global_stubs.concrete_definitions() {
    // TODO: Elaborate each concrete definition
    // This requires updates to elaborator to accept pre-built StubTable
}

// 3. Parametric definitions are available for compile-time evaluation
// but NOT lowered to Verilog
```

---

## 🎨 **Examples**

### **Example 1: Multi-File Library**

**File: `src/types.hwml`**
```hwml
namespace Types {
    def Bit8 = ...
    def Bit16 = ...
}
```

**File: `src/main.hwml`**
```hwml
open Types

def MyModule : Bit8 -> Bit16 = ...
```

**Usage:**
```rust
let db = HwmlDatabase::new();
let vfs_map = /* load both files */;
let decls = library_declarations(&db, vfs_map);

// MyModule can reference Types.Bit8 and Types.Bit16
// because they're in the same library!
```

---

### **Example 2: Explicit Monomorphization**

**File: `src/fifo.hwml`**
```hwml
// Parametric definition (compile-time only)
def Fifo (width : Nat) = ...

// Concrete definitions (lowered to Verilog)
def Fifo_8 = Fifo 8
def Fifo_16 = Fifo 16
def Fifo_32 = Fifo 32
```

**Usage:**
```rust
let decls = library_declarations(&db, vfs_map);

// Parametric: Fifo (not lowered)
let parametric: Vec<_> = decls.parametric_definitions().collect();
assert_eq!(parametric.len(), 1); // Just "Fifo"

// Concrete: Fifo_8, Fifo_16, Fifo_32 (lowered to Verilog)
let concrete: Vec<_> = decls.concrete_definitions().collect();
assert_eq!(concrete.len(), 3);
```

---

### **Example 3: Cross-Library Dependencies**

**Library: `hwml-util/hwml.toml`**
```toml
[library]
name = "util"
```

**Library: `hwml-util/src/common.hwml`**
```hwml
def Helper : Bit = ...
```

**Library: `myproject/hwml.toml`**
```toml
[library]
name = "myproject"

[dependencies]
util = { path = "../hwml-util" }
```

**Library: `myproject/src/main.hwml`**
```hwml
// No import needed! All dependencies globally visible
def Main = Helper  // Uses Helper from util library
```

**Usage:**
```rust
let manifest = PathBuf::from("myproject/hwml.toml");
let workspace_decls = workspace_declarations(&db, manifest);

// workspace_decls contains:
// - Helper (from util library)
// - Main (from myproject library)
```

---

## 🚨 **Error Handling**

### **Collision Detection**

```rust
// lib_a/src/foo.hwml
def MyModule_32 = ...  // Concrete

// lib_b/src/bar.hwml
def MyModule_32 = ...  // Concrete - COLLISION!

// When loading workspace:
let workspace_decls = workspace_declarations(&db, manifest);
// Prints: "Warning: Cross-library collision in 'lib_b':
//          Duplicate definition of 'MyModule_32'"
```

### **Parametric Definitions Can Share Names**

```rust
// lib_a/src/foo.hwml
def Fifo (width : Nat) = ...  // Parametric

// lib_b/src/bar.hwml
def Fifo (width : Nat) = ...  // Parametric - OK!

// This is allowed because parametric definitions
// are compile-time only and not lowered to Verilog
```

---

## 📊 **Performance Tips**

1. **Use workspace_declarations() for production** - It handles dependencies automatically
2. **Use library_declarations() for testing** - Faster when you don't need dependencies
3. **Use file_declarations() for debugging** - See exactly what one file contributes
4. **Trust Salsa caching** - Don't manually cache results, Salsa is smarter
5. **Edit files via SourceFile updates** - Salsa tracks changes automatically

---

## 🔗 **Related Documentation**

- `wiki/decisions/ADR-011-module-resolution-file-discovery.md` - Architecture decisions
- `wiki/implementation/module-system/IMPLEMENTATION-PLAN.md` - Implementation plan
- `MODULE-SYSTEM-STATUS.md` - Current progress
- `crates/hwml-db/src/workspace.rs` - Source code with detailed comments

---

## ❓ **FAQ**

**Q: Do I need to import symbols from other files in the same library?**
A: No! All files in a library are pooled together. Just use the symbols directly.

**Q: Do I need to import symbols from dependencies?**
A: No! All dependencies are globally visible. Just use them.

**Q: How do I avoid name collisions?**
A: Use namespaces! `namespace MyLib { def Foo = ... }` creates `MyLib.Foo`.

**Q: What if two libraries define the same concrete symbol?**
A: Hard error! The compiler will tell you which libraries collided.

**Q: Can I have two parametric definitions with the same name?**
A: Yes! They're compile-time only, so no Verilog collision.

**Q: How do I know if something is concrete or parametric?**
A: If it has meta-level parameters (bindings), it's parametric. Otherwise concrete.

**Q: Will editing one file re-compile everything?**
A: No! Salsa caches at file, library, and workspace levels. Only changed parts recompile.


