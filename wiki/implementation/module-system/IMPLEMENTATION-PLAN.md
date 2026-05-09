# Workspace Aggregation & Global Resolution Implementation Plan

**Status:** In Progress 🚧
**Based on:** Library-level compilation model (C#/SystemVerilog style)
**Started:** 2026-05-04
**Last Updated:** 2026-05-04

---

## 🎯 **Goals**

Implement library-level compilation where all files in a library are automatically aggregated:

1. **No file-level imports** - The library (defined by `hwml.toml`) is the compilation unit
2. **Automatic file aggregation** - All `.hwml` files are pooled together
3. **Global namespace** - All definitions from all dependencies are globally visible
4. **Explicit monomorphization** - Users explicitly name concrete Verilog modules
5. **Strict collision detection** - Hard error on duplicate concrete definitions
6. **Incremental compilation** - Salsa handles fine-grained invalidation

---

## 🏗️ **Architecture Overview**

### **The Three Core Principles**

#### **1. Libraries, Not Modules**
- **HWML does NOT have `module "file.hwml"` syntax**
- The library (defined by `hwml.toml`) is the compilation unit
- All `.hwml` files within a library are automatically aggregated
- No file-level imports, includes, or dependency declarations in source code

#### **2. Three Keywords Only**
1. **`namespace Name { ... }`** - Creates logical prefix for definitions
   ```hwml
   namespace UartConfig {
       def default = { baudRate = 9600 }
   }
   // Creates: UartConfig.default
   ```

2. **`open Name`** - Strips namespace prefix in current scope
   ```hwml
   open UartConfig
   def myConfig = default  // Instead of UartConfig.default
   ```

3. **`def Name = ...`** - Defines values/functions (parametric or concrete)
   ```hwml
   def Fifo (width : Nat) = ...  // Parametric - NOT Verilog
   def Fifo_32 = Fifo 32          // Concrete - IS Verilog
   ```

#### **3. Global Visibility + Strict Collision Detection**
- All libraries in `hwml.toml` are globally visible (no import needed)
- All files in a library automatically see each other
- **Hard error on collision** for concrete definitions (Verilog-bound)
- Parametric definitions can share names (they're compile-time only)

### **Why This Design?**

**Matches Hardware Engineer Mental Model:**
- Hardware projects = flat list of files + synthesizer
- Like SystemVerilog: all modules in package are visible
- Like C#: assembly = compilation unit, all files pooled

**Enables Lean-Style Features:**
- Namespace extension across files
- Dot notation lookup (e.g., `myStruct.field`)
- Mutual recursion just works (all files in one pool)

**Simplifies Compiler:**
- No file dependency graph to track
- No cycle detection needed
- Salsa handles incrementality automatically

---

## ✅ **Completed: Phase 0 - VFS Foundation**

We already built the necessary infrastructure:

- ✅ **VfsFileMap Salsa Input** - Tracks all `.hwml` files in workspace
- ✅ **Path Normalization** - Ensures consistent HashMap keys
- ✅ **Workspace Initialization** - `CompilerSession::new_for_workspace()`
- ✅ **File Discovery** - `discover_hwml_files()` recursively finds all `.hwml` files
- ✅ **File Add/Remove API** - For file watcher integration
- ✅ **6 passing tests** - Comprehensive coverage

**Key Achievement:** All `.hwml` files are already discovered and loaded into `VfsFileMap`! We just need to harvest their declarations.

---

## 📋 **Implementation Phases**

### **Phase 1: Global Declaration Harvesting** 🔄

**Goal:** Collect all top-level declarations from all library files into a single global `StubTable`.

**The Pattern:**
```rust
#[salsa::tracked]
pub fn library_declarations(
    db: &dyn Db,
    vfs_map: VfsFileMap
) -> Result<StubTable, Vec<HarvestError>> {
    let mut global_table = StubTable::new();

    // Parse and harvest ALL files in library
    for (path, source_file) in vfs_map.files(db) {
        let program = parse_program(db, source_file);
        harvest_program(db, &mut global_table, source_file.source(), &program)?;
    }

    Ok(global_table)
}
```

**Tasks:**

**1.1: Add `is_concrete` flag to `Stub`**
- Distinguish parametric definitions from concrete ones
- Only concrete definitions need unique names for Verilog
- Parametric functions can share names across libraries

**1.2: Implement `library_declarations()` Salsa query**
- Iterate over all files in `VfsFileMap`
- Parse each file using existing `parse_program()`
- Call `harvest_program()` for each file
- Collect all declarations into single `StubTable`

**1.3: Update collision detection**
- Check for duplicate concrete definitions (hard error)
- Allow duplicate parametric definitions (they're compile-time)
- Emit `SymbolCollisionError` with source locations

**1.4: Add tests**
- Test harvesting from multiple files
- Test mutual recursion across files (should just work!)
- Test collision detection for concrete definitions
- Test parametric definitions with same name (should succeed)

**Files to Create/Modify:**
- `crates/hwml-db/src/lib.rs` - Add `library_declarations` query
- `crates/hwml-elab/src/stub_table.rs` - Add `is_concrete` field
- `crates/hwml-elab/src/stub_table.rs` - Update collision logic

**Success Criteria:**
- ✅ Can harvest declarations from all files in library
- ✅ Mutual recursion across files works (no special logic needed)
- ✅ Hard error on concrete definition collision
- ✅ Parametric definitions with same name allowed

---

### **Phase 2: Incremental Harvesting Optimization** 🔜

**Goal:** Optimize Salsa invalidation so editing one file only re-harvests that file.

**The Problem:**
If `library_declarations()` directly depends on `parse_program()` for all files, then editing ANY file would invalidate the entire library harvesting!

**The Solution: Per-File Harvesting**
```rust
// Harvest EACH file independently
#[salsa::tracked]
pub fn file_declarations(
    db: &dyn Db,
    source_file: SourceFile,
) -> Result<Vec<(QualifiedName, Stub)>, Vec<HarvestError>> {
    let program = parse_program(db, source_file);
    let mut declarations = Vec::new();

    // Extract declarations from this file only
    harvest_program_into_vec(db, source_file.source(), &program, &mut declarations)?;

    Ok(declarations)
}

// Aggregate all files
#[salsa::tracked]
pub fn library_declarations(
    db: &dyn Db,
    vfs_map: VfsFileMap,
) -> Result<StubTable, Vec<HarvestError>> {
    let mut global_table = StubTable::new();

    // Depends on file_declarations for each file independently
    for (path, source_file) in vfs_map.files(db) {
        let file_decls = file_declarations(db, source_file)?;

        for (name, stub) in file_decls {
            global_table.insert(name, stub)?;  // Check collisions
        }
    }

    Ok(global_table)
}
```

**Incremental Behavior:**
```
User edits file_a.hwml:
  ↓
parse_program(file_a) invalidated
  ↓
file_declarations(file_a) invalidated, re-runs
  ↓
library_declarations() invalidated, re-runs
  ↓
BUT: file_declarations(file_b, file_c, ...) use CACHED results!
  ↓
Only file_a is re-harvested, rest come from cache
```

**Tasks:**

**2.1: Implement `file_declarations()` query**
- Extract declarations from a single file
- Return `Vec<(QualifiedName, Stub)>` for that file
- Handle namespaces correctly

**2.2: Update `library_declarations()` to aggregate**
- Call `file_declarations()` for each file
- Merge results into global `StubTable`
- Check collisions during merge

**2.3: Test incrementality**
- Edit one file → verify only that file re-harvested
- Use Salsa debug output to confirm cache hits

**Files to Modify:**
- `crates/hwml-db/src/lib.rs` - Add both queries

**Success Criteria:**
- ✅ Editing file A doesn't re-harvest files B, C, D
- ✅ Salsa cache hit rate >95% on single-file edits
- ✅ All files still see each other (mutual recursion works)

---

### **Phase 3: Cross-Library Dependencies** 🔜

**Goal:** Load and merge declarations from dependencies listed in `hwml.toml`.

**The Pattern:**
```toml
# lib/uart/hwml.toml
[package]
name = "uart"
version = "0.1.0"

[dependencies]
fifo = { path = "../fifo" }
axi = { path = "../axi" }

[lib]
root = "src"  # Directory containing .hwml files
```

**Algorithm:**
```rust
#[salsa::tracked]
pub fn workspace_declarations(
    db: &dyn Db,
    workspace: WorkspaceRoot,
) -> Result<StubTable, Vec<Error>> {
    let mut global_table = StubTable::new();

    // 1. Harvest current library
    let vfs_map = workspace.vfs_file_map(db);
    let current_lib_decls = library_declarations(db, vfs_map)?;
    merge_into(&mut global_table, current_lib_decls)?;

    // 2. Load and harvest each dependency
    let manifest = workspace.manifest(db);
    for (lib_name, lib_spec) in manifest.dependencies() {
        let dep_workspace = load_dependency(db, lib_spec)?;
        let dep_decls = library_declarations(db, dep_workspace.vfs_file_map(db))?;

        // Merge - CHECK FOR COLLISIONS!
        merge_into(&mut global_table, dep_decls)?;
    }

    Ok(global_table)
}
```

**Collision Handling:**
```rust
fn merge_into(
    global: &mut StubTable,
    library: StubTable
) -> Result<(), SymbolCollisionError> {
    for (name, stub) in library.stubs() {
        if stub.is_concrete {
            // Hard error if concrete definition already exists
            if let Some(existing) = global.get(name) {
                if existing.is_concrete {
                    return Err(SymbolCollisionError {
                        name,
                        first_lib: existing.library,
                        first_location: existing.source_range,
                        second_lib: stub.library,
                        second_location: stub.source_range,
                    });
                }
            }
        }
        global.insert(name, stub)?;
    }
    Ok(())
}
```

**Tasks:**

**3.1: Parse `hwml.toml` manifest**
- Add `toml` crate dependency
- Parse package metadata and dependencies
- Create `Manifest` struct

**3.2: Implement dependency loading**
- `load_dependency()` - Create `VfsFileMap` for dependency library
- Handle relative paths from manifest
- Cache loaded dependencies (Salsa input)

**3.3: Implement `workspace_declarations()`**
- Aggregate current library + all dependencies
- Detect cross-library collisions
- Return unified global `StubTable`

**3.4: Test cross-library scenarios**
- Test using definitions from dependencies
- Test collision detection across libraries
- Test transitive dependencies

**Files to Create/Modify:**
- `crates/hwml-db/src/manifest.rs` - Manifest parsing
- `crates/hwml-db/src/lib.rs` - Add `workspace_declarations` query
- `crates/hwml-db/Cargo.toml` - Add `toml` dependency

**Success Criteria:**
- ✅ Can load dependencies from `hwml.toml`
- ✅ All dependencies globally visible
- ✅ Hard error on cross-library concrete collisions
- ✅ Transitive dependencies work


---

### **Phase 4: Elaborator Integration** 🔜

**Goal:** Use the global `StubTable` during elaboration and type checking.

**The Pipeline:**
```rust
// Compilation pipeline
fn compile_workspace(workspace: WorkspaceRoot) -> Result<CompiledWorkspace> {
    let db = HwmlDatabase::new();

    // 1. Build global StubTable (all files + dependencies)
    let global_stubs = workspace_declarations(&db, workspace)?;

    // 2. Type check each concrete definition
    let mut checked_modules = Vec::new();
    for (name, stub) in global_stubs.concrete_definitions() {
        let checked = elaborate_definition(&db, &global_stubs, stub)?;
        checked_modules.push((name, checked));
    }

    // 3. Lower to Verilog (only concrete definitions)
    let verilog = lower_to_verilog(&db, &checked_modules)?;

    Ok(CompiledWorkspace { verilog, ... })
}
```

**Key Updates:**

**Resolver Changes:**
- `Resolver` no longer needs file-aware scoping
- All files in library share same environment
- `open` just modifies current lexical scope (already works!)

**StubTable Changes:**
- Already has namespace support ✅
- Add `concrete_definitions()` iterator
- Add `parametric_definitions()` iterator

**Elaboration Changes:**
- Reference global `StubTable` for name lookups
- Mutual recursion across files works automatically
- No special "cross-file" reference handling needed

**Tasks:**

**4.1: Add definition categorization**
- `StubTable::concrete_definitions()` - Iterator over Verilog-bound defs
- `StubTable::parametric_definitions()` - Iterator over compile-time defs
- Determine concreteness during harvesting

**4.2: Update compilation pipeline**
- Wire `workspace_declarations()` into main compilation
- Pass global `StubTable` to elaborator
- Remove any file-scoped logic (it doesn't exist anymore!)

**4.3: Test elaboration with multiple files**
- Define function in file A, use in file B (mutual recursion)
- Test namespace extension across files
- Test `open` directive behavior

**Files to Modify:**
- `crates/hwml-elab/src/stub_table.rs` - Add iterators
- `crates/hwml/src/main.rs` - Update compilation pipeline
- Integration tests

**Success Criteria:**
- ✅ Can reference definitions from any file in library
- ✅ Mutual recursion across files works
- ✅ Namespace extension works (multiple files extend same namespace)
- ✅ `open` strips namespace prefix correctly

---

### **Phase 5: File Watcher Integration** 🔜

**Goal:** Enable live updates in LSP when files are created/deleted.

**The Beauty:** This is almost trivial now! File watcher just updates `VfsFileMap`, and Salsa automatically re-runs `library_declarations()`.

**Implementation:**
```rust
// In LSP server main loop
loop {
    select! {
        // File system events
        recv(file_watcher_rx) -> event => {
            match event? {
                Create(path) if is_hwml_file(&path) => {
                    let text = fs::read_to_string(&path)?;
                    session.add_file_to_workspace(path, text)?;
                    // ↑ This updates VfsFileMap
                    // → Salsa invalidates library_declarations()
                    // → Re-harvests automatically!
                }
                Remove(path) if is_hwml_file(&path) => {
                    session.remove_file_from_workspace(&path)?;
                    // Same invalidation cascade
                }
                Write(path) if is_hwml_file(&path) => {
                    // File saved externally - reload from disk
                    let text = fs::read_to_string(&path)?;
                    session.update_file(&path, text)?;
                }
            }
        }

        // LSP protocol messages
        recv(lsp_rx) -> msg => {
            handle_lsp_message(&mut session, msg)?;
        }
    }
}
```

**Automatic Incremental Behavior:**
```
User creates new_file.hwml:
  ↓
File watcher detects creation
  ↓
session.add_file_to_workspace(new_file, text)
  ↓
VfsFileMap updated (Salsa input changed!)
  ↓
library_declarations() invalidated
  ↓
file_declarations(new_file) runs (NEW)
  ↓
Other files use CACHED file_declarations results
  ↓
Global StubTable updated with new file's declarations
  ↓
LSP shows new definitions available immediately!
```

**Tasks:**

**5.1: Add `notify` crate dependency**
- Add to `hwml-lsp-server/Cargo.toml`
- Choose appropriate version

**5.2: Implement file watcher loop**
- Create `notify::Watcher` for workspace directory
- Filter for `.hwml` file events
- Wire to `CompilerSession` methods (already implemented!)

**5.3: Test live updates**
- Create new file → verify declarations appear
- Delete file → verify declarations disappear
- Edit file externally → verify changes reflected

**Files to Modify:**
- `crates/hwml-lsp-server/Cargo.toml` - Add `notify` dependency
- `crates/hwml-lsp-server/src/main.rs` - Add watcher loop

**Success Criteria:**
- ✅ Creating `.hwml` file makes definitions visible in LSP
- ✅ Deleting file removes definitions from scope
- ✅ External edits (e.g., git pull) reflected automatically
- ✅ Only affected files re-harvested (incremental!)

---

### **Phase 6: Comprehensive Testing** 🔜

**Goal:** Verify correctness, incrementality, and performance.

**Test Categories:**

**6.1 Multi-File Harvesting Tests**
- Test declarations from multiple files visible
- Test mutual recursion across files (define in A, use in B, use in A)
- Test namespace extension (two files add to same namespace)

**6.2 Collision Detection Tests**
- Test concrete definition collision (hard error)
- Test parametric definition with same name (should succeed)
- Test cross-library collision (hard error with library names)

**6.3 Incremental Harvesting Tests** ⚡ **CRITICAL**
- Edit file A → verify only file A re-harvested
- Add new file → verify only new file harvested
- Delete file → verify only that file removed from cache
- Measure Salsa cache hit rate (target: >95%)

**6.4 Cross-Library Tests**
- Test using definitions from dependencies
- Test transitive dependencies (A depends on B depends on C)
- Test collision between workspace and dependency

**6.5 Integration Tests**
- Full compilation with multiple files
- Namespace + open directive behavior
- Error messages for collisions

**Example Tests:**
```rust
#[test]
fn test_mutual_recursion_across_files() {
    let vfs = MemoryVfs::new();
    vfs.add("file_a.hwml", "def foo = bar");
    vfs.add("file_b.hwml", "def bar = foo");

    let session = CompilerSession::new_with_vfs(vfs);
    let stubs = library_declarations(&session.db, session.vfs_file_map())?;

    // Both definitions should exist
    assert!(stubs.contains("foo"));
    assert!(stubs.contains("bar"));
}

#[test]
fn test_incremental_harvesting() {
    let mut session = CompilerSession::new_for_workspace(workspace)?;
    session.db.enable_logging();

    // Initial compilation
    let stubs1 = library_declarations(&session.db, session.vfs_file_map())?;

    // Edit one file
    session.update_file("file_a.hwml", "def new_def = 42")?;

    // Re-harvest
    let stubs2 = library_declarations(&session.db, session.vfs_file_map())?;

    // Check logs - only file_a should be re-parsed
    let logs = session.db.take_logs();
    assert!(logs.contains("parse_program(file_a)"));
    assert!(!logs.contains("parse_program(file_b)"));
}
```

**Files to Create:**
- `crates/hwml-db/tests/workspace_aggregation_tests.rs`
- `crates/hwml-db/tests/incremental_harvesting_tests.rs`

**Success Metrics:**
- ✅ Mutual recursion works across all files
- ✅ Namespace extension works across files
- ✅ Incremental harvesting verified (cache hit rate >95%)
- ✅ LSP response time <10ms for single-file edits
- ✅ All collision cases detected with clear error messages

---

## 🗺️ **Dependency Graph**

```
Phase 0 (VFS Foundation) ✅ COMPLETE
    ↓
Phase 1 (Global Harvesting) ← START HERE
    ↓
Phase 2 (Incremental Optimization) ← Can be done in parallel with Phase 3
    ↓
Phase 3 (Cross-Library Dependencies)
    ↓
Phase 4 (Elaborator Integration)
    ↓
Phase 5 (File Watcher) ← Trivial! Just wire existing APIs
    ↓
Phase 6 (Testing)
```

---

## 📊 **Progress Tracking**

| Phase | Description | Tests | Est. Time | Status |
|-------|-------------|-------|-----------|--------|
| Phase 0 | VFS Foundation | 6/6 | - | ✅ Complete |
| Phase 1 | Global Harvesting | 0/4 | 2-3h | 🔄 Next |
| Phase 2 | Incremental Optimization | 0/3 | 2-3h | ⏸️ Blocked |
| Phase 3 | Cross-Library Deps | 0/4 | 3-4h | ⏸️ Blocked |
| Phase 4 | Elaborator Integration | 0/3 | 2-3h | ⏸️ Blocked |
| Phase 5 | File Watcher | 0/3 | 1h | ⏸️ Blocked |
| Phase 6 | Testing | 0/5 | 2-3h | ⏸️ Blocked |

**Total Estimated Time:** 12-17 hours (reduced from previous 11-17h estimate)

---

## 🔑 **Key Architectural Principles**

### **The Three Non-Negotiables:**

1. **Libraries, Not Modules**
   - No `module "file.hwml"` syntax in the language
   - Library (from `hwml.toml`) is the compilation unit
   - All files automatically aggregated

2. **Global Visibility + Strict Collision Detection**
   - All dependencies globally visible (no import needed)
   - Hard error on concrete definition collision
   - Parametric definitions can share names

3. **Explicit Monomorphization**
   - `def Fifo (w: Nat) = ...` - parametric, NOT Verilog
   - `def Fifo_32 = Fifo 32` - concrete, IS Verilog
   - User controls all Verilog module names

### **Why This Design Wins:**

✅ **No file dependency graph** - Massive complexity reduction
✅ **Mutual recursion just works** - All files in one pool
✅ **Salsa handles incrementality** - Per-file harvesting
✅ **Matches hardware mental model** - Flat list of files
✅ **Lean-style namespace extension** - Across multiple files

---

## 🎯 **Next Action**

**Start Phase 1:** Implement `library_declarations()` query to harvest all files.

**Quick Start:**
1. Add `is_concrete` field to `Stub` struct
2. Implement `library_declarations()` Salsa query
3. Update collision detection for concrete vs parametric
4. Test with multiple files

**Why This Is Easy:**
- VfsFileMap already has all files ✅
- `parse_program()` already works ✅
- `harvest_program()` already exists ✅
- Just need to call it for all files and merge!

---

**Document Status:** ✅ Radically Simplified & Ready
**Major Changes:** Removed module syntax, file dependency tracking, and structural extraction phases
**Next:** Phase 1 - Global Declaration Harvesting
