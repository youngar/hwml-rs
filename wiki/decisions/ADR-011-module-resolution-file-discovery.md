# ADR-011: Library-Level Aggregation and Global Symbol Resolution

**Status:** Approved ✅
**Date:** 2026-05-03 (Updated: 2026-05-04)
**Deciders:** Core team
**Related:** [[ADR-007-salsa-driven-compilation]], [[ADR-008-vfs-abstraction]], [[ADR-006-multi-layer-build-configuration]]

**⚠️ ARCHITECTURE CHANGE:** This ADR has been completely rewritten. The original file-based `module` system has been replaced with **Library-Level Aggregation** (similar to C#/SystemVerilog).

---

## Context

HWML compiles hardware designs to Verilog. Verilog has a **flat global namespace** for module definitions - all modules must have unique names across the entire design.

**The Core Constraint:** Because HWML's ultimate compilation target is Verilog, we are fundamentally bound by Verilog's flat global namespace. This drives the entire module system design.

**Three Critical Questions:**

1. **How do files relate to compilation units?** Do we need explicit `module "file.hwml"` imports, or is the library itself the compilation unit?

2. **How do namespaces work?** Are they tied to files, or are they purely lexical constructs?

3. **How do we handle parametric hardware?** Do we automatically monomorphize `Fifo<32>` → `Fifo_32`, or does the user explicitly create concrete instances?

**The trap:** Early designs tried to create complex file dependency graphs and automatic monomorphization. This added massive complexity for little benefit, since hardware engineers already think in terms of "flat lists of files passed to a synthesizer."

---

## Decision

**HWML adopts Library-Level Aggregation: the library (defined by `hwml.toml`) is the compilation unit. All `.hwml` files in a library are automatically aggregated into a single global namespace.**

### The Four Core Rules

**Rule 1: Modules DO NOT Create Namespaces**

There is **no `module "file.hwml"` syntax** in HWML. Files are just "chunks of the same logical program." No imports needed.

**Rule 2: `namespace` Creates Logical Prefixes**

```hwml
namespace Uart {
    def Config = { baudRate : Nat }
    def make (cfg : Config) : Module = ...
}

// Fully qualified reference: Uart.make
// Or use `open Uart` to strip the prefix
```

Namespaces can be extended across multiple files:

```hwml
// file_a.hwml
namespace Uart {
    def Config = ...
}

// file_b.hwml
namespace Uart {
    def make = ...  // Extends same namespace!
}
```

**Rule 3: `open` is Lexical Scope Only**

```hwml
open Uart  // Now can write `make` instead of `Uart.make`

def myUart = make { baudRate = 9600 }
```

`open` has **nothing to do** with file loading or library imports. It's pure syntax sugar for stripping namespace prefixes.

**Rule 4: Global Visibility + Strict Collision Detection**

All symbols defined in the workspace and its dependencies are **globally visible**. No imports needed.

**Concrete definitions** (those lowered to Verilog) must have unique names workspace-wide:

```hwml
// ✅ ALLOWED: Parametric definitions (compile-time only)
def Fifo (width : Nat) (depth : Nat) : Module = ...

// ✅ ALLOWED: Concrete instances (lowered to Verilog)
def Fifo_32 = Fifo 32 16    // → module Fifo_32 ...
def UartFifo = Fifo 8 256   // → module UartFifo ...

// ❌ ERROR: Duplicate concrete definition
def Fifo_32 = ...  // Hard error! Collision detected
```

**Why strict collision detection?** If we allow collisions in HWML, the user succeeds in HWML only to get incomprehensible Verilog linker errors later. Failing fast with clear diagnostics is better.

### Architecture: Library as Compilation Unit

**Key Principle:** All `.hwml` files in a library (directory containing `hwml.toml`) are automatically discovered and parsed. No explicit file imports needed.

**Input 1: Individual Source Files**
```rust
#[salsa::input]
pub struct SourceFile {
    #[return_ref]
    pub path: PathBuf,

    #[return_ref]
    pub text: String,
}
```

**Input 2: VFS File Map (All Known Files)**
```rust
#[salsa::input]
pub struct VfsFileMap {
    /// Map of canonical path → SourceFile
    /// Updated whenever files are added/removed by CompilerSession
    #[return_ref]
    pub files: Arc<HashMap<PathBuf, SourceFile>>,
}
```

**Query: Global Declaration Harvesting**
```rust
#[salsa::tracked]
pub fn library_declarations(
    db: &dyn Db,
    vfs_map: VfsFileMap,
) -> StubTable {
    let mut global_table = StubTable::new();

    // Iterate over ALL files in workspace
    for (path, source_file) in vfs_map.files(db).iter() {
        // Parse file (cached by Salsa!)
        let program = parse_surface_program(db, source_file);

        // Harvest declarations into global table
        harvest_program(db, &mut global_table, source, root_namespace, &program);
    }

    global_table
}
```

**The Magic: No File Dependencies**

Because all files are pooled together, mutual recursion works automatically:

```hwml
// file_a.hwml
def foo : Module = bar  // Can reference bar before it's defined!

// file_b.hwml
def bar : Module = ...  // Defined in different file - no problem!
```

No need to track which file defines what. Everything is in the global `StubTable`.

### Incremental Compilation with Salsa

**The Beauty of Library Aggregation:** When a file is edited, Salsa only re-parses that file and re-typechecks functions that depend on changed definitions.

**Flow for File Editing:**

```
User edits function body in file_a.hwml:
    ↓
SourceFile.text changed → parse_surface_program(file_a) invalidated
    ↓
library_declarations() re-runs
    ↓
Salsa iterates over ALL files, but uses CACHED parse results for unchanged files!
    ↓
Only file_a is re-parsed
    ↓
Global StubTable updated with new declarations from file_a
    ↓
Only functions that use changed symbols are re-typechecked
    ↓
✨ LSP responds in <10ms
```

**No Module Tree Needed:** Because all files are aggregated into one `StubTable`, there's no dependency graph to maintain or invalidate. Simpler architecture, same performance.

### Initialization Flow

```rust
impl CompilerSession {
    pub fn new_for_workspace(workspace_root: PathBuf) -> Result<Self> {
        let mut session = Self::new_with_os_vfs();

        // 1. Discover all .hwml files in workspace (filesystem scan)
        let discovered_files = Self::discover_hwml_files(&workspace_root)?;

        // 2. Create Salsa SourceFile inputs for each
        let mut file_map = HashMap::new();
        for path in discovered_files {
            let text = std::fs::read_to_string(&path)?;
            let source_file = SourceFile::new(&mut session.db, path.clone(), text);
            file_map.insert(path, source_file);
        }

        // 3. Create VfsFileMap input (snapshot of workspace)
        let vfs_file_map = VfsFileMap::new(&mut session.db, Arc::new(file_map));
        session.vfs_file_map = Some(vfs_file_map);

        Ok(session)
    }

    fn discover_hwml_files(root: &Path) -> Result<Vec<PathBuf>> {
        // Use walkdir or similar to find all *.hwml files
        let mut files = Vec::new();
        for entry in walkdir::WalkDir::new(root) {
            let entry = entry?;
            if entry.path().extension() == Some("hwml".as_ref()) {
                files.push(entry.path().canonicalize()?);
            }
        }
        Ok(files)
    }
}
```

### Cross-Library Dependencies

Libraries declared in `hwml.toml` are automatically visible globally:

```toml
# hwml.toml
[package]
name = "my-uart"

[dependencies]
fifo = { path = "../fifo" }
axi = { path = "../axi" }
```

```hwml
// No imports needed! All dependency symbols are globally visible
def myUart = Fifo.make 32 16  // Fifo from dependency library
```

**How it works:**

1. Workspace scans all `hwml.toml` manifests
2. Each library gets its own `library_declarations()` query
3. Type checker merges all `StubTable`s (workspace + dependencies)
4. Collision detection enforces unique names for concrete definitions

---

## Handling Missing Files

**Question:** What happens when the user creates a new `.hwml` file?

**Answer: The VfsFileMap is updated via file watcher, triggering Salsa invalidation.**

### File Watcher Integration

```rust
impl CompilerSession {
    /// Called by file watcher when files are created/deleted
    pub fn on_file_system_changed(&mut self, event: FileSystemEvent) {
        match event {
            FileSystemEvent::Created(path) if path.extension() == Some("hwml".as_ref()) => {
                self.add_file_to_workspace(path);
            }
            FileSystemEvent::Deleted(path) => {
                self.remove_file_from_workspace(path);
            }
            _ => {}
        }
    }
    
    fn add_file_to_workspace(&mut self, path: PathBuf, text: String) {
        // 1. Create Salsa SourceFile input
        let source_file = SourceFile::new(&mut self.db, path.clone(), text);

        // 2. Update VfsFileMap (THIS INVALIDATES SALSA QUERIES!)
        let mut files = (*self.vfs_file_map.unwrap().files(&self.db)).clone();
        files.insert(path, source_file);
        self.vfs_file_map.unwrap().set_files(&mut self.db).to(Arc::new(files));
    }

    fn remove_file_from_workspace(&mut self, path: PathBuf) {
        let mut files = (*self.vfs_file_map.unwrap().files(&self.db)).clone();
        files.remove(&path);
        self.vfs_file_map.unwrap().set_files(&mut self.db).to(Arc::new(files));
    }
}
```

**Flow for Missing Files:**

```hwml
// lib/uart/src/lib.hwml
module Registers from "registers.hwml"  // ← File doesn't exist yet!
```

1. `library_module_tree` query runs
2. Parses `module Registers from "registers.hwml"`
3. Resolves path: `lib/uart/src/registers.hwml`
4. Looks up in `VfsFileMap` → **file not found**
5. Records error in `ModuleTree.errors`
6. Compiler shows: "Module file not found: registers.hwml"

**When user creates the file:**

7. User creates `lib/uart/src/registers.hwml` and saves
8. File watcher detects creation → calls `session.add_file_to_workspace(path, text)`
9. `add_file_to_workspace` updates `VfsFileMap` input
10. **Salsa automatically invalidates** `library_module_tree` query
11. Query re-runs, finds file this time, no error!
12. Red squiggly disappears in editor ✨

---

## Rationale

### 1. Library-Level Aggregation Matches Hardware Engineering Practice

**How hardware engineers actually work:**
```bash
# Traditional Verilog/SystemVerilog workflow
$ iverilog -o design.vvp src/*.sv lib/*.sv  # Flat list of files!
$ vvp design.vvp
```

Hardware synthesizers take **flat lists of files**. There's no notion of "importing" modules - all modules are globally available.

**HWML mirrors this:**
- Library = bag of `.hwml` files
- No file-level imports needed
- All definitions globally visible (just like Verilog modules)
- File organization is purely for human convenience

**Benefits:**
- **Familiar mental model:** Hardware engineers don't have to learn complex module systems
- **Refactoring freedom:** Move code between files without updating imports
- **Mutual recursion works naturally:** No dependency order to worry about
- **Simpler tooling:** No need to build file dependency graphs

### 2. Global Collision Detection Prevents Verilog Linker Errors

**The Problem We're Solving:**

If we allowed shadowing/scoping for Verilog-bound definitions, users would succeed in HWML only to get cryptic Verilog errors:

```
Error: Multiple definitions of module 'Fifo_32'
  lib/fifo/fifo.v:10: first definition here
  lib/uart/fifo.v:15: redefinition here
```

**Our Solution:**

Hard error during HWML elaboration with clear diagnostics:

```
Error: Duplicate concrete definition 'Fifo_32'
  lib/fifo/src/main.hwml:10: first definition here
  lib/uart/src/util.hwml:15: redefinition here

  Note: Concrete definitions (those without meta-level parameters)
  must have unique names across the entire workspace because they
  are lowered to Verilog modules.
```

**Fail fast, fail clearly!**

### 3. Explicit Monomorphization Gives User Control

**Rejected Approach: Automatic Monomorphization**
```hwml
def Fifo (w : Nat) = ...

// Compiler automatically generates: Fifo_32, Fifo_64, Fifo_8, ...
let x = Fifo 32
let y = Fifo 64
let z = Fifo 8
```

**Problems:**
- User doesn't control Verilog module names (generated names may be ugly)
- Unclear cost model (how many Verilog modules will be generated?)
- Name collisions if mangling scheme isn't careful

**Our Approach: Explicit Monomorphization**
```hwml
def Fifo (w : Nat) = ...  // Generic, compile-time only

// User explicitly creates concrete instances with meaningful names
def Fifo_32 = Fifo 32  // → module Fifo_32 ...
def UartRxFifo = Fifo 8  // → module UartRxFifo ...
```

**Benefits:**
- **User controls naming:** Meaningful Verilog module names
- **Explicit cost model:** You see exactly which modules will be synthesized
- **No name mangling surprises:** What you name is what you get

### 4. Pure Declaration Harvesting (The Core Benefit)

**VfsFileMap enables pure queries:**

```rust
#[salsa::tracked]
pub fn library_declarations(db: &dyn Db, vfs_map: VfsFileMap) -> StubTable {
    // Pure lookup, no IO!
    for (path, source_file) in vfs_map.files(db).iter() {
        let program = parse_surface_program(db, source_file);
        harvest_program(db, &mut global_table, ...);
    }
    global_table
}
```

Salsa can cache and invalidate properly because all inputs are explicit.

### 5. File Discovery Happens Once (Efficient)

**Eager discovery at initialization:**
- Filesystem scan happens once when `CompilerSession` is created
- All `.hwml` files registered as Salsa inputs upfront
- Subsequent queries use pure lookups (fast)

**Incremental updates via file watcher:**
- File created → Add to VfsFileMap → Salsa invalidates `library_declarations()`
- File deleted → Remove from VfsFileMap → Salsa invalidates
- File modified → Update SourceFile.text → Salsa invalidates only that file's parsing

**No redundant scanning:** We don't re-scan the filesystem on every query.

### 6. Hermetic CLI Builds (Buck2 Compatible)

For CLI builds, the initial file discovery creates an atomic snapshot:

```rust
// CLI main.rs
let session = CompilerSession::new_for_workspace(workspace_root)?;
// ↑ All files loaded into Salsa inputs NOW
// Even if files change on disk mid-compilation, Salsa uses the snapshot
```

This is critical for remote execution and deterministic builds.

### 7. LSP Gets Live Updates

For LSP, the file watcher ensures live updates:

```rust
// LSP server
let mut session = CompilerSession::new_for_workspace(workspace_root)?;

// Start file watcher
let (tx, rx) = channel();
let watcher = notify::watcher(tx, Duration::from_secs(1))?;
watcher.watch(&workspace_root, RecursiveMode::Recursive)?;

loop {
    select! {
        recv(rx) -> event => {
            session.on_file_system_changed(event.unwrap());
        }
        recv(lsp_events) -> msg => {
            handle_lsp_message(&mut session, msg);
        }
    }
}
```

User creates file → Watcher fires → VfsFileMap updated → Diagnostics refresh automatically.

---

## Consequences

### Positive

1. **Radical simplification:** No file dependency graphs, no module trees, no import resolution
2. **Faster compilation:** No cycle detection, no complex invalidation logic
3. **Salsa invalidation works correctly:** VfsFileMap is an input, changes tracked automatically
4. **Efficient:** File discovery once at init, then pure lookups
5. **Hermetic CLI builds:** Snapshot at initialization prevents races
6. **LSP gets live updates:** File watcher updates VfsFileMap, Salsa recomputes
7. **Mutual recursion works automatically:** No dependency order constraints
8. **Matches hardware engineering practice:** Flat file lists like Verilog/SystemVerilog

### Negative

1. **Global namespace pollution:** All symbols visible everywhere
   - *Mitigation:* Use `namespace` to organize code. Collision detection prevents accidents.
   - *Note:* This matches Verilog's model anyway.

2. **Eagerly scans entire workspace:** Could be slow for very large workspaces
   - *Mitigation:* Most HWML projects will be <1000 files. Scanning takes <100ms.
   - *Future optimization:* Lazy loading per library if needed.

3. **File watcher complexity:** Need to integrate `notify` crate or similar
   - *Mitigation:* Well-understood pattern, used by all modern LSPs.

4. **VfsFileMap clones on update:** Updating VfsFileMap clones the HashMap
   - *Mitigation:* Use `Arc<HashMap>` inside VfsFileMap, cheap to clone.

### Neutral

- **No automatic monomorphization:** Users must explicitly create concrete instances.
  - This is by design - it gives users control over Verilog module naming and makes the cost model explicit.

---

## Alternatives Considered

### Alternative 1: File-Based Module System (Original ADR-011)

**What:** Explicit `module "file.hwml"` declarations with file dependency trees.

```hwml
module Registers from "registers.hwml"
module State from "state.hwml"
```

**Why rejected:**
- Adds massive complexity (cycle detection, import resolution, module trees)
- Doesn't match hardware engineering practice (no one thinks in terms of file imports for Verilog)
- Mutual recursion requires complex cycle-breaking logic
- Still ends up with global namespace anyway (Verilog requirement)

### Alternative 2: Automatic Monomorphization

**What:** Compiler automatically generates Verilog modules for all instantiations:

```hwml
def Fifo (w : Nat) = ...
let x = Fifo 32  // Compiler auto-generates Fifo_32 module
```

**Why rejected:**
- User doesn't control Verilog module names
- Unclear cost model (which modules get synthesized?)
- Name collisions if mangling scheme isn't perfect
- Users prefer explicit control over hardware resources

### Alternative 3: Scoped Symbol Tables (Per-Library Namespaces)

**What:** Each library gets its own namespace, no global visibility:

```hwml
import Fifo from "fifo"  // Explicit import needed
```

**Why rejected:**
- Still need global collision detection for Verilog emission
- Adds import boilerplate with no real benefit
- Users would just `import *` everything anyway
- Doesn't prevent the real problem (Verilog name collisions)

---

## Implementation

### Path Normalization (Critical for Correctness) 🚨

**The Trap:** `VfsFileMap` uses `PathBuf` as HashMap keys. **Any mismatch breaks lookup:**

```rust
// ❌ BROKEN: Different representations of same path
files.insert(PathBuf::from("lib/uart/src/uart.hwml"), file1);  // Relative
files.get(&PathBuf::from("/abs/path/lib/uart/src/uart.hwml"))  // Absolute → None!

// ❌ BROKEN: Case sensitivity differences (Windows)
files.insert(PathBuf::from("C:\\project\\lib.hwml"), file);
files.get(&PathBuf::from("c:\\project\\lib.hwml"))  // Lowercase drive → None!
```

**The Fix: Strict Canonicalization Boundary**

```rust
impl CompilerSession {
    /// Normalize path to canonical absolute form
    /// ALWAYS call this before VfsFileMap operations!
    fn normalize_path(&self, path: &Path) -> Result<PathBuf> {
        // 1. Canonicalize (resolves symlinks, makes absolute)
        let canonical = path.canonicalize()
            .or_else(|_| {
                // File might not exist yet, manually make absolute
                std::env::current_dir()?.join(path)
            })?;

        // 2. On Windows, normalize drive letter case
        #[cfg(windows)]
        let canonical = normalize_windows_path(canonical);

        Ok(canonical)
    }

    /// LSP integration: Convert URI to normalized path
    fn uri_to_path(&self, uri: &lsp_types::Url) -> Result<PathBuf> {
        let path = uri.to_file_path()
            .map_err(|_| Error::InvalidUri)?;
        self.normalize_path(&path)
    }

    pub fn add_file_to_workspace(&mut self, path: PathBuf, text: String) {
        // ALWAYS normalize before inserting!
        let canonical = self.normalize_path(&path).unwrap();

        let source_file = SourceFile::new(&mut self.db, canonical.clone(), text);

        let mut files = (*self.vfs_file_map.unwrap().files(&self.db)).clone();
        files.insert(canonical, source_file);
        self.vfs_file_map.unwrap().set_files(&mut self.db).to(Arc::new(files));
    }
}

#[cfg(windows)]
fn normalize_windows_path(path: PathBuf) -> PathBuf {
    // Ensure drive letter is uppercase: C:\ not c:\
    let s = path.to_string_lossy();
    if s.len() >= 2 && s.chars().nth(1) == Some(':') {
        let mut chars = s.chars();
        let drive = chars.next().unwrap().to_ascii_uppercase();
        PathBuf::from(format!("{}{}", drive, &s[1..]))
    } else {
        path
    }
}
```

**LSP Integration Example:**

```rust
impl LanguageServer {
    fn on_did_change(&mut self, params: DidChangeTextDocumentParams) {
        // URI from LSP: file:///C:/project/lib.hwml
        let path = self.session.uri_to_path(&params.text_document.uri).unwrap();
        // path is now: C:\project\lib.hwml (normalized)

        self.session.update_file(&path, params.content_changes[0].text.clone());
        // VfsFileMap lookup will succeed!
    }
}
```

### VfsFileMap with Arc for Cheap Cloning

```rust
#[salsa::input]
pub struct VfsFileMap {
    #[return_ref]
    pub files: Arc<HashMap<PathBuf, SourceFile>>,
}

impl CompilerSession {
    fn add_file_to_workspace(&mut self, path: PathBuf, text: String) {
        let canonical = self.normalize_path(&path).unwrap();
        let source_file = SourceFile::new(&mut self.db, canonical.clone(), text);

        // Arc makes this clone cheap (just increment refcount)
        let mut files = (*self.vfs_file_map.unwrap().files(&self.db)).clone();
        files.insert(canonical, source_file);

        self.vfs_file_map.unwrap().set_files(&mut self.db).to(Arc::new(files));
    }
}
```

### File Watcher Integration (LSP)

```rust
use notify::{Watcher, RecursiveMode, watcher};
use std::sync::mpsc::channel;
use std::time::Duration;

impl LanguageServer {
    pub fn start(workspace_root: PathBuf) -> Result<Self> {
        let session = CompilerSession::new_for_workspace(workspace_root.clone())?;

        let (tx, rx) = channel();
        let mut watcher = watcher(tx, Duration::from_millis(500))?;
        watcher.watch(&workspace_root, RecursiveMode::Recursive)?;

        Ok(Self { session, file_watcher: watcher, watcher_rx: rx })
    }

    pub fn poll_file_events(&mut self) {
        while let Ok(event) = self.watcher_rx.try_recv() {
            match event {
                notify::DebouncedEvent::Create(path) if is_hwml_file(&path) => {
                    let text = std::fs::read_to_string(&path).unwrap_or_default();
                    self.session.add_file_to_workspace(path, text);
                }
                notify::DebouncedEvent::Remove(path) if is_hwml_file(&path) => {
                    self.session.remove_file_from_workspace(path);
                }
                notify::DebouncedEvent::Write(path) if is_hwml_file(&path) => {
                    // File modified on disk (user saved in external editor)
                    let text = std::fs::read_to_string(&path).unwrap_or_default();
                    self.session.update_file(&path, text);
                }
                _ => {}
            }
        }
    }
}
```

---

## Implementation Gotchas 🚨

Before implementing, be aware of these critical mechanical issues:

### 1. Path Normalization is Mandatory

**Problem:** `VfsFileMap` uses `PathBuf` as HashMap keys. Different representations of the same path will cause lookup failures:
- Relative vs absolute: `lib/uart.hwml` vs `/abs/path/lib/uart.hwml`
- Case sensitivity (Windows): `C:\` vs `c:\`
- Symlinks: `/home/user/project` vs `/home/user/symlink-to-project`

**Solution:** **Always** call `normalize_path()` before any `VfsFileMap` operation. See implementation section for details.

### 2. Collision Detection Must Check `is_concrete` Flag

**Problem:** Parametric and concrete definitions can have the same name:

```hwml
def Fifo (w : Nat) = ...  // Parametric - OK
def Fifo_32 = Fifo 32     // Concrete - must be unique!
```

**Solution:** `StubTable::insert()` only checks collisions for `is_concrete` definitions:

```rust
pub fn insert(&mut self, name: QualifiedName, stub: Stub) -> Result<(), String> {
    if stub.is_concrete {
        if let Some(existing) = self.stubs.get(&name) {
            if existing.is_concrete {
                return Err(format!("Duplicate concrete definition: {}", name));
            }
        }
    }
    self.stubs.insert(name, stub);
    Ok(())
}
```

### 3. File Watcher Must Update VfsFileMap

**Problem:** When user creates new `.hwml` file, `library_declarations()` won't see it until VfsFileMap is updated.

**Solution:** File watcher must call `session.add_file_to_workspace()` which updates the Salsa input:

```rust
fn add_file_to_workspace(&mut self, path: PathBuf, text: String) {
    let canonical = self.normalize_path(&path).unwrap();
    let source_file = SourceFile::new(&mut self.db, canonical.clone(), text);

    let mut files = (*self.vfs_file_map.unwrap().files(&self.db)).clone();
    files.insert(canonical, source_file);
    self.vfs_file_map.unwrap().set_files(&mut self.db).to(Arc::new(files));
}
```

---

## Success Metrics

### Correctness
- [ ] `library_declarations` is a pure `#[salsa::tracked]` query (no IO)
- [ ] All files registered in `VfsFileMap` at initialization
- [ ] File watcher updates `VfsFileMap` when files created/deleted
- [ ] Salsa invalidates `library_declarations` when `VfsFileMap` changes
- [ ] CLI builds are hermetic (snapshot at init, immune to concurrent file changes)
- [ ] Collision detection only applies to `is_concrete` definitions
- [ ] Parametric definitions can have same name across files (no error)
- [ ] Concrete definitions with same name cause hard error with clear diagnostic

### Performance
- [ ] Editing function body → only that file re-parsed
- [ ] LSP response time <10ms for single-file edits
- [ ] File discovery at init takes <100ms for 1000 files
- [ ] Cache hit rate >95% on incremental LSP edits

---

## References

**rust-analyzer SourceRoot:**
- https://github.com/rust-lang/rust-analyzer/blob/master/crates/base-db/src/input.rs

**Salsa Documentation:**
- https://salsa-rs.github.io/salsa/

**File watching:**
- `notify` crate: https://docs.rs/notify/

**Related ADRs:**
- [[ADR-007-salsa-driven-compilation]] - Demand-driven queries
- [[ADR-008-vfs-abstraction]] - VFS feeds Salsa inputs
- [[ADR-006-multi-layer-build-configuration]] - Workspace manifests

---

**Status:** Approved ✅
**Next Steps:**
1. ✅ Implement `VfsFileMap` Salsa input with `Arc<HashMap<PathBuf, SourceFile>>`
2. ✅ Add `is_concrete` flag to `Stub` struct
3. ✅ Update collision detection in `StubTable::insert()`
4. 🚧 Implement `library_declarations()` query in `hwml-db`
5. Add file discovery to `CompilerSession::new_for_workspace()`
6. Integrate `notify` file watcher for LSP with path normalization
7. Test collision detection: Duplicate concrete defs → error, parametric defs → OK
8. Test file creation: Create new file → verify `library_declarations` invalidates
9. Measure LSP response time (target: <10ms for single-file edits)


