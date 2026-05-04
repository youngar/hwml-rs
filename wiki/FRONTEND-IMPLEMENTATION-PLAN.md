# HWML Frontend Implementation Plan: Multi-File Compilation + Working LSP

**Date:** 2026-05-03
**Goal:** Get the language frontend up and running so we can compile libraries and use LSP in a repository
**Status:** Implementation roadmap based on current progress

---

## Current State Assessment

### ✅ What's Complete (Phase 1)

**Core Kernel (`hwml-core`):**
- ✅ NbE engine with 4-quadrant architecture (Syntax, Value, TySyntax, Ty)
- ✅ Evaluation and quotation working perfectly
- ✅ De Bruijn index ↔ level conversion proven correct
- ✅ All 7 tests passing (beta reduction, dependent Pi, neutrals)
- ✅ Bidirectional type checking
- ✅ Pattern unification
- ✅ LCF-style trusted kernel

**Elaborator (`hwml-elab`):**
- ✅ Core infrastructure complete
- ✅ Constraint-based elaboration with metavariables
- ✅ Three-phase design: lowering → solving → zonking
- ✅ Basic expression elaboration (synth/check)
- ✅ Declaration elaboration (`def`, primitives)
- ✅ Name resolution (Resolver + StubTable)

**Surface Language (`hwml-surface`):**
- ✅ LALRPOP parser for surface syntax
- ✅ Lexer and grammar
- ✅ Surface AST (Program, Statement, Expression)

**Salsa Integration (`hwml-core`, `hwml-db`):**
- ✅ Basic Salsa database in `hwml-core`
- ✅ `hwml-db` with File input, parsing, diagnostics accumulation
- ✅ Line info tracking for error messages

**LSP Server (`hwml-lsp-server`):**
- ✅ Basic LSP server skeleton with:
  - Document open/change tracking
  - Incremental text edits
  - Diagnostic publishing
  - Salsa-based compilation

**Documentation (`mdbook-hwml`):**
- ✅ mdBook preprocessor for validating code snippets
- ✅ Build-time validation of HWML code

### 🔄 What's In Progress (Phase 1.5)

**Inductive Types & Pattern Matching:**
- 🔄 Type constructors and data constructors
- 🔄 Case expressions with stuck elimination
- 🔄 LET expressions being finalized

### ❌ What's Missing for Multi-File + LSP

**Critical Gaps:**

1. **No Multi-File Support**
   - ❌ No `.hwmli` serialization/deserialization
   - ❌ No `hwml-workspace` manifest parsing implementation
   - ❌ No topological sorting of libraries
   - ❌ No `open` statement elaboration
   - ❌ No cross-file name resolution

2. **No Build System**
   - ❌ No CLI for `hwml build`
   - ❌ No caching (local, user-global, or remote)
   - ❌ No dependency resolution

3. **Limited LSP Capabilities**
   - ❌ No workspace understanding (only single files)
   - ❌ No go-to-definition across files
   - ❌ No completion
   - ❌ No hover info

4. **Missing Compiler Flags**
   - ❌ No `--emit-deps` for dependency files
   - ❌ No `@args.txt` response files
   - ❌ No `--message-format=json`

---

## Implementation Plan: Minimal Viable Frontend

**Goal:** Get from "single-file elaboration" to "multi-library compilation with working LSP" in the shortest path

### Phase A: Multi-File Foundation (2-3 weeks)

**Objective:** Compile a workspace with multiple `.hwml` files and libraries

**⚠️ ARCHITECTURE CHANGE:** Based on ADR-007, ADR-008, ADR-009, we use:
- **Salsa-driven compilation** (no manual topo-sort)
- **VFS abstraction** (unified CLI/LSP file access)
- **rkyv serialization** (zero-copy `.hwmli` loading)

---

**A0: VFS Infrastructure (Days 1-2)**

**Priority:** MUST be done before any multi-file work

**Tasks:**
1. Create `crates/hwml-vfs/`
2. Define `Vfs` trait (see [[ADR-008-vfs-abstraction]])
3. Implement `OsVfs` (reads from disk)
4. Implement `MemoryVfs` (for testing)
5. Add VFS to `HwmlDatabase`
6. Update `file_text` query to use VFS

**Deliverables:**
```rust
// CLI usage
let db = HwmlDatabase::with_os_vfs();

// LSP usage (implemented later)
let db = HwmlDatabase::with_lsp_vfs(lsp_vfs);

// Testing
let db = HwmlDatabase::with_memory_vfs();
let file = db.vfs_mut().create_file(
    PathBuf::from("test.hwml"),
    "def id (A : Type) (x : A) : A = x".to_string()
);
```

**Why first?** LSP requires VFS to typecheck unsaved files. Doing this early prevents rework.

---

**A1: Complete `hwml-workspace` Crate (Days 3-7)**

Priority tasks:
1. ✅ Basic types exist (`LibraryManifest`, `LibraryDep`, `Workspace`)
2. **Implement manifest parsing**
   - Parse `hwml.toml` from disk
   - Extract `[package]`, `[dependencies]`, `[lib]`
   - Handle path dependencies for local development
3. **Implement workspace loading**
   - Find `hwml.toml` files in workspace
   - Return library metadata (NO topological sort - see ADR-007)
4. **File discovery**
   - Read `[sources]` or default to `*.hwml` glob
   - Return list of source files per library

**Deliverables:**
```rust
let workspace = Workspace::load(PathBuf::from("."))?;
let libraries = workspace.libraries(); // HashMap<String, LibraryManifest>
println!("Found {} libraries", libraries.len());
// NO topo_order() method - Salsa handles ordering!
```

**A2: Design `.hwmli` Format (Days 8-10)**

**Purpose:** Serialized compilation artifact for a library

**Decision (ADR-009):** Use **rkyv** for zero-copy serialization

**Why rkyv?**
- Zero-copy loading (<1ms per file, 20x faster than bincode)
- Memory-mapped files (OS manages paging, lower memory usage)
- Schema evolution support (can add fields without breaking old files)
- Validation prevents crashes from corrupted files

**Contents:**
- Library metadata (name, version)
- Exported declarations (types, functions, data constructors)
- Declaration fingerprints (for early cutoff)
- Interface hash (BLAKE3)

**Schema:**
```rust
use rkyv::{Archive, Deserialize, Serialize};

#[derive(Archive, Deserialize, Serialize)]
#[archive(check_bytes)]  // Enable validation
pub struct Hwmli {
    pub version: u32,  // Format version
    pub library_name: String,
    pub library_version: String,  // semver as String for rkyv compat

    // Exported declarations
    pub declarations: Vec<Declaration>,  // From hwml-core

    // For incremental compilation (Phase 2+)
    pub export_interface_hash: [u8; 32],  // BLAKE3
}

impl Hwmli {
    pub fn to_bytes(&self) -> Result<Vec<u8>> {
        Ok(rkyv::to_bytes::<_, 256>(self)?.to_vec())
    }

    pub fn from_mmap(mmap: &[u8]) -> Result<&ArchivedHwmli> {
        rkyv::check_archived_root::<Hwmli>(mmap).map_err(Into::into)
    }
}
```

**A5: Build `.hwmli` Serialization (Days 11-15)**

**Tasks:**
1. Add `rkyv` derives to `hwml-core` types (Declaration, Syntax, etc.)
2. Implement `Hwmli::to_bytes()` (rkyv serialization)
3. Implement `Hwmli::from_mmap()` (zero-copy loading with validation)
4. Create `HwmliCache` for memory-mapped file management
5. Test: Elaborate library → serialize → load → verify equality

**Deliverables:**
```rust
// After elaboration
let hwmli = elaborate_library(db, lib)?;
let bytes = hwmli.to_bytes()?;
std::fs::write(".hwml-build/mylib.hwmli", bytes)?;

// Later, zero-copy load from cache
let file = File::open(".hwml-build/mylib.hwmli")?;
let mmap = unsafe { Mmap::map(&file)? };
let cached_hwmli = Hwmli::from_mmap(&mmap)?;  // Instant, no deserialization!
// `cached_hwmli` is &ArchivedHwmli, usable immediately
```

---

**A3: Implement `open` Statement (Week 2-3)**

**Current state:** Parser recognizes `open` but elaborator ignores it

**Implementation:**
1. Modify `hwml-elab` to track opened libraries
2. When encountering `open Foo`:
   - Query `library_interface(db, workspace, "Foo")` (recursive Salsa call)
   - Extract exported names from `.hwmli`
   - Add to elaboration context (Resolver)
3. Name resolution: `Foo.bar` looks up `bar` in `Foo`'s exports

**Example:**
```rust
// In hwml-elab/src/elaborate.rs
fn elaborate_open(&mut self, open: &surface::Open) -> Result<()> {
    let lib_name = &open.library_name;

    // Salsa automatically handles dependency loading
    let interface = library_interface(self.db, self.workspace, lib_name.clone())?;

    // Add exported names to scope
    for decl in &interface.declarations {
        self.resolver.add_import(decl.name.clone(), decl.clone());
    }

    Ok(())
}
```

---

**A4: Salsa-Driven Compilation (Week 2-3)** ⭐ **Critical - ADR-007**

**Current:** `hwml-db` only handles single File input

**Decision:** NO manual topological sorting. Let Salsa drive execution via recursive queries.

**Upgrade to workspace-aware queries:**

```rust
// crates/hwml-db/src/queries.rs

// Input: Workspace root path
#[salsa::input]
pub struct WorkspaceRoot {
    #[return_ref]
    pub path: PathBuf,
}

// Tracked: Parse all manifests in workspace
#[salsa::tracked]
pub fn workspace_libraries(
    db: &dyn Db,
    root: WorkspaceRoot,
) -> Arc<HashMap<String, LibraryManifest>> {
    // Find and parse all hwml.toml files
    // Return map of library name → manifest
    // NO topological sort here!
}

// Tracked: Get source files for a library
#[salsa::tracked]
pub fn library_source_files(
    db: &dyn Db,
    root: WorkspaceRoot,
    lib_name: String,
) -> Vec<FileId> {
    let libs = workspace_libraries(db, root);
    let manifest = &libs[&lib_name];
    // Return FileIds for all .hwml files in this library
}

// Tracked: Elaborate a library (RECURSIVE on dependencies!)
#[salsa::tracked]
pub fn library_interface(
    db: &dyn Db,
    root: WorkspaceRoot,
    lib_name: String,
) -> Result<Hwmli, ElabError> {
    let libs = workspace_libraries(db, root);
    let manifest = &libs[&lib_name];

    // 🔥 CRITICAL: Recursive query calls for dependencies
    // Salsa automatically:
    // - Handles execution order (leaves-first)
    // - Memoizes results
    // - Detects cycles
    for dep in &manifest.dependencies {
        let _dep_interface = library_interface(db, root, dep.name.clone())?;
        // Salsa caches this result, won't recompute if called again
    }

    // Now elaborate this library
    // ⚠️ THIS is where constraint solving happens (ADR-010)
    let files = library_source_files(db, root, lib_name.clone());
    elaborate_library_with_local_solver(db, root, lib_name, files)
}

// Tracked: Elaborate library with local constraint solver
// This is where metavariables live and die (ADR-010)
#[salsa::tracked]
pub fn elaborate_library_with_local_solver(
    db: &dyn Db,
    root: WorkspaceRoot,
    lib_name: String,
    files: Vec<FileId>,
) -> Result<Hwmli, ElabError> {
    // Build SCC graph for mutual recursion within library
    let sccs = compute_declaration_sccs(db, files)?;

    let mut elaborated_decls = HashMap::new();

    // Process each SCC with LOCAL metavariable context
    for scc in sccs.topo_order() {
        // 🔥 Metavariables created, solved, and destroyed here
        let result = elaborate_scc_with_local_state(db, root, lib_name.clone(), scc)?;
        elaborated_decls.extend(result);
    }

    // ✅ Return pure, metavariable-free declarations
    Ok(Hwmli {
        version: 1,
        library_name: lib_name,
        declarations: elaborated_decls.into_values().collect(),
    })
}

// NOT a Salsa query! Regular function with local state.
fn elaborate_scc_with_local_state(
    db: &dyn Db,
    root: WorkspaceRoot,
    lib_name: String,
    scc: Scc,
) -> Result<HashMap<DeclId, Declaration>, ElabError> {
    // Fresh metavariable context (local to this SCC)
    let mut elab_state = ElabState::new();

    // Phase 1: Elaborate signatures
    let signatures = elaborate_signatures(&mut elab_state, db, &scc)?;
    solve_constraints_to_fixpoint(&mut elab_state)?;
    let zonked_sigs = zonk_signatures(&elab_state, signatures)?;

    // Phase 2: Elaborate bodies
    elab_state.clear_for_bodies();
    let bodies = elaborate_bodies(&mut elab_state, db, &scc, &zonked_sigs)?;
    solve_constraints_to_fixpoint(&mut elab_state)?;
    let zonked_bodies = zonk_terms(&elab_state, bodies)?;

    // Phase 3: Kernel verification (LCF boundary)
    for (id, (sig, body)) in zonked_sigs.iter().zip(&zonked_bodies) {
        kernel::verify_declaration(db, body, sig)?;
    }

    // ElabState destroyed here, return pure CoreTerms
    Ok(zonked_sigs.into_iter()
        .zip(zonked_bodies.into_iter())
        .map(|((id, sig), (_, body))| (id, Declaration { sig, body }))
        .collect())
}
```

**See [[ADR-010-metavariable-scoping-constraint-solver]] for complete details on the three-level architecture.**

**Why this works (ADR-007):**
- Calling `library_interface(db, workspace, "uart")` automatically triggers:
  1. `library_interface(db, workspace, "fifo")` (dependency)
  2. Salsa memoizes fifo's result
  3. Then elaborates uart
- **NO manual topological sort needed!**
- **Incremental compilation automatic:** Change fifo → Salsa recomputes fifo + uart only
- **Cycle detection automatic:** Salsa panics with precise stack trace

**CLI usage:**
```rust
fn main() -> Result<()> {
    let db = HwmlDatabase::with_os_vfs();
    let workspace = WorkspaceRoot::new(&db, PathBuf::from("."));

    // Get all libraries
    let libs = workspace_libraries(&db, workspace);

    // Build each library (order doesn't matter!)
    for lib_name in libs.keys() {
        let interface = library_interface(&db, workspace, lib_name.clone())?;

        // Write to cache
        let bytes = interface.to_bytes()?;
        std::fs::write(format!(".hwml-build/{}.hwmli", lib_name), bytes)?;
    }

    Ok(())
}
```

---

### Phase B: CLI Build Tool (1 week)

**Objective:** `hwml build` that compiles a workspace

**B1: Implement `hwml` CLI (Days 1-2)**

**Current:** `crates/hwml/src/main.rs` exists but minimal

**Features:**
```bash
hwml build                  # Build current workspace
hwml build --manifest path/to/hwml.toml
hwml clean                  # Remove .hwml-build/
hwml check                  # Type-check only, no artifacts
```

**Implementation:**
- Use `clap` for argument parsing
- Find workspace root (walk up for `hwml.toml` or `hwml-workspace.toml`)
- Create `HwmlDatabase` with OsVfs
- Load workspace: `WorkspaceRoot::new(&db, path)`
- For each library: call `library_interface(&db, workspace, lib_name)`
  - Salsa handles dependencies automatically (ADR-007)
  - Write resulting `.hwmli` to `.hwml-build/`
- Print progress, errors

**Example:**
```rust
use clap::{Parser, Subcommand};

#[derive(Parser)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    Build { manifest: Option<PathBuf> },
    Check,
    Clean,
}

fn main() -> Result<()> {
    let cli = Cli::parse();

    match cli.command {
        Commands::Build { manifest } => {
            let root = find_workspace_root(manifest)?;
            let db = HwmlDatabase::with_os_vfs();
            let workspace = WorkspaceRoot::new(&db, root);

            // Build all libraries
            let libs = workspace_libraries(&db, workspace);
            for lib_name in libs.keys() {
                println!("Building {}...", lib_name);
                let interface = library_interface(&db, workspace, lib_name.clone())?;

                // Write .hwmli
                let bytes = interface.to_bytes()?;
                let path = format!(".hwml-build/{}.hwmli", lib_name);
                std::fs::create_dir_all(".hwml-build")?;
                std::fs::write(&path, bytes)?;
                println!("  → {}", path);
            }
        }
        Commands::Clean => {
            std::fs::remove_dir_all(".hwml-build")?;
        }
        _ => todo!(),
    }

    Ok(())
}
```

**B2: Basic Caching (Days 3-5)**

**Tier 1 only:** Local build directory

**Strategy:**
- Input hash = hash(source files content + dependency .hwmli hashes)
- Output = `.hwml-build/{library_name}-{input_hash}.hwmli`
- Hardlink to `.hwml-build/{library_name}.hwmli` for easy discovery

**Cache invalidation:**
- Source file changed → input hash changes → rebuild
- Dependency changed → input hash changes → rebuild

**B3: Pretty Error Messages (Days 5-7)**

**Current:** Basic diagnostics in LSP

**Improvements:**
- Use `codespan-reporting` for pretty errors with source snippets
- Show error location across files: `lib/uart/src/types.hwml:42:5`
- Color output in terminal

---

### Phase C: LSP Workspace Support (1-2 weeks)

**Objective:** LSP understands workspaces, provides go-to-definition across files

**Prerequisites:** VFS abstraction (ADR-008) enables LSP to work with unsaved files

**C1: LSP VFS Integration (Days 1-2)**

**Implement `LspVfs`:**
```rust
pub struct LspVfs {
    files: HashMap<FileId, LspFile>,
    uri_to_id: HashMap<lsp_types::Url, FileId>,
    next_id: u32,
}

struct LspFile {
    uri: lsp_types::Url,
    text: String,  // In-memory buffer (may be unsaved)
    version: i32,
}
```

**Integration with LSP server:**
```rust
struct LanguageServer {
    db: HwmlDatabase,
    vfs: LspVfs,
}

fn on_did_open(&mut self, params: DidOpenTextDocumentParams) {
    let file_id = self.vfs.create_file(
        params.text_document.uri.to_file_path().unwrap(),
        params.text_document.text
    );
    // Salsa query will now read from VFS, not disk
}

fn on_did_change(&mut self, params: DidChangeTextDocumentParams) {
    let file_id = self.vfs.file_by_uri(&params.text_document.uri).unwrap();
    self.vfs.update_file(file_id, params.content_changes[0].text.clone());

    // Salsa automatically invalidates affected queries
    // Diagnostics will use NEW text from VFS
}
```

**C2: Workspace Discovery (Days 3-4)**

**Current:** LSP only tracks individual documents, no workspace concept

**Implementation:**
1. On LSP `initialize`, read `InitializeParams.rootUri`
2. Find workspace root (look for `hwml-workspace.toml` or `hwml.toml`)
3. Create database: `HwmlDatabase::with_lsp_vfs(lsp_vfs)`
4. Load workspace: `WorkspaceRoot::new(&db, root_path)`
5. Pre-discover all source files in workspace (add to VFS)

**C2: Cross-File Name Resolution (Days 3-5)**

**Enable go-to-definition across files:**

1. When user requests `textDocument/definition` on an identifier:
   - Parse identifier path: `Foo.bar.baz`
   - Look up `Foo` in opened libraries
   - Load `Foo.hwmli` to get exported declarations
   - Find declaration for `bar.baz`
   - Return source location from original `.hwml` file

2. Store source locations in `.hwmli`:
   ```rust
   pub struct Hwmli {
       // ...
       pub source_map: HashMap<DeclId, SourceRange>,
   }
   ```

**C3: Hover Info (Days 6-8)**

**Show type on hover:**

```rust
// User hovers over `myFunc`
// LSP looks up type: `Vec A n -> A`
// Returns formatted string with pretty-printing
```

**Implementation:**
- `textDocument/hover` handler
- Look up identifier in context
- Get type from elaboration
- Pretty-print type using `hwml-core` quote
- Return as markdown

**C4: Basic Completion (Days 9-10)**

**Show available names from opened libraries:**

```rust
// User types: `Std.Vec.`
// LSP returns: [map, filter, fold, length, ...]
```

**Implementation:**
- `textDocument/completion` handler
- Parse partial identifier
- Look up library (`Std.Vec`)
- Return all exported names from that library

---

### Phase D: Integration & Polish (1 week)

**D1: VS Code Extension (Days 1-3)**

**Minimal extension:**

```json
{
  "name": "hwml",
  "displayName": "HWML",
  "version": "0.1.0",
  "engines": { "vscode": "^1.75.0" },
  "activationEvents": ["onLanguage:hwml"],
  "main": "./out/extension.js",
  "contributes": {
    "languages": [{
      "id": "hwml",
      "extensions": [".hwml"],
      "configuration": "./language-configuration.json"
    }],
    "grammars": [{
      "language": "hwml",
      "scopeName": "source.hwml",
      "path": "./syntaxes/hwml.tmLanguage.json"
    }]
  }
}
```

**Extension activation:**
```typescript
export function activate(context: vscode.ExtensionContext) {
    const serverPath = context.asAbsolutePath(
        path.join('bin', 'hwml-lsp-server')
    );

    const serverOptions: ServerOptions = {
        command: serverPath,
        args: []
    };

    const clientOptions: LanguageClientOptions = {
        documentSelector: [{ scheme: 'file', language: 'hwml' }]
    };

    const client = new LanguageClient(
        'hwml',
        'HWML Language Server',
        serverOptions,
        clientOptions
    );

    client.start();
}
```

**D2: Example Project (Days 4-5)**

**Create `examples/uart-controller/`:**

```
examples/uart-controller/
├── hwml-workspace.toml
├── lib/
│   ├── fifo/
│   │   ├── hwml.toml
│   │   └── src/
│   │       ├── types.hwml
│   │       └── impl.hwml
│   └── uart/
│       ├── hwml.toml
│       └── src/
│           ├── types.hwml
│           ├── uart.hwml
│           └── testbench.hwml
└── .vscode/
    └── settings.json  # Points to hwml-lsp-server
```

**Test workflow:**
1. Open in VS Code
2. LSP activates, discovers workspace
3. Edit `uart/src/uart.hwml` → LSP shows errors in real-time
4. Go to definition: `Fifo.Queue` → jumps to `fifo/src/types.hwml`
5. Run `hwml build` → compiles both libraries, caches artifacts
6. Edit `fifo/src/types.hwml` → `hwml build` only recompiles `uart` (depends on fifo)

**D3: Documentation (Days 6-7)**

**Update wiki and docs:**

1. User guide: "Getting Started with Multi-File Projects"
2. Reference: "Workspace Configuration (`hwml.toml`)"
3. Tutorial: "Building Your First HWML Library"
4. LSP guide: "Setting Up the Language Server"

---

## Implementation Timeline

**Estimated:** 5-7 weeks total

| Phase | Duration | Deliverable |
|-------|----------|-------------|
| **Phase A** | 2-3 weeks | Multi-file compilation working |
| **Phase B** | 1 week | `hwml build` CLI with caching |
| **Phase C** | 1-2 weeks | LSP with workspace support |
| **Phase D** | 1 week | VS Code extension + example |

**Parallel work opportunities:**
- VS Code extension (D1) can be developed alongside Phase C
- Documentation (D3) can be written as features complete

---

## Success Criteria

### Minimal Viable Product (MVP)

**After Phase A + B:**
- [ ] Can write `hwml.toml` for a library
- [ ] Can run `hwml build` to compile workspace
- [ ] Libraries can depend on each other via `open` statements
- [ ] `.hwmli` artifacts cached in `.hwml-build/`
- [ ] Incremental builds work (change one library → only dependents rebuild)

**After Phase C:**
- [ ] LSP understands workspace structure
- [ ] Go-to-definition works across files
- [ ] Hover shows types
- [ ] Diagnostics shown in editor in real-time
- [ ] Completion suggests available names

**After Phase D:**
- [ ] VS Code extension installable
- [ ] Example project demonstrating multi-library setup
- [ ] Documentation for users

---

## Related Documents

**Design Documents:**
- `design/package-manager.md` - Package manager architecture
- `design/to-ingest/PHASE1-COMPLETE.md` - What's been completed
- `design/to-ingest/PHASE1.5-PLAN.md` - Current phase goals

**Wiki References:**
- [[decisions/ADR-006-multi-layer-build-configuration]] - Build configuration layers
- [[research/buck2-integration-patterns]] - Future: Buck2 integration
- [[research/build-system-caching-synthesis]] - Advanced caching strategies

**Implementation Status:**
- `ELABORATOR_PROGRESS.md` - Elaborator status
- `PHASE1_IMPLEMENTATION_STATUS.md` - Package manager progress

---

## Next Immediate Actions

**Week 1 Priorities:**

1. **Implement manifest parsing** (Days 1-3)
   - Create `hwml-workspace/src/manifest.rs`
   - Parse `hwml.toml` files
   - Write unit tests

2. **Design `.hwmli` format** (Days 4-5)
   - Add serde to hwml-core types
   - Define Hwmli struct
   - Implement serialization

3. **Workspace loading** (Days 6-7)
   - Implement topo-sort
   - Cycle detection
   - File discovery

**Ready to start implementation!**
