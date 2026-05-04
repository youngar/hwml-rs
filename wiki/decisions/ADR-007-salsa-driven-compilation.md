# ADR-007: Salsa-Driven Compilation (Not Topological Sort)

**Status:** Approved
**Date:** 2026-05-03
**Updated:** 2026-05-03 (Added reference to ADR-010)
**Deciders:** Core team
**Related:** [[ADR-006-multi-layer-build-configuration]], [[ADR-010-metavariable-scoping-constraint-solver]], [[research/buck2-integration-patterns]], [[research/build-system-caching-synthesis]]

---

## Context

When implementing multi-library compilation for HWML, we need to decide how to execute the compilation pipeline:

**Traditional approach:** 
- Parse all `hwml.toml` manifests
- Build dependency graph
- Topologically sort libraries (leaves-first)
- Iterate through sorted list, compiling each library

**Demand-driven approach:**
- Define Salsa queries for compilation units
- Call top-level query
- Let Salsa automatically handle execution order, memoization, and cycle detection

We already use Salsa for single-file incremental compilation (Phase 1 complete). The question is: should we introduce a separate "workspace orchestration" layer, or let Salsa drive everything?

---

## Decision

**We adopt Salsa-driven compilation throughout.** There will be NO explicit topological sort or iteration loop in the compiler. Instead, we define queries that naturally express dependencies:

```rust
#[salsa::tracked]
pub fn library_interface(
    db: &dyn Db, 
    workspace: WorkspaceRoot, 
    lib_name: String
) -> Result<Hwmli, ElabError> {
    let manifest = &workspace_libraries(db, workspace)[&lib_name];
    
    // When this library opens a dependency, recursively query it
    for dep in &manifest.dependencies {
        let _dep_interface = library_interface(db, workspace, dep.name.clone())?;
        // Salsa memoizes this call automatically
    }
    
    // Elaborate this library
    elaborate_library_with_local_solver(db, workspace, lib_name)
}
```

**Execution is query-driven:**
- Call `library_interface(db, workspace, "my-top-level-lib")`
- Salsa recursively executes dependency queries as needed
- Execution order emerges naturally from query dependencies
- No manual scheduling required

**Note:** The `elaborate_library_with_local_solver` query contains all metavariable/constraint solving logic. See [[ADR-010-metavariable-scoping-constraint-solver]] for details on how elaboration integrates with Salsa while maintaining pure, cacheable outputs.

---

## Rationale

### 1. Salsa Already IS a Dependency Graph Engine

Salsa's core purpose is to:
- Track query dependencies dynamically
- Memoize results
- Incrementally recompute when inputs change
- Detect cycles

**Writing a separate topo-sort is duplicating Salsa's functionality poorly.**

From the Salsa documentation:
> "Salsa is a demand-driven incremental computation framework... When a query calls another query, Salsa tracks this dependency automatically."

If we implement manual topological sorting, we're:
- Reimplementing dependency tracking (Salsa does this)
- Reimplementing memoization (Salsa does this)
- Reimplementing cycle detection (Salsa does this)

### 2. Better Cycle Detection

**Manual approach:**
```rust
fn topo_sort(libs: &HashMap<String, Manifest>) -> Result<Vec<String>> {
    // 50+ lines of cycle detection logic
    // Returns cycle path: ["A", "B", "C", "A"]
    // BUT: Only detects library-level cycles
}
```

**Salsa approach:**
```rust
// Salsa panics with full query stack trace:
// library_interface("A") -> library_interface("B") -> library_interface("A")
// Shows EXACTLY where the cycle occurred
// Plus: Detects cycles at query granularity (could be within a single library)
```

### 3. Incremental Compilation is Automatic

**Manual approach:**
```rust
fn rebuild_workspace(old_cache: &Cache) -> Vec<String> {
    let mut to_rebuild = Vec::new();
    
    for lib in topo_order {
        // Check if lib or any dependency changed
        if lib_changed(lib) || any_dep_changed(lib, old_cache) {
            to_rebuild.push(lib);
        }
    }
    
    for lib in to_rebuild {
        compile(lib);  // Wastes work if earlier dep already compiled
    }
}
```

**Salsa approach:**
```rust
// Change a file
db.set_file_text(file_id, new_text);

// Just call the query
let result = library_interface(db, workspace, "uart");
// Salsa AUTOMATICALLY:
// - Detects that fifo's files changed
// - Recomputes library_interface("fifo")
// - Recomputes library_interface("uart") because it depends on fifo
// - Skips everything else (cached)
```

### 4. Unified CLI and LSP

Both the CLI and LSP can use the exact same queries:

**CLI:**
```rust
fn main() {
    let db = HwmlDatabase::with_os_vfs();
    let workspace = WorkspaceRoot::new(&db, PathBuf::from("."));
    
    // Build all libraries
    for lib in workspace_libraries(&db, workspace).keys() {
        library_interface(&db, workspace, lib.clone())?;
    }
}
```

**LSP:**
```rust
fn on_file_change(&mut self, file_id: FileId, new_text: String) {
    // Update VFS
    self.db.set_file_text(file_id, new_text);
    
    // Salsa recomputes affected queries automatically
    // No need to figure out what to rebuild!
    let lib = file_to_library(&self.db, file_id);
    let diagnostics = library_diagnostics(&self.db, self.workspace, lib);
    send_diagnostics(diagnostics);
}
```

**Persistent Worker (Buck2):**
```rust
fn worker_loop() {
    loop {
        let request = read_request();
        
        // Update files that changed
        for (file, text) in request.changed_files {
            db.set_file_text(file, text);
        }
        
        // Same query as CLI and LSP!
        let result = library_interface(&db, workspace, request.lib_name)?;
        send_response(result);
    }
}
```

### 5. Fine-Grained Parallelism (Future)

Salsa 2022+ supports parallel query execution. With query-driven compilation, parallelism is automatic:

```rust
// Salsa can execute these in parallel:
let fifo_interface = library_interface(db, ws, "fifo");    // Independent
let axi_interface = library_interface(db, ws, "axi");      // Independent
// Then execute uart once both are done:
let uart_interface = library_interface(db, ws, "uart");    // Depends on both
```

With manual topo-sort, we'd have to implement this parallelism ourselves.

---

## Consequences

### Positive

1. **Less code:** No topological sort implementation (~100-200 lines eliminated)
2. **Better errors:** Salsa's cycle detection gives precise stack traces
3. **Automatic incrementality:** File change → Salsa recomputes only affected queries
4. **Unified architecture:** CLI, LSP, and persistent worker share exact same code path
5. **Future-proof:** When Salsa adds parallel queries, we get parallelism for free
6. **Demand-driven:** Only elaborate libraries actually requested (good for LSP)

### Negative

1. **Learning curve:** Team must understand Salsa query model
   - *Mitigation:* Salsa is widely used (rust-analyzer, rust compiler, Sorbet). Good documentation exists.

2. **Panics on cycles:** Salsa panics rather than returning `Result`
   - *Mitigation:* This is actually better for development (immediate detection). We can configure Salsa to use `Result` if needed.

3. **Query overhead:** Small cost per query invocation
   - *Mitigation:* Negligible compared to compilation cost. Rust compiler uses Salsa extensively.

### Neutral

- **Execution order non-deterministic:** Queries execute in dependency order, but exact scheduling varies
  - This is fine! Compilation is deterministic (same inputs → same outputs), even if execution order differs.

---

## Alternatives Considered

### Alternative 1: Manual Topological Sort

**What:** Implement traditional topo-sort, iterate over libraries

**Why rejected:**
- Duplicates Salsa's functionality
- Requires manual dependency tracking
- No automatic incremental compilation
- Cycle detection less precise
- Harder to unify CLI and LSP

### Alternative 2: Hybrid (Topo-sort + Salsa)

**What:** Use topo-sort for library order, Salsa for within-library incrementality

**Why rejected:**
- Complexity: Two dependency tracking systems
- Salsa's incremental compilation only works within libraries, not across them
- Still requires manual "what changed?" logic

### Alternative 3: No Salsa (Pure Batch Compilation)

**What:** Remove Salsa entirely, implement traditional batch compiler

**Why rejected:**
- LSP would be impossibly slow (recompile everything on each edit)
- No incremental compilation
- Contradicts Phase 1 decision to use Salsa

---

## Implementation Notes

### Query Structure

```rust
// Input: Workspace root
#[salsa::input]
pub struct WorkspaceRoot {
    pub path: PathBuf,
}

// Tracked: Parse all manifests
#[salsa::tracked]
pub fn workspace_libraries(
    db: &dyn Db, 
    root: WorkspaceRoot
) -> Arc<HashMap<String, LibraryManifest>> {
    // Parse all hwml.toml files in workspace
    // Return map of library name → manifest
}

// Tracked: Get source files for a library
#[salsa::tracked]
pub fn library_source_files(
    db: &dyn Db,
    root: WorkspaceRoot,
    lib_name: String,
) -> Vec<FileId> {
    // Read manifest, return FileIds for all .hwml files
}

// Tracked: Elaborate a library (recursive on dependencies)
#[salsa::tracked]
pub fn library_interface(
    db: &dyn Db,
    root: WorkspaceRoot,
    lib_name: String,
) -> Result<Hwmli, ElabError> {
    let manifest = &workspace_libraries(db, root)[&lib_name];
    
    // Recursive query calls for dependencies
    for dep in &manifest.dependencies {
        let _dep_interface = library_interface(db, root, dep.name.clone())?;
    }
    
    // Elaborate this library
    let files = library_source_files(db, root, lib_name.clone());
    elaborate_library_with_local_solver(db, root, lib_name, files)
}
```

**Important:** The `elaborate_library_with_local_solver` query is where metavariable/constraint solving happens. See [[ADR-010-metavariable-scoping-constraint-solver]] for the complete architecture. Key points:

- **Metavariables never escape:** The query creates a local `ElabState`, solves constraints, zonks (replaces metavars with solutions), and returns pure `CoreTerm`s
- **Deterministic output:** Same Surface AST → same Core AST (required for Buck2 caching)
- **LCF boundary:** Kernel verification happens inside the query, kernel never sees metavariables

This ensures Salsa can cache elaboration results while supporting full dependent type elaboration with constraint solving.

### Cycle Handling

Salsa will panic with a message like:
```
thread 'main' panicked at 'cycle detected:
  library_interface("uart")
  library_interface("fifo")
  library_interface("uart")
```

We can catch this panic and convert to a user-friendly error:
```rust
let result = std::panic::catch_unwind(|| {
    library_interface(db, workspace, lib_name)
});

match result {
    Ok(Ok(hwmli)) => Ok(hwmli),
    Ok(Err(e)) => Err(e),  // Elaboration error
    Err(_) => Err(ElabError::DependencyCycle),  // Salsa cycle panic
}
```

---

## Success Metrics

- [ ] No topological sort code in codebase
- [ ] Cycle detection catches circular dependencies
- [ ] CLI and LSP use identical query paths
- [ ] Incremental compilation works: change one file → only affected libraries recompute
- [ ] Parallel query execution works when Salsa supports it

---

## References

**Salsa Documentation:**
- https://github.com/salsa-rs/salsa
- https://salsa-rs.github.io/salsa/

**Related ADRs:**
- [[ADR-006-multi-layer-build-configuration]] - Build configuration system
- [[research/buck2-integration-patterns]] - Persistent worker using same queries

**Examples in the Wild:**
- rust-analyzer: Uses Salsa for all compilation queries
- Sorbet (Stripe's Ruby typechecker): Salsa-driven execution
- Rust compiler: Uses Salsa-like query system (predates Salsa crate)

---

**Status:** Approved  
**Next Steps:**
1. Design workspace query structure (see Implementation Notes)
2. Implement `library_interface` query with dependency recursion
3. Remove any topo-sort code from early prototypes
4. Test cycle detection with circular dependency example
