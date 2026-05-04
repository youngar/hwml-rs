# HWML Frontend Architecture Summary

**Date:** 2026-05-03
**Updated:** 2026-05-03 (Added ADR-010: Constraint Solver Integration)
**Status:** Architecture decisions approved, ready for implementation
**Full Plan:** [[FRONTEND-IMPLEMENTATION-PLAN]]

---

## The Four Pillars

HWML's frontend architecture is built on four state-of-the-art decisions:

### 1. 🔄 Salsa-Driven Compilation (ADR-007)

**NO manual topological sorting.** Execution is demand-driven via recursive Salsa queries.

```rust
#[salsa::tracked]
pub fn library_interface(db: &dyn Db, workspace: WorkspaceRoot, lib_name: String) 
    -> Result<Hwmli, ElabError> 
{
    // Recursively query dependencies
    for dep in &manifest.dependencies {
        library_interface(db, workspace, dep.name.clone())?;
        // Salsa handles: execution order, memoization, cycle detection
    }
    
    elaborate_library(db, lib_name)
}
```

**Benefits:**
- Automatic execution order (leaves-first emerges naturally)
- Automatic incremental compilation (Salsa tracks changes)
- Automatic cycle detection (precise stack traces)
- Unified CLI/LSP (same query paths)

**Reference:** [[decisions/ADR-007-salsa-driven-compilation]]

---

### 2. 📁 Virtual File System (ADR-008)

**Compiler NEVER directly accesses filesystem.** All file operations go through VFS trait.

```rust
pub trait Vfs {
    fn file_text(&self, id: FileId) -> Option<String>;
    fn create_file(&mut self, path: PathBuf, text: String) -> FileId;
    fn update_file(&mut self, id: FileId, text: String);
}

// CLI:     OsVfs      (reads from disk)
// LSP:     LspVfs     (in-memory buffers, unsaved files)
// Testing: MemoryVfs  (pure in-memory, no I/O)
```

**Benefits:**
- LSP typechecks unsaved files (as user types)
- Fast unit tests (no disk I/O, no tempfiles)
- Unified code paths (CLI and LSP share same compiler core)

**Reference:** [[decisions/ADR-008-vfs-abstraction]]

---

### 3. ⚡ Zero-Copy Serialization (ADR-009)

**Use `rkyv` for instant loading.** `.hwmli` files are memory-mapped and used directly.

```rust
// Write
let bytes = hwmli.to_bytes()?;
std::fs::write(".hwml-build/lib.hwmli", bytes)?;

// Zero-copy load (instant, no deserialization!)
let file = File::open(".hwml-build/lib.hwmli")?;
let mmap = unsafe { Mmap::map(&file)? };
let archived = rkyv::check_archived_root::<Hwmli>(&mmap)?;
// `archived` usable immediately
```

**Performance:**
- Load time: <1ms per file (20x faster than bincode)
- LSP startup: <100ms for 50 libraries
- Memory: OS manages paging, only loads accessed data

**Reference:** [[decisions/ADR-009-rkyv-zero-copy-serialization]]

---

### 4. 🧠 Metavariable Scoping (ADR-010)

**Metavariables NEVER escape Salsa queries.** Constraint solving is local to query execution.

**The Three-Level Architecture:**

**Level 1: Cross-Library (Salsa)**
```rust
#[salsa::tracked]
pub fn library_interface(db: &dyn Db, root: WorkspaceRoot, lib_name: String)
    -> Result<Hwmli, ElabError>
{
    // Salsa handles cross-library dependencies
    for dep in &manifest.dependencies {
        library_interface(db, root, dep.name.clone())?;
    }
    elaborate_library_with_local_solver(db, root, lib_name, files)
}
```

**Level 2: Within-Library (SCC Solver)**
```rust
#[salsa::tracked]
pub fn elaborate_library_with_local_solver(...) -> Result<Hwmli> {
    let sccs = compute_declaration_sccs(db, files)?;

    for scc in sccs.topo_order() {
        elaborate_scc_with_local_state(db, scc)?; // Fresh ElabState
    }

    Ok(Hwmli { /* pure, metavariable-free */ })
}
```

**Level 3: SCC Elaboration (Local Solver)**
```rust
fn elaborate_scc_with_local_state(...) -> Result<...> {
    let mut elab_state = ElabState { metas, worklist };

    // Elaborate → Solve constraints → Zonk (replace metavars)
    solve_constraints_to_fixpoint(&mut elab_state)?;

    // ElabState destroyed, return pure CoreTerms
}
```

**Benefits:**
- Salsa caching works (pure inputs/outputs)
- Deterministic builds (same inputs → same outputs)
- No false cycle panics (constraint iteration is local)
- LCF kernel never sees metavariables

**Reference:** [[decisions/ADR-010-metavariable-scoping-constraint-solver]]

---

## How They Work Together

```
┌──────────────────────────────────────────────────────────────┐
│                         CLI or LSP                            │
└────────────┬─────────────────────────────────────┬───────────┘
             │                                     │
             v                                     v
      ┌──────────┐                          ┌──────────┐
      │  OsVfs   │  (CLI reads from disk)   │  LspVfs  │
      └────┬─────┘                          └─────┬────┘
           │                                      │
           └────────────┬─────────────────────────┘
                        v
                ┌───────────────┐
                │ Salsa Queries │  (demand-driven)
                └───────┬───────┘
                        │
          ┌─────────────┼─────────────┐
          v             v             v
    library_interface  ←→  file_text  ←→  parse_file
          │                               (recursive)
          v
    ┌─────────────┐
    │ .hwmli file │  (rkyv zero-copy)
    └─────────────┘
```

**Flow:**
1. **VFS** provides file text (from disk or memory, depending on frontend)
2. **Salsa** queries drive compilation (automatic execution order, cross-library)
3. **Local solver** handles metavariables/constraints (intra-library, per SCC)
4. **rkyv** loads dependencies instantly (zero-copy mmap)
5. **Result:** Fast, deterministic, incremental compilation for both CLI and LSP

---

## Implementation Phases

**See:** [[FRONTEND-IMPLEMENTATION-PLAN]] for full 5-7 week roadmap

### Phase A0: VFS Infrastructure (Week 1, Days 1-2) ⭐ CRITICAL FIRST

1. Create `crates/hwml-vfs/`
2. Implement `OsVfs`, `MemoryVfs`
3. Add VFS to `HwmlDatabase`
4. Update queries to use VFS

**Why first?** Prevents rework. Both CLI and LSP depend on VFS.

### Phase A: Multi-File Foundation (Weeks 1-3)

- A1: Manifest parsing (`hwml.toml`)
- A2: `.hwmli` format design (rkyv)
- A3: `open` statement implementation
- A4: Salsa workspace queries (recursive!)
- A5: Serialization implementation

### Phase B: CLI Build Tool (Week 4)

- B1: `hwml build` command
- B2: Basic caching
- B3: Pretty error messages

### Phase C: LSP Workspace Support (Weeks 5-6)

- C1: LSP VFS integration (`LspVfs`)
- C2: Workspace discovery
- C3: Go-to-definition
- C4: Hover, completion

### Phase D: Integration & Polish (Week 7)

- D1: VS Code extension
- D2: Example project (`uart-controller`)
- D3: Documentation

---

## Success Criteria

After implementation:

- [x] **Architecture approved** (ADRs 007, 008, 009 created)
- [ ] No `std::fs::read_to_string` in compiler core (all via VFS)
- [ ] No topological sort code (Salsa handles ordering)
- [ ] LSP startup <100ms for 50 libraries
- [ ] LSP typechecks unsaved files correctly
- [ ] Unit tests use `MemoryVfs` (no disk I/O)
- [ ] `hwml build` compiles multi-library workspaces
- [ ] Incremental builds work (only recompile changed libraries)

---

## References

**Architecture Decision Records:**
- [[decisions/ADR-007-salsa-driven-compilation]]
- [[decisions/ADR-008-vfs-abstraction]]
- [[decisions/ADR-009-rkyv-zero-copy-serialization]]
- [[decisions/ADR-010-metavariable-scoping-constraint-solver]]

**Related ADRs:**
- [[decisions/ADR-006-multi-layer-build-configuration]] - Build configuration layers
- [[research/buck2-integration-patterns]] - Persistent worker, LSP integration

**Implementation Plan:**
- [[FRONTEND-IMPLEMENTATION-PLAN]] - Full 5-7 week roadmap

**Examples in the Wild:**
- rust-analyzer: Salsa + VFS
- Sorbet (Stripe): VFS + daemon architecture
- GHC 9+: Incremental compilation with fingerprints

---

**Ready to start? Begin with Phase A0: VFS Infrastructure!**
