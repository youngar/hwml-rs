# Buck2 Integration for HWML: Quick Summary

**Date:** 2026-05-03  
**Status:** Design synthesis complete, ready for implementation

---

## What We Added to the Wiki

### New Research Document
**[[research/buck2-integration-patterns]]** - Comprehensive guide covering:
- Four-layer architecture (pure core + interface + 3 frontends + build bridge)
- Persistent Worker Protocol (10-100x faster local builds)
- LSP integration via BXL (Buck Extensibility Language)
- Reference implementations (Rust, Hack, Zig, Sorbet)
- Compiler requirements for Buck2 compatibility
- Anti-patterns to avoid (like `ccache`)

### Updated Documents
**[[decisions/ADR-006-multi-layer-build-configuration]]**:
- Added persistent worker support section
- Linked to new Buck2 integration research
- Explained how Buck2 integration complements standalone HWML builds

**[[wiki/index.md]]** and **[[wiki/log.md]]**:
- Added new research page to index
- Documented the integration in chronological log
- Updated progress metrics (26% complete)

---

## Key Concepts for HWML

### 1. The Four-Layer Architecture

**Layer 1: Pure Compiler Core (`hwml-core`, `hwml-elab`)**
- Built with Salsa query engine
- Pure functions: `parse(FileId) → AST`, `typecheck(AST) → TypedAST`
- No I/O, no side effects
- Mathematical determinism

**Layer 2: Interface Layer (`hwml-db`)**
- Virtual File System (VFS): Maps paths to contents
- Source Database: Tracks file changes, invalidates queries
- Bridge between pure compiler and real world

**Layer 3: Three Execution Frontends**
- **Cold-start CLI** (`hwml`): One-shot compilation, exit
- **Persistent worker** (`hwml --persistent_worker`): Long-running, keeps ASTs in memory
- **Language server** (`hwml-lsp`): Daemon for editors, uses unsaved buffers

**Layer 4: Build System Bridge**
- Starlark rules: `hwml_library`, `hwml_binary`, `hwml_toolchain`
- BXL script: `generate_project.bxl` → outputs `hwml-project.json`
- LSP reads JSON to understand workspace

### 2. Persistent Worker Protocol

**The Problem:**
- LSP/developers want warm daemon (2ms recompiles)
- Buck2 wants stateless CLI (mathematical purity)
- Conflict: Fresh boot per module is slow

**The Solution:**
```bash
# Buck2 starts compiler once
hwml --persistent_worker

# Compiler loops reading JSON requests from stdin
# Keeps ASTs in memory between requests
# Writes JSON responses to stdout
# Buck2 gets hermeticity, you get speed
```

**Used by:** Java, Scala, Rust in Buck2/Bazel environments

### 3. Compiler Requirements

Must support:
- `--emit-deps out.d` - Dependency file for Buck2's action graph
- `@args.txt` - Response files for long command lines
- `--message-format=json` - Parseable errors for parallel builds
- Zero implicit state - No hidden caches, no `~/.hwmlconfig`

### 4. LSP Integration (Path A: BXL)

**Flow:**
1. User opens VS Code → extension runs `buck2 bxl //tools:generate_project.bxl`
2. BXL script traverses Buck2 graph
3. Extracts: dependencies, compiler flags, library locations
4. Writes `hwml-project.json` to repo root
5. LSP watches this file, reads on startup
6. LSP knows entire workspace before user opens a file

**Similar to:** `compile_commands.json` (C++), `rust-project.json` (Rust)

---

## Integration with Existing Plans

### How Buck2 Complements ADR-006

**ADR-006 Three Layers:**
1. Library manifest (`hwml.toml`) - What this library is
2. Build config (`hwml-build.toml`) - How to build it
3. Lock file (`hwml.lock`) - Exact dependency versions

**Buck2 Integration:**
- Reads `hwml.toml` → generates `BUCK` files (`hwml generate buck`)
- Uses `hwml-build.toml` for features, optimization, platform properties
- Respects `hwml.lock` for reproducible dependency resolution
- Adds execution layer: persistent workers, remote execution, CAS

**Two Modes:**
- **Standalone HWML**: `hwml build` with three-tier CAS (local + user + remote)
- **Buck2-integrated**: Buck2 orchestrates, uses persistent workers, leverages Buck2's CAS
- **LSP**: Works in both modes (reads `hwml-project.json` or `hwml-workspace.toml`)

---

## Implementation Roadmap

### Phase 1: Core Compiler (Months 1-3)
- [ ] Salsa query engine integrated into `hwml-db`
- [ ] Cold-start CLI with required flags
- [ ] VFS and source database infrastructure

### Phase 2: Persistent Worker (Months 4-5)
- [ ] `--persistent_worker` mode
- [ ] stdin/stdout WorkRequest/WorkResponse protocol
- [ ] Keep VFS + Query Engine in memory

### Phase 3: LSP (Months 6-8)
- [ ] LSP server using same compiler core
- [ ] JSON-RPC protocol implementation
- [ ] Read `hwml-project.json` on startup

### Phase 4: Buck2 Rules (Months 9-10)
- [ ] Starlark rules: `hwml_toolchain`, `hwml_library`, `hwml_binary`
- [ ] Local Buck2 builds working
- [ ] Remote execution integration

### Phase 5: BXL Project Generator (Months 11-12)
- [ ] `generate_project.bxl` script
- [ ] Traverse Buck2 graph, extract dependency info
- [ ] Generate `hwml-project.json` for LSP

---

## Reference Implementations to Study

1. **Rust + rust-analyzer**: Salsa framework, Buck2 → `rust-project.json`
2. **Hack**: `hh_server` daemon, saved states from remote cache
3. **Zig**: Compiler as build system, built-in content-addressed caching
4. **Sorbet**: Bazel-first typechecker, strict hermeticity

---

## Next Actions

1. ✅ Wiki updated with Buck2 integration patterns
2. ✅ ADR-006 enhanced with persistent worker details
3. ⏭️ Prototype Salsa integration in `hwml-db`
4. ⏭️ Design persistent worker protocol
5. ⏭️ Draft initial Buck2 Starlark rules
6. ⏭️ Review four-layer architecture with team

---

**Full details:** See [[research/buck2-integration-patterns]] for complete analysis.
