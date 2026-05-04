# LSP Integration with Remote Compilation

**Created:** 2026-05-03  
**Type:** Research Synthesis  
**Status:** Analysis of LSP performance patterns  
**Confidence:** 0.90 (based on production LSP implementations)

---

## Summary

Language Server Protocol (LSP) servers must remain **responsive locally** even when compilation happens remotely. Modern LSP implementations achieve this through **aggressive caching**, **incremental computation**, **parallel analysis**, and **smart synchronization** with remote artifacts.

---

## The Challenge

**Conflicting Requirements:**
- LSP: Sub-100ms responses for goto-definition, hover, completions
- Remote builds: Network latency (10-100ms), compilation time (seconds to minutes)
- Monorepos: Millions of lines of code, thousands of dependencies

**If LSP waits for remote compilation, it's unusable.**

---

## Solution Patterns

### 1. Local Analysis with Remote Compilation

**rust-analyzer model:**
- LSP server runs **locally** with full source code
- Analyzes code incrementally using Salsa query system
- Uses **local cache** for metadata (`.rmeta` files from cargo check)
- Remote execution used only for actual compilation (cargo build)

**Workflow:**
1. Developer types code
2. LSP analyzes on file save (or on-type)
3. Queries incremental database (Salsa) for types, definitions
4. Returns results in <100ms from cache
5. Separately, CI/remote builds run full compilation

**Key Insight:** Analysis for IDE features doesn't require full compilation, just type checking.

**References:**
- [rust-analyzer architecture](https://rust-analyzer.github.io/book/contributing/architecture.html)
- [LSP doesn't assume unified filesystem](https://github.com/rust-lang/rust-analyzer)

---

### 2. Compilation Database + Remote Artifacts

**clangd remote index:**
- Batch process on powerful server: Parse entire codebase → produce index file
- Index server loads file into memory, exposes gRPC query API
- clangd client (local) requests symbol info over network in real-time
- Local clangd also has fallback: Parse files locally if network slow

**Tradeoffs:**
- Fast symbol search (server has full index)
- Network dependency (must handle offline gracefully)
- Staleness (index lags behind changes until rebuilt)

**References:**
- [clangd remote index](https://clangd.llvm.org/design/remote-index.html)

---

### 3. LSP-Specific Caching Layers

**Deno Language Server:**
- **Cache between Rust and TypeScript compiler**
- Track file changes, evict only affected entries
- Notify JS layer of changes, let it invalidate selectively
- Distinguish: Local files (change often) vs remote imports (npm, jsr - cached permanently)

**Result:** 10x speedup by avoiding redundant type checking.

**References:**
- [How We Made the Deno Language Server Ten Times Faster](https://denoland.medium.com/how-we-made-the-deno-language-server-ten-times-faster-62358af87d11)

---

### 4. Daemon Mode for Shared LSP

**gopls daemon:**
- Single persistent gopls process shared across editor instances
- Editor starts thin "forwarder" process that connects to daemon
- Daemon maintains warm state (parsed packages, type info)
- Multiple editor windows share one daemon → less memory, warm cache

**Benefits:**
- Faster startup (daemon already running)
- Shared cache across projects
- Consistent view of workspace

**Tradeoffs:**
- Daemon management complexity
- Must handle daemon crashes gracefully

**References:**
- [Gopls: Running as a daemon](https://go.dev/gopls/daemon)

---

### 5. Parallel Priming and Lazy Loading

**rust-analyzer cache priming:**
- **Parallel analysis** on startup: Process all crates concurrently
- **Lazy project loading**: Only analyze opened projects in monorepo
- **Delay priming** until proc macros loaded (avoid stale IDs)
- **Symbol indexing** pre-computed so first symbol search is fast

**Optimizations (2024-2025):**
- Offload expensive drops (Rowan nodes, span maps) to separate thread
- Prime crate lang item queries upfront (avoid sequential walk later)
- LRU eviction of unused query results

**References:**
- [rust-analyzer perf: Improve start up time #21046](https://github.com/rust-lang/rust-analyzer/pull/21046)
- [Lazy Workspace/Project Discovery #17537](https://github.com/rust-lang/rust-analyzer/issues/17537)

---

## Synchronization Strategies

### File Watching

**Problem:** LSP must know when files change (local edits, git pull, build outputs).

**Options:**
1. **Client-side watching** (VS Code default):
   - Editor watches filesystem, notifies LSP
   - Unreliable on some platforms (macOS fsevents lag, network FS)
   
2. **Server-side watching** (rust-analyzer can use):
   - LSP watches files itself
   - More reliable but higher resource usage
   - Can get stuck on huge monorepos

**Recommendation:** Server-side for correctness, client-side for lower overhead.

---

### Metadata Sync from Remote Builds

**Problem:** Remote build produces `.rmeta`, `.hi`, `.class` metadata files. How does local LSP get them?

**Solutions:**

1. **Download on-demand:**
   - LSP requests artifact by hash from remote cache
   - Only download metadata, not full binaries
   - Example: Rust `.rmeta` files are small, fast to fetch

2. **Prefetch after build:**
   - CI build completes → trigger download of metadata for this commit
   - Developer switches to that commit → metadata already local
   - Example: Bazel's `build-event-stream` can trigger artifact sync

3. **Hybrid compilation:**
   - LSP runs `cargo check` locally (fast, produces `.rmeta`)
   - CI runs `cargo build` remotely (slow, produces binaries)
   - LSP uses local `.rmeta`, never needs remote artifacts

**References:**
- [Rust `.rmeta` files](https://rustc-dev-guide.rust-lang.org/backend/libs-and-metadata.html)

---

## Case Study: CLion Remote Development

**Architecture:**
- IDE frontend: Local (macOS/Windows/Linux)
- IDE backend: Remote (Linux server or container)
- Source code: Can be local (synced) or remote

**Modes:**

1. **Remote with local sources:**
   - Code on local machine
   - Automatic rsync to remote on file save
   - Remote: Compilation, build, debug
   - Local: Parsing for code completion (with synced headers)
   - Uses `pigz` (parallel gzip) for fast header sync

2. **Thin client mode:**
   - All code remote
   - IDE backend runs on server (JetBrains Gateway)
   - Local machine just renders UI
   - Compilation and analysis both remote, cached in backend

**Performance:**
- Fast turnaround for most edits (header sync is incremental)
- Remote compilation on powerful servers
- Local analysis for instant feedback

**References:**
- [CLion Remote Development](https://jetbrains.com/help/clion/remote-projects-support.html)

---

## Best Practices for HWML

Given HWML's requirements (fast LSP, remote compilation, hermetic builds):

1. **Separate analysis from compilation:**
   - LSP runs type checking locally (fast, produces `.hwmli` metadata)
   - Remote execution for Verilog generation (slow, uses CIRCT)

2. **Content-addressed metadata:**
   - Store `.hwmli` files in CAS by source file hash
   - LSP fetches dependencies from CAS on-demand
   - Local disk cache with LRU eviction

3. **Incremental LSP database:**
   - Use Salsa (already familiar) for LSP queries
   - Track file changes, invalidate affected queries
   - Cache parse trees, type info, elaboration results

4. **Prefetch on git operations:**
   - `git checkout` → fetch `.hwmli` for new HEAD from remote cache
   - Background task, doesn't block editor

5. **Hybrid mode:**
   - Developer runs `hwml check` locally (fast feedback)
   - CI runs `hwml build` remotely (full Verilog + synthesis)
   - Both share CAS for intermediate artifacts

**References:**
- See [[research/modern-incremental-compilation]] for Salsa details
- See [[research/modern-build-systems]] for CAS implementation patterns

---

**Related:**
- [[research/modern-incremental-compilation]]
- [[research/modern-build-systems]]
- [[research/artifact-deduplication]]
