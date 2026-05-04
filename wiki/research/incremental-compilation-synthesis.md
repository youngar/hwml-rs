# Incremental Compilation Synthesis: Recommendations for HWML

**Created:** 2026-05-03  
**Type:** Synthesis & Recommendations  
**Status:** Research-backed design guidance  
**Confidence:** 0.93 (based on proven production patterns)

---

## Executive Summary

Modern incremental compilation systems achieve **10-100x speedups** on subsequent builds through:
1. **Content-based change detection** (not timestamps)
2. **Fine-grained dependency tracking** (member-level, not file-level)
3. **Query-based incremental computation** (Salsa, rustc model)
4. **Content-addressable storage** (deduplicate across users/machines)
5. **Remote execution** (scale beyond local resources)
6. **Hermetic builds** (reproducible, cacheable results)

HWML should adopt these patterns to enable:
- **Fast local LSP** (sub-100ms responses)
- **Fast subsequent builds** (seconds, not minutes)
- **Remote compilation** (powerful servers, not laptops)
- **Cross-user cache sharing** (team benefits from each other's builds)
- **Hermetic Verilog generation** (reproducible hardware synthesis)

---

## Architecture Overview

```
┌─────────────────────────────────────────────────────────────┐
│  Developer Machine (Local)                                   │
│                                                              │
│  ┌──────────────┐         ┌──────────────┐                  │
│  │   Editor     │────────▶│  hwml-lsp    │                  │
│  │  (VS Code)   │  LSP    │  (Salsa DB)  │                  │
│  └──────────────┘         └──────────────┘                  │
│                                 │                            │
│                                 ▼                            │
│                           ┌──────────────┐                   │
│                           │ Local Cache  │                   │
│                           │  .hwmli CAS  │                   │
│                           └──────────────┘                   │
│                                 │                            │
└─────────────────────────────────┼────────────────────────────┘
                                  │
                      ┌───────────┴───────────┐
                      ▼                       ▼
           ┌─────────────────────┐  ┌──────────────────┐
           │  Remote Cache (CAS) │  │  Remote Executor │
           │  S3 / BuildBuddy    │  │  (RE API v2)     │
           └─────────────────────┘  └──────────────────┘
                      │                       │
                      └───────────┬───────────┘
                                  ▼
                        ┌──────────────────┐
                        │  Verilog Output  │
                        │  (CIRCT backend) │
                        └──────────────────┘
```

---

## Key Design Decisions

### 1. Compiler Artifact Format: `.hwmli` Files

**Inspiration:** Rust `.rmeta`, GHC `.hi`, Scala `.class` + Analysis

**Content:**
- **Interface:** Exported types, functions, modules (for dependents)
- **Metadata:** Source hash, compiler version, flags hash
- **Dependencies:** List of imported `.hwmli` files with their hashes
- **Optional:** Simplified core terms for fast re-elaboration

**Format:**
- Binary (fast to parse)
- Versioned (compiler can detect incompatible files)
- Content-addressed (filename = hash of inputs)

**Storage:**
- Local: `~/.cache/hwml/cas/{sha256_prefix}/{sha256_full}.hwmli`
- Remote: S3/CAS at `cas/{sha256}/hwmli`

**Example:**
```
Source: lib/uart.hwml (hash: abc123...)
Compiler: hwml 0.2.0
Flags: --target fpga
Output: abc123def456.hwmli
```

---

### 2. Incremental Computation: Salsa

HWML already uses Salsa. Extend it for compilation:

**Queries:**
- `parse_file(path) -> AST`
- `elaborate_file(path) -> CoreModule`
- `type_check_module(module_id) -> TypedModule`
- `dependencies_of(module_id) -> Vec<ModuleId>`
- `hwmli_file_for(module_id) -> HwmliMetadata`

**Durability:**
- **High:** Stdlib modules (change rarely)
- **Low:** User source files (change frequently)

**Workflow:**
1. User edits `uart.hwml`
2. Salsa detects change (file watcher or explicit `invalidate`)
3. Queries dependent on `uart.hwml` are red
4. LSP requests type of symbol → triggers incremental re-elaboration
5. Only `uart.hwml` and its direct dependents are reprocessed
6. Results cached in Salsa DB (in-memory + optional disk persistence)

**References:**
- [[entities/nbe]] (current usage in HWML)
- [[research/modern-incremental-compilation]] (Salsa details)

---

### 3. Change Detection: Content Hashing

**Never use mtimes.** Always use content hashes.

**Hash Function:** BLAKE3
- Faster than SHA-256
- Cryptographically secure (unlike MD5)
- Used by Cargo, Nix, Rust ecosystem

**What to Hash:**
- Source file content
- Compiler version + flags (affects semantics)
- Dependency `.hwmli` hashes (transitive)

**Fingerprint:**
```rust
struct Fingerprint {
    source_hash: Blake3Hash,      // Hash of source file
    compiler_version: Version,     // e.g., "0.2.0"
    flags_hash: Blake3Hash,        // Hash of compilation flags
    deps: Vec<(ModuleName, Blake3Hash)>, // Dependencies
}
```

**Cache Lookup:**
1. Compute fingerprint for `uart.hwml`
2. Query CAS: `cas/{fingerprint_hash}/hwmli`
3. Hit? Deserialize `.hwmli`, use cached elaboration
4. Miss? Elaborate, serialize to `.hwmli`, store in CAS

**References:**
- [[research/modern-incremental-compilation]] (content-based change detection)
- Cargo tracking issue: [#14136](https://github.com/rust-lang/cargo/issues/14136)

---

### 4. Dependency Tracking: Fine-Grained

**Level of Tracking:**
- **File-level:** `uart.hwml` depends on `std.hwml`
- **Definition-level:** `uart.hwml` uses `std::Option`, `std::Result` (not `std::Vec`)

**Why Definition-Level?**
- Changing `std::Vec` doesn't invalidate `uart.hwml` if it doesn't use `Vec`
- Massive reduction in invalidations in large codebases

**Implementation:**
- During elaboration, track which definitions are referenced
- Store in `.hwmli`:
```rust
struct HwmliMetadata {
    // ...
    used_definitions: HashMap<ModuleName, HashSet<DefinitionId>>,
}
```
- On recompilation of `std.hwml`:
  - Compute which definitions changed
  - Only invalidate dependents that use those definitions

**References:**
- GHC usage tracking
- Scala Zinc name hashing
- [[research/modern-incremental-compilation]] (fine-grained tracking)

---

### 5. Local LSP Architecture

**Goal:** <100ms responses, even for monorepo

**Strategy: Separate Concerns**
- **LSP (local):** Type checking, elaboration, IDE features
- **Compilation (remote):** Verilog generation via CIRCT

**LSP Workflow:**
1. User opens `uart.hwml`
2. LSP parses, elaborates, type-checks (Salsa queries)
3. Produces `.hwmli` metadata (cached locally)
4. Returns hover/goto-def/completion results (<100ms)

**Compilation Workflow (async, doesn't block LSP):**
1. User runs `hwml build uart.hwml`
2. CLI checks local CAS: `.hwmli` up-to-date? Verilog cached?
3. Cache miss → send to remote executor
4. Remote executor: Fetch `.hwmli` from CAS, run CIRCT backend
5. Upload Verilog to CAS
6. Stream results back to developer

**Key Insight:** LSP never waits for CIRCT (slow). Verilog generation is separate pipeline.

**References:**
- [[research/lsp-and-remote-compilation]] (rust-analyzer model)

---

### 6. Remote Execution Integration

**Protocol:** Bazel Remote Execution API v2
- Industry standard (Bazel, Buck2, Pants compatible)
- gRPC-based, high performance
- Supports ActionCache + CAS

**Server Options:**
- **BuildBuddy** (commercial, easy setup, good UI)
- **NativeLink** (OSS, Nix-powered, high performance)
- **Buildbarn** (OSS, proven at scale)
- **Self-hosted:** bazel-remote (Go, simple HTTP+gRPC server)

**What to Execute Remotely:**
- **Verilog generation** (CIRCT backend - heavy, CPU-bound)
- **Full workspace builds** (many modules)
- **Simulation** (if deterministic)

**What to Keep Local:**
- **Type checking** (fast, needs low latency for LSP)
- **Parsing** (fast, Salsa-cached)
- **Single-file checks** (cargo check equivalent)

**References:**
- [[research/modern-build-systems]] (RE API, BuildBuddy, NativeLink)

---

### 7. Hermetic Builds

**Requirements for Hermeticity:**
1. **Explicit dependencies:** All `.hwmli` files declared in manifest
2. **Pinned toolchain:** Specific CIRCT version, not "whatever is installed"
3. **No network access** during compilation (fetch deps beforehand)
4. **Deterministic output:** No timestamps, no random UUIDs in Verilog comments

**Determinism Checklist:**
- Use fixed `SOURCE_DATE_EPOCH` for any timestamps (e.g., last Git commit)
- Sort module/definition output by name (not HashMap iteration order)
- Don't embed absolute paths (use relative to workspace root)
- Disable non-deterministic optimizations in CIRCT (if any)

**Verification:**
- Run build twice → compare output hashes → must be identical
- CI job: Build same commit on two different machines → compare

**References:**
- [[research/modern-build-systems]] (hermeticity, Bazel, Nix)

---

---

## Implementation Roadmap

### Phase 1: Content-Addressed Artifacts (2-3 weeks)

**Goal:** `.hwmli` files with content-based caching

**Tasks:**
1. Define `.hwmli` binary format (bincode serialization)
   - Interface: Exported types/functions
   - Dependencies: List of imported modules + hashes
   - Metadata: Source hash, compiler version, flags
2. Implement local CAS:
   - `~/.cache/hwml/cas/{sha256}/hwmli`
   - Store + retrieve by hash
3. Integrate with Salsa:
   - Query: `hwmli_metadata(module_id) -> Option<HwmliMetadata>`
   - Load from CAS if hash matches, else recompile
4. Testing:
   - Build project twice → second build instant (cache hit)
   - Change one file → only it and dependents rebuild

**Success Criteria:**
- 10x speedup on null builds (no changes)
- Correct invalidation (change propagation)

---

### Phase 2: Fine-Grained Dependencies (3-4 weeks)

**Goal:** Only recompile when used definitions change

**Tasks:**
1. Track used definitions during elaboration:
   - Instrument NbE to record which names are referenced
   - Store in `.hwmli`: `used_defs: HashMap<ModuleName, HashSet<DefId>>`
2. Compute API diff on recompilation:
   - Hash each definition's type signature
   - Detect which definitions changed
3. Smart invalidation:
   - Only invalidate dependents that use changed definitions
4. Testing:
   - Add unused function to stdlib → no user code rebuilds
   - Change used function → only real dependents rebuild

**Success Criteria:**
- 50%+ reduction in invalidations for typical stdlib changes
- Zero false negatives (all necessary rebuilds happen)

---

### Phase 3: Remote CAS (2-3 weeks)

**Goal:** Share artifacts across developers and CI

**Tasks:**
1. Choose backend:
   - Option A: S3 bucket (simple, no server)
   - Option B: bazel-remote (Docker, easy local setup)
   - Option C: BuildBuddy/NativeLink (full RBE support)
2. Implement cache client:
   - On cache miss: Check remote before local compilation
   - On cache hit: Download `.hwmli` to local cache
   - On local build: Upload `.hwmli` to remote cache
3. Authentication:
   - Workspace API tokens (per-project)
   - Read-all, write-restricted for production
4. Testing:
   - Developer A builds → uploads to cache
   - Developer B builds → downloads from cache (instant)
   - CI builds → cache shared with all developers

**Success Criteria:**
- Cache hit rate >80% in team environment
- <100ms latency for cache queries (local network / CDN)

---

### Phase 4: LSP Integration (4-5 weeks)

**Goal:** Fast LSP using cached metadata

**Tasks:**
1. LSP uses Salsa for incremental queries:
   - `hover(position) -> HoverText`
   - `goto_def(position) -> Location`
   - `completions(position) -> Vec<CompletionItem>`
2. LSP loads `.hwmli` from local cache:
   - Never recompiles unless file changed
   - Fetches dependencies on-demand
3. Parallel cache priming:
   - On project open: Load all `.hwmli` in background
   - Rayon-based parallelism
4. File watching:
   - Server-side file watcher (notify crate)
   - Invalidate Salsa queries on file change
5. Testing:
   - Open large project → LSP responsive within 5 seconds
   - Hover on symbol → <50ms response (from cache)
   - Edit file → re-analysis completes within 100ms

**Success Criteria:**
- LSP startup: <5s for 100-module project
- Query latency: <100ms (95th percentile)
- Memory usage: <2GB for large projects

---

### Phase 5: Remote Execution (5-6 weeks)

**Goal:** Offload Verilog generation to remote servers

**Tasks:**
1. Integrate RE API v2 client:
   - Use `bazel-remote-execution` Rust crate or similar
   - Implement Action, Command, Execution protocol
2. Define execution actions:
   - Input: `.hwmli` + CIRCT version
   - Command: `hwml-circt-backend --input uart.hwmli --output uart.v`
   - Output: Verilog file
3. Hermeticity:
   - Package CIRCT in container (Docker image)
   - No network access during execution
   - Reproducible output (deterministic paths, timestamps)
4. Deploy executor cluster:
   - Local: Docker Compose with bb-worker/bb-runner
   - Production: Kubernetes with BuildBuddy
5. Testing:
   - Local build vs remote build → identical output (hash match)
   - Remote build cached → reused by other developers
   - Execution time: <10s for typical module on remote (vs 60s local)

**Success Criteria:**
- 5-10x speedup for Verilog generation (remote parallelism)
- 100% reproducibility (hash match)
- Cache hit rate >90% (team shares results)

---

### Phase 6: Cross-Clone Deduplication (1-2 weeks)

**Goal:** Share cache across multiple local checkouts

**Tasks:**
1. Centralized local cache:
   - All projects point to `~/.cache/hwml/` (env var override)
   - Content-addressed, automatic dedup
2. Garbage collection:
   - LRU eviction: Keep 50GB, delete oldest
   - Background GC task (runs weekly)
3. Testing:
   - Clone repo 3 times → build in each → storage = 1x (not 3x)
   - Switch branches → cache reused if source unchanged

**Success Criteria:**
- 3x reduction in local disk usage
- No cache corruption (concurrent access safe)

---

## Performance Targets

| Scenario | Current | Target | Improvement |
|----------|---------|--------|-------------|
| Null build (no changes) | 60s | 2s | 30x |
| Single file change | 45s | 5s | 9x |
| LSP hover (cold) | 3s | 50ms | 60x |
| LSP hover (warm) | - | 10ms | - |
| Verilog generation (local) | 60s | 60s | 1x (baseline) |
| Verilog generation (remote) | - | 10s | 6x |
| Cache hit (remote) | - | 0.5s | 120x |
| Full project build (clean) | 15min | 2min | 7.5x |

---

## Open Questions

1. **`.hwmli` format:** Binary (bincode/rkyv) or text (JSON/TOML)?
   - Binary: Faster parse, smaller size
   - Text: Human-readable, easier debugging
   - **Recommendation:** Binary with `--dump-hwmli-text` debug flag

2. **Salsa persistence:** Disk-backed DB or in-memory only?
   - Disk: Survive restarts, slower startup
   - Memory: Fast, but re-analyze on LSP restart
   - **Recommendation:** Memory for LSP, disk for CLI builds

3. **Remote executor platform:** Docker or Firecracker?
   - Docker: Easy setup, good ecosystem
   - Firecracker: Faster startup, better isolation
   - **Recommendation:** Start with Docker, migrate to Firecracker if needed

4. **Cache backend:** S3, GCS, or BuildBuddy?
   - S3/GCS: Cheap storage, no server maintenance
   - BuildBuddy: UI, monitoring, easier debugging
   - **Recommendation:** BuildBuddy for now (easier), S3 fallback for cost

---

## Academic References

1. **Adapton**: Composable, Demand-Driven Incremental Computation (PLDI 2014)
   - Memoization, change propagation, nominal dependencies

2. **PIE**: Precise, Efficient, and Expressive Incremental Build Scripts (IC 2019)
   - Sound + optimal incremental builds with dynamic dependencies

3. **Salsa**: Incremental computation framework (used by rust-analyzer)
   - Red-green algorithm, durability, query-based computation

4. **Shake**: Build system with monadic dependencies
   - Dynamic dependencies, early cut-off

5. **Zinc**: Scala incremental compiler
   - Name hashing, API change detection, transitive invalidation

6. **Rustc**: Query-based compiler
   - Incremental compilation in detail, on-disk cache

---

**See also:**
- [[research/modern-incremental-compilation]]
- [[research/modern-build-systems]]
- [[research/lsp-and-remote-compilation]]
- [[research/artifact-deduplication]]
- [[decisions/ADR-004-mvs-package-manager]]
- [[entities/nbe]]
