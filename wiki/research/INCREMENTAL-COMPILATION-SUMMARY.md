# Incremental Compilation Research: Executive Summary

**Created:** 2026-05-03  
**Research Duration:** 2026-05-03 (comprehensive web and academic literature review)  
**Documents Created:** 5 comprehensive research pages  
**Status:** Ready for design decisions

---

## What Was Researched

Comprehensive survey of modern incremental compilation systems (2020-2026), covering:

1. **Academic Research:**
   - Adapton (PLDI 2014): Demand-driven incremental computation
   - PIE (IC 2019): Sound, optimal incremental builds with dynamic dependencies
   - Stateful compilers (CGO 2024): Fine-grained incremental builds
   - Incremental type-checkers (OOPSLA 2022): 147x speedups

2. **Production Systems:**
   - Rust (rustc + cargo): Query-based incremental compilation
   - GHC (Haskell): Interface files and recompilation avoidance
   - Scala Zinc: Name hashing for fine-grained invalidation
   - Salsa: Incremental computation framework (rust-analyzer)

3. **Build Systems:**
   - Bazel: Remote Execution API v2, content-addressable storage
   - Buck2 (Meta): Dynamic dependencies, hermetic builds, 2x faster than Buck1
   - Nix: Content-addressed derivations, reproducible builds
   - Shake: Monadic dependencies, early cut-off
   - PIE: Programmatic incremental builds

4. **LSP Integration:**
   - rust-analyzer: Local analysis with remote compilation
   - clangd: Remote index architecture
   - gopls: Daemon mode for shared state
   - Crystal LSP: Incremental-first design

5. **Remote Execution:**
   - Bazel Remote Execution API v2 (industry standard)
   - BuildBuddy, Buildbarn, NativeLink (server implementations)
   - Remote persistent workers, action deduplication
   - Platform properties, timeouts, streaming

6. **Artifact Caching:**
   - Content-addressable storage (CAS) fundamentals
   - Deduplication scopes (instance-wide, org-scoped, repo-scoped)
   - Garbage collection policies (LRU, TTL, S3-FIFO)
   - Cross-user cache sharing patterns

---

## Key Findings

### 1. Content Hashing is Essential

**Timestamps (mtime) are unreliable:**
- Network filesystems
- Git operations
- Docker layers
- Reproducible builds

**Modern systems use content hashing:**
- Rust cargo: Moving to BLAKE3 checksums
- Scala Zinc: Replaced timestamps with bytecode hashes
- All CAS systems: SHA-256 for artifacts

### 2. Fine-Grained Tracking Matters

**File-level dependencies are too coarse.**

**Modern systems track at definition/member level:**
- GHC: Tracks which definitions are imported
- Scala Zinc: Name hashing (class-member granularity)
- Result: 50-90% reduction in unnecessary rebuilds

### 3. Query-Based Computation Wins

**Rustc model (Salsa):**
- Every computation is a query
- Memoized results
- Incremental change propagation (red-green algorithm)
- Durability levels (skip validation of stable inputs)

**Benefits:**
- Correct invalidation (no false negatives)
- Minimal recomputation (no false positives)
- Easy to reason about (pure functions)

### 4. LSP Needs Local Analysis

**Remote compilation is too slow for IDE features.**

**Successful pattern:**
- Type checking local (Salsa-based, <100ms)
- Code generation remote (CIRCT, seconds/minutes)
- Metadata shared via CAS (.rmeta, .hi, .hwmli)

### 5. Hermetic Builds Enable Caching

**Reproducible builds = cacheable builds.**

**Requirements:**
- Explicit dependencies (all inputs declared)
- Isolated execution (sandbox from host)
- Deterministic outputs (no timestamps, random)
- Pinned toolchains (specific versions)

**Result:** Cache artifacts across users, machines, time

---

## Recommendations for HWML

### Immediate (Phase 1-2, ~6 weeks)

1. **Implement `.hwmli` metadata files:**
   - Binary format (bincode)
   - Content-addressed (BLAKE3 hash)
   - Store interface + dependencies

2. **Content-based change detection:**
   - Never use mtimes
   - Hash source files, dependencies, flags
   - Cache lookup by fingerprint

3. **Fine-grained dependency tracking:**
   - Track which definitions are used
   - Only invalidate on relevant changes

### Short-Term (Phase 3-4, ~8 weeks)

4. **Remote CAS for team sharing:**
   - S3 or BuildBuddy as backend
   - Local cache with LRU eviction
   - Workspace-scoped authentication

5. **LSP with cached metadata:**
   - Load `.hwmli` from local cache
   - Parallel cache priming on startup
   - File watcher for invalidation
   - Target: <100ms responses, <5s startup

### Medium-Term (Phase 5-6, ~8 weeks)

6. **Remote execution for Verilog generation:**
   - Integrate Bazel RE API v2
   - Hermetic CIRCT backend (Docker)
   - Action cache + CAS
   - Target: 5-10x speedup via parallelism

7. **Cross-clone deduplication:**
   - Shared local cache directory
   - Background garbage collection
   - Target: 3x reduction in disk usage

---

## Performance Targets

| Metric | Current | Target | Improvement |
|--------|---------|--------|-------------|
| Null build | 60s | 2s | 30x |
| Single-file change | 45s | 5s | 9x |
| LSP hover (cold) | 3s | 50ms | 60x |
| LSP hover (warm) | - | 10ms | - |
| Remote Verilog gen | - | 10s | 6x vs local |
| Remote cache hit | - | 0.5s | 120x vs rebuild |
| Full clean build | 15min | 2min | 7.5x |

---

## Research Documents

1. **[[research/incremental-compilation-synthesis]]** ← **START HERE**
   - Complete architecture, design decisions, implementation roadmap
   - Concrete recommendations for HWML

2. **[[research/modern-incremental-compilation]]**
   - Academic and industry systems analysis
   - Rust, GHC, Scala, Salsa, PIE, Shake

3. **[[research/modern-build-systems]]**
   - CAS, remote execution, hermetic builds
   - Bazel, Buck2, Nix, BuildBuddy

4. **[[research/lsp-and-remote-compilation]]**
   - LSP performance patterns
   - Local analysis, remote compilation, metadata sync

5. **[[research/artifact-deduplication]]**
   - Cross-user cache sharing
   - Deduplication scopes, GC policies, security

---

## Next Steps

1. **Review synthesis document** - [[research/incremental-compilation-synthesis]]
2. **Discuss with team** - Validate assumptions, priorities
3. **Create ADR** - Decide on `.hwmli` format, CAS backend, LSP architecture
4. **Start Phase 1** - Content-addressed artifacts (2-3 weeks)
5. **Iterate** - Measure, optimize, extend

---

**Questions? Start with the synthesis document:**  
[[research/incremental-compilation-synthesis]]
