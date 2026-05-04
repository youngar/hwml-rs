# Modern Incremental Compilation Systems

**Created:** 2026-05-03  
**Type:** Research Synthesis  
**Status:** Comprehensive survey (2020-2026)  
**Confidence:** 0.95 (based on extensive academic and industry sources)

---

## Summary

Modern incremental compilation systems use sophisticated **dependency tracking**, **content-addressable storage**, **query-based computation models**, and **memoization** to achieve dramatic speedups in subsequent builds. The field has converged on several key design patterns that enable both correctness and performance.

---

## Core Concepts

### 1. Content-Based Change Detection

**Problem:** Timestamp-based (mtime) change detection is unreliable:
- Network filesystems
- Git operations that restore old timestamps
- Build tools that touch files without changing content
- Docker layers and reproducible builds

**Solution:** Content hashing (MD5, SHA-256, BLAKE3)
- Rust cargo: Moving to BLAKE3 checksums ([#14137](https://github.com/rust-lang/cargo/pull/14137))
- Zinc (Scala): Replaced timestamps with bytecode hashes ([#1430](https://github.com/sbt/zinc/pull/1430))
- Shake: Early cut-off - files that rebuild but don't change don't invalidate dependents

**Key Insight:** Hash comparison eliminates false positives from timestamp changes.

---

### 2. Query-Based Incremental Computation

**Rust's Query System** (rustc):
- Every compilation artifact is a **query** with inputs and outputs
- Queries are **memoized** - cached results reused when inputs unchanged
- **Incremental algorithm**: Try-mark-green propagation
  - If all inputs are green (unchanged), output is green without recomputation
  - If inputs changed, compare output hash - if same, dependent queries stay green
- **Durability levels**: Low (source files) vs High (stdlib) - skip validation of high-durability queries when only low-durability changes

**References:**
- [Incremental compilation in detail](https://rustc-dev-guide.rust-lang.org/queries/incremental-compilation-in-detail.html)
- Rust Project Goal: [Incremental Systems Rethought (2026)](https://rust-lang.github.io/rust-project-goals/2026/incremental-system-rethought.html)

---

### 3. Fine-Grained Dependency Tracking

**GHC (Haskell):** Interface files (`.hi`)
- Track not just file dependencies, but **which definitions** are used
- Recompilation checker compares fingerprints of:
  - Source hash
  - Flag hash (compilation flags)
  - Usage fingerprints (what was imported from each module)
- Only recompile if relevant parts of dependencies changed

**Scala Zinc:** Name hashing
- Tracks dependencies at **class-member level**, not just file level
- Collects "used names" during compilation
- On recompilation, only invalidate if the changed API members are in the used-names set
- Handles As Seen From (type member resolution through inheritance)

**References:**
- [GHC Recompilation Avoidance](https://gitlab.haskell.org/ghc/ghc/wikis/commentary/compiler/recompilation-avoidance)
- [Zinc Name Hashing](https://scala-sbt.org/1.x/docs/Understanding-Recompilation.html)

---

### 4. Dynamic Dependencies

**Problem:** Static dependency graphs cannot express:
- Generated code that determines its own dependencies
- Conditional compilation
- Header files discovered by preprocessor

**Shake Build System:**
- **Monadic dependencies**: Discover dependencies during execution
- Build rules can examine files, then declare additional dependencies
- Uses demand-driven evaluation (like lazy computation)
- Example: Run C preprocessor, extract `#include` directives, add as dependencies

**PIE (Programmatic Incremental Build System):**
- Sound and optimal incremental builds with dynamic dependencies
- Interleaves dependency analysis and execution
- Maintains invariants on dependency graph (no cycles, correct ordering)

**References:**
- [Shake: Why choose Shake?](https://shakebuild.com/why)
- [PIE: Precise, Efficient, and Expressive Incremental Build Scripts (IC 2019)](https://researchr.org/publication/KonatSEV19)

---

### 5. Salsa: Incremental Computation Framework

Used by **rust-analyzer** for LSP support.

**Key Features:**
- Queries are pure functions: same inputs → same outputs
- **Red-green algorithm**: Revision-based change propagation
- **Durability**: Group inputs by change frequency, skip validation of stable inputs
- **LRU eviction**: Limit memory usage
- Supports **cycles** (with cycle recovery removed in recent versions)

**Memory Optimizations (2024-2025):**
- Reduced rust-analyzer memory from 8GB → 4GB on analysis-stats
- Lazy loading of dependency information
- Garbage collection of unused intermediate results

**References:**
- [Salsa Book: Algorithm](https://salsa-rs.github.io/salsa/reference/algorithm.html)
- [Durable Incrementality (rust-analyzer blog)](https://rust-analyzer.github.io/blog/2023/07/24/durable-incrementality.html)

---

## Continued in Part 2...

**See:** [[research/modern-build-systems]] for CAS, remote execution, and hermetic builds.
