# HWML Design Wiki Index

**Last Updated:** 2026-05-03
**Total Pages:** 13 (in progress)
**Status:** Bootstrap phase - ingesting key documents

---

## Overview

- [[overview]] - High-level introduction to HWML for new contributors

---

## Decisions (ADRs)

### Implemented
- [[decisions/ADR-001-lcf-kernel]] - LCF-style trusted kernel for type safety
- [[decisions/ADR-002-bidirectional-typing]] - Bidirectional type checking (TO CREATE)

### Approved (Planned)
- [[decisions/ADR-003-universe-polymorphism]] - Phased approach to universe stratification
- [[decisions/ADR-004-mvs-package-manager]] - Minimum Version Selection for dependencies
- [[decisions/ADR-005-debug-information]] - Dual debug strategy (meta-level + object-level)
- [[decisions/ADR-006-multi-layer-build-configuration]] - Multi-layer build configuration (manifest + build + lock)

### Approved (Frontend Architecture - 2026-05-03) ⭐ **NEW**
- [[decisions/ADR-007-salsa-driven-compilation]] - **Demand-driven compilation via Salsa (no manual topo-sort)**
- [[decisions/ADR-008-vfs-abstraction]] - **Virtual File System for unified CLI/LSP file access** (CRITICAL FIX: VFS feeds Salsa)
- [[decisions/ADR-009-rkyv-zero-copy-serialization]] - **Zero-copy `.hwmli` loading with rkyv**
- [[decisions/ADR-010-metavariable-scoping-constraint-solver]] - **Metavariables local to Salsa queries, worklist constraint solver**
- [[decisions/ADR-011-module-resolution-file-discovery]] - **FileSet input for pure module resolution** (DRAFT)

### To Create
- ADR-012: Content-addressed artifacts - Hash-based package storage
- ADR-013: Persistent Worker Protocol - Long-lived compiler processes for Buck2

### To Extract
- Staged computation / two-level type theory
- Pattern matching compilation
- Universe hierarchy design
- Location information architecture
- LSP server design
- CIRCT backend architecture

---

## Components

### Core System
- [[components/kernel]] - Trusted kernel (hwml-core) (TO CREATE)
- [[components/elaborator]] - Surface to core elaboration (hwml-elab) (TO CREATE)
- [[components/package-manager]] - Multi-library compilation (hwml-workspace) (TO CREATE)

### Tooling
- [[components/lsp-server]] - Language Server Protocol implementation (TO CREATE)
- [[components/circt-backend]] - Verilog generation via CIRCT (TO CREATE)
- [[components/surface-parser]] - LALRPOP-based parser (TO CREATE)

---

## Entities

### Concepts
- [[entities/nbe]] - Normalization by Evaluation
- [[entities/bidirectional-typing]] - Bidirectional typing discipline (TO CREATE)
- [[entities/lcf-pattern]] - LCF-style trusted computing base (TO CREATE)
- [[entities/mvs]] - Minimum Version Selection algorithm (TO CREATE)
- [[entities/pattern-unification]] - Metavariable solving (TO CREATE)
- [[entities/dependent-types]] - Dependent type theory basics (TO CREATE)
- [[entities/universes]] - Universe hierarchy and levels (TO CREATE)
- [[entities/de-bruijn]] - De Bruijn indices and levels (TO CREATE)

### Libraries & Tools
- [[entities/salsa]] - Incremental computation framework (TO CREATE)
- [[entities/circt]] - Circuit IR Compilers and Tools (TO CREATE)
- [[entities/lalrpop]] - Parser generator (TO CREATE)
- [[entities/content-addressed-storage]] - Hash-based storage model (TO CREATE)

### Phases
- [[entities/phase-1]] - Core kernel and NbE (Complete) (TO CREATE)
- [[entities/phase-1-5]] - LET expressions and improvements (In Progress) (TO CREATE)
- [[entities/phase-2]] - Multi-file and package manager (Planned) (TO CREATE)

---

## Research

### Type Theory
- [[research/type-theory-foundations]] - Dependent types, NbE, bidirectional typing (TO CREATE)
- [[research/two-level-type-theory]] - Staged computation for hardware (TO CREATE)

### Elaboration & Error Messages
- [[research/elaboration-error-messages]] - Constraint origins, global diagnosis, metavar provenance

### Incremental Compilation & Build Systems (2026-05-03)
- [[research/incremental-compilation-synthesis]] - **Comprehensive synthesis and recommendations for HWML**
- [[research/build-system-caching-synthesis]] - **Caching, databases, and persistent stores synthesis**
- [[research/buck2-integration-patterns]] - **Buck2 integration patterns: persistent workers, LSP, four-layer architecture** (NEW)
- [[research/content-addressable-storage-systems]] - CAS in Git, Nix, IPFS, Buck2, Bazel, BLAKE3 hashing
- [[research/dependent-types-object-file-formats]] - Object file formats for dependent types: interning, serialization
- [[research/hardware-compiler-artifact-taxonomy]] - **Hardware artifact types, build system integration**
- [[research/modern-incremental-compilation]] - Modern systems: Rust, GHC, Scala Zinc, Salsa, PIE, Shake
- [[research/modern-build-systems]] - CAS, Remote Execution API, Hermetic builds (Bazel, Buck2, Nix)
- [[research/lsp-and-remote-compilation]] - LSP performance with remote builds
- [[research/artifact-deduplication]] - Cross-user cache sharing and deduplication strategies

### Debug Information
- [[research/debug-info-systems]] - Software debug info (DWARF, LLVM, Rust, GHC)
- [[research/hardware-debug-info]] - Hardware debug info (VCS, Verdi, waveforms, Chisel)
- [[research/llvm-debug-info-internals]] - LLVM debug info internals (preservation, optimization, consumption)
- [[research/debug-info-research-modern]] - Modern academic research (2020-2024, PLDI, ASPLOS, Onward!)

### External Systems
- [[research/go-mvs]] - Go's Minimum Version Selection (referenced)
- [[research/ghc-compilation]] - GHC's recompilation avoidance (TO CREATE)
- [[research/lean-elaboration]] - Lean 4's elaborator design (TO CREATE)
- [[research/agda-modules]] - Agda's module system (TO CREATE)

### Papers & Research
- [[research/extensible-elaborator]] - ExEl: Extensible constraint-based elaborators
- [[research/togt-heterogeneous-unification]] - Tog⁺: Heterogeneous unification with twin types
- [[research/disentangling-unification-coercion]] - Jon Sterling: Explicit casts for unification/coercion
- [[research/crude-but-effective-stratification]] - McBride: Lightweight universe polymorphism
- [[research/papers]] - Collected paper references (TO CREATE)

---

## Onboarding

- [[onboarding/new-contributor-guide]] - Start here for new contributors (TO CREATE)
- [[onboarding/type-system-primer]] - Understanding HWML's type system (TO CREATE)
- [[onboarding/codebase-map]] - Guide to the crates and modules (TO CREATE)
- [[onboarding/contributing-to-elaborator]] - How to work on elaboration (TO CREATE)
- [[onboarding/contributing-to-kernel]] - How to work on the kernel (TO CREATE)

---

## Analysis

- [[analysis/ADR-006-vs-package-manager-design-reconciliation]] - Reconciliation between ADR-006 and design/package-manager.md

---

## Synthesis

- [[synthesis/design-evolution]] - How HWML's design has evolved (TO CREATE)
- [[synthesis/trade-offs]] - Key trade-off decisions (TO CREATE)
- [[synthesis/open-questions]] - Current open design questions (TO CREATE)

---

## Source Documents (design/ directory)

### Fully Ingested
- `ARCHITECTURE.md` → ADR-001, ADR-002, ADR-003, kernel, elaborator entities
- `package-manager.md` → ADR-004, ADR-005, ADR-006, package manager component
- `hwml.md` → (Partial) Overview, dependent types concept
- `README.md` (root) → Overview

### Pending Ingestion (Priority Order)

**High Priority (Core Understanding):**
- [ ] `2ltt-nbe.md` - Two-level type theory with NbE
- [ ] `elaboration.md` - Elaboration algorithm
- [ ] `unification.md` - Unification and metavariable solving
- [ ] `pattern-matching.md` - Pattern compilation
- [ ] `universes.md` - Universe hierarchy
- [ ] `kernel-judgements.md` - Typing rules

**Medium Priority (Implementation):**
- [ ] `NbE-IMPLEMENTATION-PLAN.md` - NbE implementation details
- [ ] `PHASE1-COMPLETE.md` - What was completed in Phase 1
- [ ] `PHASE1.5-PLAN.md` - Current phase goals
- [ ] `LET_IMPLEMENTATION_FINAL.md` - LET expression design
- [ ] `LEGACY-TO-TYPECODE-MIGRATION.md` - Migration notes

**Lower Priority (Research & Exploration):**
- [ ] `lsp-object-file-research.md` - LSP metadata design
- [ ] `debug-info-research.md` - Debugging information
- [ ] `location-information-design.md` - Source location tracking
- [ ] `async-unification-tutorial.md` - Async unification explanation
- [ ] `nbe-vs-legacy-comparison.md` - Implementation comparison
- [ ] `case-splitting.md` - Pattern matching details

**Specialized Topics:**
- [ ] `2ltt-csp.md`, `2ltt-quote.md`, `2ltt-stuck-splice.md` - Two-level TT details
- [ ] `better-elaboration.md`, `eda-workflow-comprehensive.md`
- [ ] `hwml-evaluation-strategy.md`, `hwml-reorg.md`
- [ ] `implementation-plan-lcf.md`
- [ ] `mdbook-integreation.md` - Documentation tooling
- [ ] `metavariable-migration-guide.md`
- [ ] `nbe-architecture.md`, `nbe-quick-reference.md`
- [ ] `poisoned-metavariables.md`
- [ ] `renaming.md`
- [ ] `salsa-location-architecture.md`
- [ ] `simulation-model-stubbing.md`
- [ ] `type-checking-implementation-plan.md`
- [ ] `universes_and_shunting.md`, `universes_and_shunting2.md`

**Meta (Wiki System):**
- [ ] `LLMWiki.md` - (Keep as reference, not to ingest)
- [ ] `WIKI-*.md` - (Keep as reference, not to ingest)

---

## Statistics

**Created:**
- Overview: 1
- ADRs: **8** (of ~10-15 needed) ← **NEW: ADR-007 through ADR-010 (2026-05-03)**
  - ADR-001 through ADR-006: Core architecture, packages, build config
  - ADR-007: Salsa-driven compilation (demand-driven, no topo-sort)
  - ADR-008: VFS abstraction for CLI/LSP unification
  - ADR-009: rkyv zero-copy serialization for `.hwmli` files
  - ADR-010: Metavariable scoping & constraint solver integration
- Components: 0 (of ~6 needed)
- Entities: 1 (of ~15-20 needed)
- Research: 13 (of ~15-20 needed) ← **Major update 2026-05-03 (Buck2 integration added)**
- Onboarding: 0 (of ~5 needed)
- Plans: **FRONTEND-IMPLEMENTATION-PLAN.md** (5-7 week roadmap)

**Progress:** ~36% complete (Phase 1 complete + Frontend plan + state-of-the-art architecture decisions + constraint solver integration)

**Next Steps:**
1. Create remaining high-priority ADRs (002, 003, 005, 006)
2. Create component pages (kernel, elaborator, package-manager)
3. Create key entity pages (bidirectional-typing, lcf-pattern, mvs)
4. Ingest high-priority design documents
5. Generate onboarding guides from accumulated knowledge

---

## Quick Navigation

**I want to understand...**
- "What is HWML?" → [[overview]]
- "Why the LCF kernel?" → [[decisions/ADR-001-lcf-kernel]]
- "Why MVS for packages?" → [[decisions/ADR-004-mvs-package-manager]]
- "What is NbE?" → [[entities/nbe]]

**I want to work on...**
- "The kernel" → [[components/kernel]] (TO CREATE)
- "The elaborator" → [[components/elaborator]] (TO CREATE)
- "Package management" → [[components/package-manager]] (TO CREATE)

**I'm new and want...**
- "To get started" → [[onboarding/new-contributor-guide]] (TO CREATE)
- "To understand the type system" → [[onboarding/type-system-primer]] (TO CREATE)
