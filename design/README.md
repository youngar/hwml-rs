# HWML Design Documents

This directory contains design documents for the HWML compiler and toolchain.

**Organization (as of 2026-05-02):**
- **This directory:** Processed documents (ingested into wiki) + wiki system docs
- **`to-ingest/` subdirectory:** Documents awaiting wiki ingestion (~57 files)
- **`../wiki/` directory:** LLM-maintained knowledge base derived from these docs

## Documents in This Directory (Processed)

### Core Architecture & Language Design

- **ARCHITECTURE.md** ✅ Ingested into wiki
  - LCF-style trusted kernel architecture
  - Bidirectional type checking
  - Async constraint solving
  - Separation of surface and core languages
  - → Generated: `wiki/decisions/ADR-001-lcf-kernel.md`
  - → Generated: `wiki/decisions/ADR-002-bidirectional-typing.md`

- **package-manager.md** ✅ Ingested into wiki
  - Library manifest format (`hwml.toml`)
  - Dependency resolution (Minimum Version Selection)
  - Compilation cache with content-addressable storage
  - `.hwmli` artifact format for incremental compilation
  - Multi-tier cache strategy (project, per-user, remote)
  - Integration with Salsa incremental computation
  - → Generated: `wiki/decisions/ADR-004-mvs-package-manager.md`

- **hwml.md** ✅ Partially ingested
  - Core language design
  - Universe hierarchy (HType, MType, SType, Type)
  - Modules and functions
  - Surface language concepts
  - → Contributed to: `wiki/overview.md`

### Remaining Documents

**See `to-ingest/README.md` for the 57 documents awaiting ingestion, organized by priority.**

## Key Design Decisions (from Ingested Docs)

### Architecture (ARCHITECTURE.md → Wiki)

**LCF-Style Kernel:**
- Only kernel can construct typed terms
- Evidence tokens prove well-typedness at compile time
- Small trusted computing base (~2000 lines)
- See: `wiki/decisions/ADR-001-lcf-kernel.md`

**Bidirectional Type Checking:**
- Check mode (⇐): verify term has expected type
- Synth mode (⇒): synthesize type from term
- Predictable inference, works for dependent types
- See: `wiki/decisions/ADR-002-bidirectional-typing.md`

**Async Elaboration:**
- Cooperative constraint solving via Rust async/await
- Metavariables can await solution
- See: Referenced in ADR-001, ADR-002

### Package Management (package-manager.md → Wiki)

**Minimum Version Selection (MVS):**
- Deterministic, no silent downgrades
- Explicit `hwml update` for dependency updates
- Reproducibility over automatic updates
- See: `wiki/decisions/ADR-004-mvs-package-manager.md`

**Content-Addressed Artifacts:**
- Hash is identity, URL is hint
- Enables mirror support, reproducible builds
- `.hwmli` format with export interface hashing

**Three-Tier Cache:**
1. Project local (`./.hwml-build/`)
2. Per-user global (`~/.cache/hwml/cas/`)
3. Remote shared (REapi, optional)

**Salsa Integration:**
- In-process queries cache elaboration results in RAM
- `.hwmli` files persist across sessions
- Complementary: Salsa = hot cache, `.hwmli` = cold cache

## Implementation Phases (from Design Docs)

**Phase 1:** ✅ COMPLETE (See `to-ingest/PHASE1-COMPLETE.md`)
- Core kernel with bidirectional typing
- NbE implementation
- Basic elaboration

**Phase 1.5:** 🔄 IN PROGRESS (See `to-ingest/PHASE1.5-PLAN.md`)
- LET expressions
- Improved elaboration

**Phase 2:** PLANNED
- Multi-file elaboration + `.hwmli` serialization
- Per-user CAS cache + garbage collection

**Phase 3:** PLANNED (See `package-manager.md`)
- Package manager (manifests, MVS, install)

**Phase 4:** PLANNED
- Remote cache (REapi client)

**Phase 5:** PLANNED
- LSP enhancements (symbol table, occurrences, type pool)

**Phase 6:** PLANNED
- Fine-grained early cutoff (per-declaration fingerprints)

## Cross-References

- `package-manager.md` references `lsp-object-file-research.md` for LSP metadata
  design decisions
- Both documents reference the Salsa incremental computation framework as a
  complementary layer
- Implementation will be in `hwml-workspace` (new crate) and `hwml-db`
  (integrates with Salsa)

## Reading Order

For new contributors:

1. Start with this README
2. Read `package-manager.md` sections 1-2 (library system + cache basics)
3. Skim `lsp-object-file-research.md` to understand the research basis
4. Return to `package-manager.md` sections 3-6 for detailed implementation plan

For LSP feature development:

1. Read `lsp-object-file-research.md` in full
2. Focus on "Common Patterns" and "Recommendations for HWML" sections
3. Reference `package-manager.md` Part 2 for `.hwmli` format details
4. See implementation phases in both documents

## External References

Key papers and projects cited:

- **Salsa**: https://github.com/rust-analyzer/salsa
- **Go MVS**: https://research.swtch.com/vgo-mvs
- **Zig package manager**: https://ziglang.org/download/0.11.0/release-notes.html#Package-Manager
- **GHC .hie files**: https://www.haskell.org/ghc/blog/20190626-HIEFiles.html
- **SemanticDB**: https://scalameta.org/docs/semanticdb/specification.html
- **Lean 4 server**: https://github.com/leanprover/lean4/blob/master/src/Lean/Server/README.md
- **Buck2 DICE**: https://buck2.build/docs/concepts/dice/
- **Bazel REapi**: https://github.com/bazelbuild/remote-apis

## Design Wiki System (NEW - 2026-05-02)

A proposal for an LLM-maintained knowledge base to organize design decisions, rationales, and research.

### Quick Links
- **Start here:** `WIKI-QUICK-START.md` - Overview and user guide
- **Full proposal:** `WIKI-SYSTEM-PROPOSAL.md` - Complete design
- **Decision summary:** `WIKI-SUMMARY.md` - For decision makers
- **Implementation plan:** `WIKI-BOOTSTRAP-PLAN.md` - Step-by-step execution
- **Examples:** `EXAMPLE-ADR.md` - What wiki pages would look like
- **LLM schema:** `../WIKI.md` (root directory) - Instructions for LLM

### What It Does
- Ingests all design docs and extracts key information
- Builds structured wiki with Architecture Decision Records (ADRs)
- Creates cross-referenced knowledge graph
- Generates onboarding paths for new contributors
- Answers "why?" questions about design decisions
- Maintains itself automatically as new docs are added

### Status
- [x] Proposal complete
- [x] Schema defined
- [x] Examples created
- [ ] Approved for implementation
- [ ] Bootstrap started
- [ ] Full ingestion complete

See `WIKI-SUMMARY.md` for decision points and next steps.

---

## Contributing

When adding new design documents:

1. Create a new `.md` file in this directory
2. Add a summary entry to this README
3. Cross-reference related documents
4. Tag open questions with `QUESTION:` or `TODO:` for easy searching
5. (Optional) If wiki system is active: run `ingest design/new-file.md`
