# HWML Research Directory

This directory contains research pages documenting external systems, academic papers, and design explorations that inform HWML's architecture.

---

## Quick Navigation

### NEW: Mixfix Operators & Type-Directed Parsing (2026-05-06)

**🎯 START HERE:** [[benes-flow-variational-overloading]] - **NEWEST:** Flow-based variational type-checking (Beneš OOPSLA 2025)

**🔑 Key Insights:**
1. **Beneš (2025) shows HOW to implement backtracking-free type-checking** via variational constraints
2. Represent ambiguities as **"choices"** (variational calculus), prune via **flow-based biunification**
3. **Polynomial complexity O(M×N²)** not exponential O(2^M×N²) – maintains all worlds simultaneously!
4. **Perfect fit for HWML:** Unifies SPPF parse ambiguity + overloading + suspended constraints
5. **🆕 ERROR MESSAGES:** Variational systems produce **BETTER** errors than backtracking (Section 14)!

**📋 Main Documents:**
1. **[[benes-flow-variational-overloading]]** - **NEWEST (2026-05-06):** Deep dive into Beneš OOPSLA 2025, variational type-checking, choice constraints
   - **Section 14:** Why variational systems have BETTER error messages (challenges conventional wisdom!)
   - **Section 15:** No-ambiguity (Rust/Elm) vs Variational comparison - proves "no ambiguity ≠ good errors"
2. **[[parse-forest-type-disambiguation]]** - SPPF + constraint pruning, no type-checker backtracking
3. **[[mixfix-backtracking-free-parsing]]** - Danielsson-Norell analysis, bounded backtracking, precedence DAG
4. **[[mixfix-type-directed-parsing]]** - General survey: mixfix, overloading, dot notation, suspended constraints

---

### Provenance Tracking Research (2026-05-06)

**🎯 START HERE:** [[provenance-action-plan]] - 6-week implementation roadmap with concrete steps

**📋 Main Documents:**
1. **[[provenance-deep-dive]]** - Comprehensive survey: RedPRL philosophy, LSP InfoTree, async solvers
2. **[[provenance-implementation-examples]]** - Concrete code from Lean 4, Agda, GHC, Idris 2, cooltt
3. **[[provenance-action-plan]]** - 5-phase implementation plan (4-6 weeks total)

**🔑 Key Insight:** Provenance is NOT debug info—it's **essential error reporting infrastructure**

---

### Incremental Compilation Research (2026-05-03)

**🎯 START HERE:** [[INCREMENTAL-COMPILATION-SUMMARY]] - Executive summary and quick links

**📋 Main Documents:**
1. **[[incremental-compilation-synthesis]]** - Complete architecture, recommendations, and 6-phase roadmap
2. **[[modern-incremental-compilation]]** - Survey of Rust, GHC, Scala Zinc, Salsa, PIE, Shake
3. **[[modern-build-systems]]** - CAS, Remote Execution API, hermetic builds (Bazel, Buck2, Nix)
4. **[[lsp-and-remote-compilation]]** - LSP performance patterns with remote builds
5. **[[artifact-deduplication]]** - Cross-user cache sharing and deduplication strategies

**📚 Reference:** [[incremental-compilation-references]] - Complete bibliography (38 sources)

---

## All Research Pages

### Type Theory & Elaboration

- [[benes-flow-variational-overloading]] - **NEWEST (2026-05-06):** Beneš OOPSLA 2025 deep dive, variational type-checking, choice constraints, HOW to implement!
- [[parse-forest-type-disambiguation]] - **NEW (2026-05-06):** SPPF + constraints = NO type-checker backtracking!
- [[mixfix-backtracking-free-parsing]] - **NEW (2026-05-06):** Danielsson-Norell analysis, bounded backtracking, precedence DAG
- [[mixfix-type-directed-parsing]] - **NEW (2026-05-06):** Mixfix operators, type-based overloading, suspended constraints
- [[provenance-deep-dive]] - Provenance tracking: RedPRL philosophy, InfoTree, async solvers (comprehensive)
- [[provenance-implementation-examples]] - Production code from Lean 4, Agda, GHC, Idris 2, cooltt
- [[provenance-action-plan]] - 5-phase implementation plan (4-6 weeks, concrete steps)
- [[utf8-diagnostics-rendering]] - UTF-8/graphemes/LSP encoding, diagnostic rendering, InfoTree
- [[elaboration-error-messages]] - Error reporting: constraint origins, global diagnosis, metavar provenance
- [[sterling-structures-bundled-unbundled]] - Sterling's structures: bundled/unbundled, refinements, field deps
- [[structure-types-theory-implementation]] - Deep dive: Type theory & implementation of records/Σ-types
- [[type-unification-structures-implementation]] - Σ-types, records, efficient unification (Abel & Pientka)
- [[extensible-elaborator]] - ExEl: Constraint-based extensible elaborators (ICFP 2025)
- [[togt-heterogeneous-unification]] - Tog⁺: Heterogeneous unification with twin types
- [[disentangling-unification-coercion]] - Jon Sterling: Explicit casts for unification/coercion
- [[crude-but-effective-stratification]] - McBride: Lightweight universe polymorphism

### Debug Information

- [[debug-info-systems]] - Software debug info (DWARF, LLVM, Rust, GHC)
- [[hardware-debug-info]] - Hardware debug info (VCS, Verdi, waveforms, Chisel)
- [[llvm-debug-info-internals]] - LLVM debug info internals (preservation, optimization)
- [[debug-info-research-modern]] - Modern academic research (PLDI 2020-2024)

### Incremental Compilation & Build Systems

- [[incremental-compilation-synthesis]] - **PRIMARY: Complete architecture + roadmap**
- [[modern-incremental-compilation]] - Survey of academic/industry systems
- [[modern-build-systems]] - CAS, RE API, hermetic builds
- [[lsp-and-remote-compilation]] - LSP performance patterns
- [[artifact-deduplication]] - Cache sharing strategies
- [[INCREMENTAL-COMPILATION-SUMMARY]] - Executive summary
- [[incremental-compilation-references]] - Complete bibliography

---

## Research by Topic

### Performance & Optimization

- Incremental compilation systems (Rust, GHC, Scala Zinc)
- Content-addressable storage and artifact caching
- Remote execution and distributed builds
- LSP responsiveness with remote compilation
- Cross-user artifact deduplication

### Type Systems & Semantics

- Extensible elaborators with pluggable constraint solvers
- Heterogeneous unification for dependent types
- Universe polymorphism strategies
- Bidirectional type checking

### Debugging & Diagnostics

- Dual debug strategy (meta-level + object-level)
- Source location preservation through transformations
- Hardware waveform debugging
- Debug info correctness and completeness

---

## How to Use This Research

### For Architecture Decisions

1. Check if an ADR exists in `wiki/decisions/`
2. If not, review relevant research pages
3. Consult synthesis documents (e.g., [[incremental-compilation-synthesis]])
4. Create new ADR with research citations

### For Implementation

1. Read synthesis document for overview
2. Dive into specific research pages for details
3. Check references for original papers/docs
4. Refer to concrete recommendations

### For Onboarding

1. Start with [[wiki/overview]]
2. Read relevant research based on your area (type system, build, debug)
3. Follow cross-references to related pages
4. Check ADRs for final decisions

---

## Research Quality Standards

Every research page includes:

- **Created date** and **confidence score** (0-1)
- **Type** (survey, synthesis, analysis, etc.)
- **Sources** with links and citations
- **Summary** of key findings
- **References** to related wiki pages
- **Implications for HWML** where applicable

---

## Contributing Research

When adding new research pages:

1. Follow template in `WIKI.md` (in root)
2. Cite sources (papers, docs, code)
3. Cross-reference related pages
4. Add to [[wiki/index]] and [[wiki/log]]
5. Include confidence score
6. Provide HWML-specific discussion

---

## External Resources

**Design Documents:** `design/` directory in repository root  
**Academic Papers:** `external/` directory for paper repositories  
**Standards:** Bazel RE API, LSP spec, etc. (linked in research pages)

---

**Questions?** Check [[wiki/README]] for general wiki usage.
