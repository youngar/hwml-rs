# HWML Design Wiki Log

Chronological record of wiki updates.

---

## [2026-05-08] design | Diagnostic Implementation Plan Revised (from Asai Source)

**Status:** REVISION - Implementation plan updated after studying Asai codebase
**Impact:** **CRITICAL** - Major corrections to rendering approach and type design
**Files:**
- `wiki/design/DIAGNOSTIC-IMPLEMENTATION-PLAN-REVISED.md` (NEW - 310 lines)
- `wiki/design/UNICODE-RENDERING-ASAI-APPROACH.md` (UPDATED - critical corrections)
- `wiki/design/DIAGNOSTIC-VFS-LSP-INTEGRATION.md` (SUPERSEDED notice added)

**Key Discovery:** Studied actual Asai source code in `external/asai/` and found critical implementation details missing from documentation.

**Major Findings:**

1. **Terminal Rendering Uses ANSI Underlines, NOT Column Alignment**
   - Asai uses `\x1b[4m` (underline) to highlight ranges IN the source text
   - The `^` marker is at a FIXED left margin, never aligned with code
   - This is the ONLY way to achieve Unicode correctness
   - NO use of `unicode-width`, `wcwidth`, or any visual width calculation

2. **Severity Has 5 Levels (not 4)**
   - Added `Bug` severity for internal compiler errors
   - Order: Bug > Error > Warning > Info > Hint

3. **Position Caching is Critical**
   ```ocaml
   type position = {
     offset : int;         (* Byte offset *)
     start_of_line : int;  (* Line start offset *)
     line_num : int;       (* 1-indexed *)
   }
   ```
   - Asai stores line info WITH byte offsets to avoid recomputation
   - Our current `Span` only has offsets - inefficient

4. **Backtrace vs. Extra Remarks Separation**
   - Backtrace: Execution context (where elaborator was)
   - Extra remarks: Related notes (other locations)
   - Currently mixed in our design

5. **Block Splitting Feature**
   - Don't show huge files with one error
   - Default threshold: 5 non-highlighted lines
   - Split into blocks around errors

6. **LSP is Deliberately Simple**
   - Callback-based interface
   - NO `positionEncoding` handling (always UTF-8 bytes)
   - Asai source comment: "does not handle positionEncoding"
   - This is OK! Most editors support UTF-8

7. **GitHub Actions Integration**
   - Asai has `Github` module for workflow commands
   - Format: `::error file=main.hwml,line=42::message`

**Implementation Status:**
- Week 1 (Foundation): ✅ Basic types complete, 🔄 needs revision for Position caching
- Weeks 2-6: Updated plan with revised approach

**Changes to Plan:**
- Week 4: Add block splitting, remove pattern detection (→ Week 6)
- Week 5: Complete redesign for ANSI underlines
- Week 6: Add GitHub Actions, custom markers

**Comparison Table:**

| Aspect | Original | Revised (from Asai) |
|--------|----------|---------------------|
| Severity | 4 levels | 5 (add Bug) |
| Span | Byte offsets only | Position with line cache |
| Terminal | Column alignment | ANSI underline + fixed margin |
| LSP | Complex encoding | Simple, UTF-8 only |
| Block splitting | Not planned | Week 4 (from Asai) |

**ADRs Created:**
- ADR-016: No Column Alignment (ANSI underline approach)
- ADR-017: Position Caching (performance optimization)
- ADR-018: Five Severity Levels (add Bug level)

**Week 1 Revision Completed:**
- Updated types based on Asai findings
- All tests passing (24/24)
- Ready for Week 2 (Salsa integration)

**Deep Dive: Asai Pretty Printing (2026-05-08)**
- Analyzed `external/asai/src/Text.ml` and `tty/Tty.ml`
- Documented OCaml Format module integration
- Identified marked source architecture
- Created `ASAI-PRETTY-PRINTING-ANALYSIS.md` with implementation guidance

**Key Findings:**
- Asai uses **Text as formatter functions** (not pre-formatted strings)
- **Three rendering modes:** Color, Monochrome-ANSI, Plain
- **Block splitting** for multi-range diagnostics
- **Marked source** representation separates structure from presentation
- ANSI codes: `[4m` underline, `[31m` red, `[33m` yellow, `[2m` dim

**Integrated into hwml-diagnostic (2026-05-08):**
- Created `src/ansi.rs` with all ANSI codes, colors, symbols from Asai
- Created `src/marked_source.rs` with types for rendering pipeline
- Added `AnsiMode` auto-detection (TTY, TERM, NO_COLOR env vars)
- Added `LineBreaks` enum (Traditional vs Unicode)
- All Week 5 constants and types ready for implementation
- Tests still pass (24/24)

---

## [2026-05-08] research | Diagnostic Framework Design (Inspired by Asai)

**Status:** NEW RESEARCH - Comprehensive diagnostic system design
**Impact:** **HIGH** - Foundation for production-quality error messages
**File:** `wiki/research/diagnostic-framework-design.md`

**Scope:** Complete design for HWML's diagnostic framework based on Asai (浅い), the compiler diagnostics library from the RedPRL team.

**Core Design Principles:**
1. **Five Independent Parameters:** Fatality, error code, severity, backtrace, extra remarks
2. **Location Inheritance:** Automatic context threading (RAII in Rust vs effects in OCaml)
3. **Byte-Level Positions:** Unambiguous, fast, platform-independent
4. **Unicode Display Stability (Level 2):** Beautiful diagnostics across platforms
5. **Structured Messages:** Typed error variants with short codes ("E001" not "type-checking error")

**Key Insights:**
- **Asai has:** Elaboration backtrace, error codes, location inheritance
- **HWML has:** Constraint provenance, meta provenance (unique!)
- **Together:** Best-in-class diagnostics combining both systems

**RAII Pattern for Rust:**
```rust
pub struct DiagnosticContext<'db> {
    trace_stack: Vec<DiagnosticFrame<'db>>,
    current_location: Option<SourceRange<'db>>,
}

// Usage
let _guard = elab.diagnostics.trace(
    format!("checking against {}", ty),
    Some(location),
);
// Auto-pops on return/error
```

**Implementation Plan:**
- **Phase 1:** Core infrastructure (1-2 days)
- **Phase 2:** Error code system (1 day)
- **Phase 3:** RAII trace guards (2-3 days)
- **Phase 4:** Enhanced display (1-2 days)
- **Total:** 3-4 weeks for production-ready system

**Expected Output:**
```
error[E001]: type mismatch at src/main.hwml:42:10
  expected: Nat
  got:      Bool

elaboration backtrace:
  0: checking expression against Nat at src/main.hwml:42:10
  1: checking function return type at src/main.hwml:40:5
  2: checking definition 'process' at src/main.hwml:38:1

constraint context:
  origin: type annotation at src/main.hwml:42:10
  created by: C10
  blocking: C10, C15
```

**Related Files:**
- `asai-detailed-review.md` - Code review of Asai library
- `asai-vs-hwml-comparison.md` - Detailed comparison and gaps
- `external/asai/` - Source code of Asai library

**Next Steps:**
1. Create ADR for diagnostic framework
2. Document error codes catalog
3. Implement 4-phase plan
4. LSP integration
5. User documentation

**UPDATE:** Extended with comprehensive post-processing and rendering design.

---

## [2026-05-08] design | Diagnostic Framework VFS & LSP Integration

**Status:** DETAILED DESIGN - Implementation-ready specification
**Impact:** **CRITICAL** - Complete integration plan for diagnostic framework
**File:** `wiki/design/DIAGNOSTIC-VFS-LSP-INTEGRATION.md` (1619 lines)

**Context:** User requested "write out a detailed design for adding a new diagnostic framework to HWML, including how it is going to integrate with the VFS, file manager, and LSP" - comprehensive specification covering all integration points.

**Document Structure:**

**8 Major Components:**

1. **Salsa Diagnostic Queries**
   - `file_diagnostics(db, SourceFile) -> Arc<Vec<Diagnostic>>` (per-file, cached!)
   - `workspace_diagnostics(db, VfsFileMap) -> Arc<DiagnosticCollection>` (aggregated)
   - Incremental: Only recompute diagnostics for changed files
   - Replace Salsa accumulator pattern with tracked queries

2. **VFS Integration**
   - **No changes to VFS!** Diagnostics are purely derived data
   - Works with all three implementations (OsVfs, LspVfs, MemoryVfs)
   - VFS feeds SourceFile inputs → Salsa invalidates → diagnostics recompute
   - Example: `vfs.update_document()` triggers `file_diagnostics()` recomputation

3. **LSP Integration**
   - Rich diagnostic publishing (related info, code links, auto-fixes)
   - `publish_file_diagnostics()` - single file updates
   - `publish_workspace_diagnostics()` - entire workspace
   - LSP conversion: HWML Diagnostic → LSP Diagnostic with full features
   - VfsFileMap management for workspace tracking

4. **Diagnostic Data Types**
   - Core types: `Diagnostic`, `Span`, `DiagnosticSeverity`, `DiagnosticCode`
   - `Suggestion` with optional `Fix` (auto-fix proposals)
   - `RelatedDiagnostic` for multi-file connections
   - `BacktraceEntry` for elaboration context
   - `DiagnosticBuilder` for ergonomic construction

5. **File Manager Integration**
   - VfsFileMap Salsa input tracks all workspace files
   - Automatic updates on file open/close/change
   - Workspace file discovery integration
   - Incremental updates: Only reprocess changed files

6. **CLI Integration**
   - Terminal renderer with ANSI colors
   - Source snippet rendering (multi-line with context)
   - JSON export for CI/CD
   - Statistics summary (errors/warnings per file)
   - Exit codes for automation

7. **Post-Processing System**
   - `DiagnosticSystem` for dedup, patterns, cascading
   - Deduplication (reduce >30%)
   - Pattern detection (typos, missing returns, wrong arity)
   - Suggestion generation (auto-fix proposals)
   - Cascading error analysis (provenance-based)

8. **Integration Testing**
   - End-to-end LSP tests
   - Incremental update validation
   - Workspace-wide diagnostic tests
   - Performance benchmarks

**Key Architectural Decisions:**

1. **Salsa Queries, Not Accumulators:**
   ```rust
   // OLD (current):
   #[salsa::accumulator]
   pub struct Diagnostics(pub Diagnostic);

   // NEW (proposed):
   #[salsa::tracked]
   fn file_diagnostics(SourceFile) -> Arc<Vec<Diagnostic>>
   ```
   - Enables caching, incrementality, post-processing
   - Cleaner separation of concerns

2. **VFS-Independent:**
   - Diagnostics don't know about VFS
   - VFS feeds Salsa, Salsa computes diagnostics
   - Works identically with all VFS implementations

3. **Incremental by Default:**
   - When file A changes, only `file_diagnostics(A)` recomputes
   - Files B, C, D use cached results
   - 95% reduction in recomputation time for large workspaces

4. **Rich LSP Features:**
   - Related information (multi-file connections)
   - Code descriptions (links to error docs)
   - Diagnostic tags (deprecated, unnecessary)
   - Auto-fix suggestions (LSP Code Actions)

5. **Multiple Output Formats:**
   - Terminal: Human-readable with colors
   - LSP: Rich IDE integration
   - JSON: Machine-readable for CI/CD
   - HTML: Web-based error reports (future)

**6-Week Implementation Plan:**

**Week 1: Foundation**
- Create `hwml-diagnostic` crate
- Core types (`Diagnostic`, `Span`, builders)
- Unit tests

**Week 2: Salsa Integration**
- Add `hwml-db/src/diagnostics.rs`
- Implement `file_diagnostics()` query
- Implement `workspace_diagnostics()` query
- Collect parse & elab errors

**Week 3: LSP Integration**
- LSP conversion (`hwml-diagnostic/src/lsp.rs`)
- Update `Server::compile_file()`
- Implement rich diagnostic publishing
- VfsFileMap management

**Week 4: Post-Processing**
- `DiagnosticSystem` implementation
- Deduplication algorithm
- Pattern detection (5+ common patterns)
- Suggestion generation

**Week 5: Terminal & JSON**
- Colored terminal rendering
- Source snippet rendering (Unicode-aware)
- JSON export schema
- File grouping and statistics

**Week 6: Advanced Features**
- RAII trace guards for backtrace
- Cascading error analysis (provenance)
- `--explain` command
- Performance optimization

**Performance Benefits:**

**Incremental Compilation Example:**
```
Workspace: 100 files
User edits: file A

WITHOUT SALSA:
- Parse all 100 files: 5s
- Elaborate all: 10s
- Total: 17s

WITH SALSA (after first build):
- file_diagnostics(A) recomputes: 150ms
- file_diagnostics(B-Z) cached: 0ms
- workspace_diagnostics aggregates: 50ms
- Total: 200ms

95% REDUCTION!
```

**Memory Overhead:**
- 100 files × 2KB diagnostics = 200KB
- VfsFileMap: ~10KB
- Total: <1MB (negligible)

**Data Flow Examples:**

**Flow A: User Types in VSCode**
```
1. User types → VSCode DidChangeTextDocument
2. LSP vfs.update_document() → file.set_text(db)
3. Salsa invalidates file_diagnostics(file)
4. LSP queries file_diagnostics(db, file) → recomputes
5. Post-process (dedup, patterns, suggestions)
6. Convert to LSP format (related info, code links)
7. PublishDiagnostics → VSCode
8. Red squiggle with hover info
```

**Flow B: CLI Build**
```
1. hwml build → load workspace
2. Create VfsFileMap with all files
3. Query workspace_diagnostics(db, vfs_map)
   → Most files cached!
4. Post-process (dedup, cascading, patterns)
5. Render to terminal (colors, snippets, stats)
6. Exit code 1 if errors
```

**LSP Features Enabled:**

1. **Related Information:**
   ```
   error: type mismatch at line 42

   Related:
   - function declared at line 10
   - used in main at line 55
   ```

2. **Code Descriptions:**
   ```
   error[E0308]: type mismatch

   [Click for details] → https://hwml.dev/errors/E0308
   ```

3. **Auto-Fix Suggestions:**
   ```
   help: add explicit return statement

   [Apply fix] → inserts "return <value>"
   ```

4. **Diagnostic Tags:**
   - Deprecated code (grayed out)
   - Unnecessary code (faded)
   - Unused imports (grayed)

**Migration Strategy:**

**Gradual Rollout:**
1. Week 1-2: Implement new system, keep old
2. Week 3: LSP switches to new system
3. Week 4: CLI gets `--new-diagnostics` flag
4. Week 5: New system becomes default
5. Week 6: Remove old system

**Backward Compatibility:**
```rust
// Keep both during transition
#[salsa::tracked]
fn file_diagnostics_new(...) -> Arc<Vec<Diagnostic>> { ... }

#[salsa::accumulator]  // OLD, will be removed
pub struct Diagnostics(pub Diagnostic);
```

**Success Metrics:**

**Week 3 (LSP):**
- [ ] Diagnostics publish <100ms after file change
- [ ] Related information shows in IDE
- [ ] Code links work
- [ ] Incremental updates only touch changed file

**Week 4 (Post-Processing):**
- [ ] Deduplication reduces count >30%
- [ ] 5+ patterns detected with suggestions
- [ ] Suggestions fix >50% of cases

**Week 5 (Terminal):**
- [ ] Visual inspection passes
- [ ] ANSI colors work
- [ ] Unicode alignment correct
- [ ] JSON validates

**Week 6 (Advanced):**
- [ ] Backtrace shows correct context
- [ ] Cascading errors identified >80%
- [ ] Root causes highlighted
- [ ] `--explain` works

**Files to Create:**

New crate:
- `crates/hwml-diagnostic/Cargo.toml`
- `crates/hwml-diagnostic/src/lib.rs`
- `crates/hwml-diagnostic/src/types.rs`
- `crates/hwml-diagnostic/src/builder.rs`
- `crates/hwml-diagnostic/src/lsp.rs`
- `crates/hwml-diagnostic/src/terminal.rs`
- `crates/hwml-diagnostic/src/json.rs`
- `crates/hwml-diagnostic/src/system.rs`

Database integration:
- `crates/hwml-db/src/diagnostics.rs`

LSP updates:
- Update `crates/hwml-lsp-server/src/main.rs`

CLI updates:
- Update `crates/hwml-cli/src/main.rs`

Tests:
- `crates/hwml-lsp-server/tests/diagnostics.rs`
- `crates/hwml-diagnostic/tests/*.rs`

**Cross-References:**
- `BIG-PICTURE-PIPELINE.md` - Overall architecture (Stage 3-4)
- `research/diagnostic-framework-design.md` - Theoretical foundation
- `research/diagnostic-post-processing.md` - Post-processing algorithms
- `ADR-008-vfs-abstraction.md` - VFS architecture
- Existing LSP implementation in `crates/hwml-lsp-server/`
- Existing Salsa queries in `crates/hwml-db/`

**Key Insights:**

1. **Salsa = Free Incrementality:**
   - Don't reimplement caching
   - Let Salsa handle invalidation
   - Query-based architecture wins

2. **VFS Separation Works:**
   - VFS feeds inputs, doesn't consume outputs
   - Diagnostics are derived data
   - Clean separation of concerns

3. **LSP Richness Matters:**
   - Related information crucial for multi-file errors
   - Code links improve discoverability
   - Auto-fixes save developer time

4. **Post-Processing Adds Value:**
   - Deduplication reduces noise >30%
   - Pattern detection catches common mistakes
   - Cascading analysis finds root causes

**Next Steps:** Implement Phase 1 (Foundation), create `hwml-diagnostic` crate

---

## [2026-05-08] architecture | Big Picture Pipeline

**Status:** NEW ARCHITECTURE DOC - Complete system pipeline from source to kernel
**Impact:** **CRITICAL** - Shows how all components fit together
**File:** `wiki/BIG-PICTURE-PIPELINE.md` (1034 lines)

**Context:** User requested "lay out the big picture pipeline for how these things should work" - comprehensive overview of entire HWML compilation pipeline from parsing to kernel verification.

**Document Structure:**

**8-Stage Pipeline:**
1. **Parsing & Desugaring** - Raw text → AST
2. **Elaboration** - Type checking, constraint solving, trace recording
3. **Error Post-Processing** - Deduplication, cascading analysis, pattern detection
4. **Diagnostic Rendering** - Terminal, LSP, JSON, HTML output
5. **Proof Term Generation** - Elaborated AST → fully explicit KernelTerm
6. **Kernel Verification** - Simple type checking (trusted code base)
7. **Proof Export** - Export to Coq, Lean, Dedukti for cross-verification
8. **Advanced Features** - ML training, proof mining, proof-carrying hardware

**Three Data Flow Paths:**

1. **Happy Path (No Errors):**
   ```
   Source → Parse → Elaborate → Proof Term → Kernel → ✓ ACCEPT
   ```

2. **Error Path (User Mistakes):**
   ```
   Source → Parse → Elaborate (errors) → Post-Process → Render → × USER ERROR
   ```

3. **Bug Path (Elaboration Bug):**
   ```
   Source → Parse → Elaborate → Proof Term → Kernel → × REJECT (BUG IN ELABORATOR)
   ```

**Trust Boundaries (LCF Architecture):**

**TRUSTED (must be correct):**
- Kernel type checker (< 5k LOC)
- Kernel language definition

**UNTRUSTED (can have bugs):**
- Parser (bug → confusing error)
- Elaborator (bug → kernel rejects)
- Diagnostics (bug → confusing messages)
- Proof term generator (bug → kernel rejects)
- External exporters (bug → external checker rejects)

**Key Insight:** Only kernel must be correct! Bug anywhere else → kernel catches it OR confusing error (not unsoundness).

**Implementation Roadmap (18 months):**

**Phase 1 (Weeks 1-4): Foundation**
- Extend error collection to lenient mode
- Record full ElaborationTrace
- RAII TraceGuards for backtrace
- Basic diagnostic output

**Phase 2 (Weeks 5-8): Diagnostics**
- Post-processing pipeline (dedup, cascading, patterns)
- Source rendering with colors
- LSP, JSON, terminal output
- File grouping and statistics

**Phase 3 (Weeks 9-14): Proof Terms**
- Kernel language design
- Proof term generation (ToKernelTerm)
- Trusted kernel implementation (< 5k LOC)
- End-to-end verification

**Phase 4 (Weeks 15-18): External Verification**
- Coq export
- Lean export
- Cross-checker testing

**Phase 5 (Months 5-6): Advanced Features**
- ML training data extraction
- Proof simplification
- Proof mining for bounds

**Phase 6 (Months 7-12): Hardware-Specific**
- Proof-carrying modules
- Compositional verification
- Security certificates

**Key Design Decisions:**

1. **Lenient vs. Fail-Fast:** Lenient (collect all errors)
   - Better UX, enables holistic analysis
   - Already partially implemented

2. **Provenance Graph vs. Explicit Trace:** Both!
   - Provenance for constraints (already exists)
   - ElaborationTrace for full history (needs implementation)

3. **Small Kernel vs. Verified Elaborator:** Small kernel
   - High assurance NOW vs. research project (years)
   - Can add verified elaborator later

4. **Error Messages vs. Proof Terms:** Parallel development
   - Both high priority, different teams
   - Phases 1-2 (diagnostics) + Phases 3-4 (proof terms)

5. **Internal vs. External Verification:** Internal first
   - Prove concept with HWML kernel
   - Add external export for additional confidence

**Success Metrics:**

**Diagnostics:**
- [ ] Deduplication reduces errors by >30%
- [ ] Root cause identification >90% accurate
- [ ] Pattern detection suggests fixes for >50% of errors
- [ ] LSP integration working

**Proof Terms:**
- [ ] Kernel < 5k LOC
- [ ] External checkers agree with kernel
- [ ] Proof generation overhead <10%
- [ ] Kernel checking overhead <5%

**Advanced:**
- [ ] Proof simplification >40% reduction
- [ ] ML training data enables automation
- [ ] Proof-carrying modules integrate with synthesis

**Current Status:**
- ✅ Bidirectional type checking
- ✅ Constraint solving with provenance
- ✅ Salsa incremental
- 🔄 Lenient error collection (partial)
- ❌ Full ElaborationTrace
- ❌ Diagnostic post-processing
- ❌ Proof term generation
- ❌ Trusted kernel

**Visual Diagrams Included:**
- Complete 8-stage pipeline
- Elaboration internals (bidirectional → constraints → solving → instantiation)
- Error post-processing flow
- Multi-format rendering
- Trust boundary separation (TCB diagram)
- All three data flow paths

**Cross-References:**
- `research/proof-distillation-survey.md` - Theoretical foundation
- `research/diagnostic-framework-design.md` - Detailed diagnostic design
- `research/diagnostic-post-processing.md` - Error handling specifics
- All ADRs (especially LCF kernel, bidirectional typing)

**Audience:** Developers, designers, stakeholders, new contributors

**Purpose:** Single comprehensive document showing how ALL pieces fit together

---

## [2026-05-08] research | Proof Distillation in Modern Theorem Provers

**Status:** NEW RESEARCH - Comprehensive survey of proof term generation and distillation
**Impact:** **CRITICAL** - Foundational for trusted compilation and proof certificates
**File:** `wiki/research/proof-distillation-survey.md` (1036 lines)

**Context:** Deep research into "distillation" process in modern theorem provers, covering:
1. Tactic-to-term elaboration (Lean, Coq, Isabelle)
2. Proof compression and simplification
3. Program extraction from constructive proofs
4. Proof mining for quantitative bounds
5. Bidirectional type checking and elaboration traces
6. Proof-carrying hardware verification

**Key Findings:**

**Multiple Meanings of "Distillation":**
- **Meaning A:** Tactic→Term translation (most common in ITPs) - convert high-level proof scripts to kernel-checkable terms
- **Meaning B:** Proof compression (SAT/SMT) - reduce proof size for efficient checking
- **Meaning C:** Proof simplification (ProofOptimizer 2024) - 87% reduction, human readability
- **Meaning D:** Proof mining (Kohlenbach 2025) - extract bounds from proofs

**Universal Architecture Pattern:**
```
High-level Language → Elaboration (untrusted) → Proof Terms → Kernel (trusted)
```
All modern proof assistants (Lean, Coq, Isabelle, Agda) follow this pattern!

**Lean 4 State-of-the-Art:**
- TacticM monad with goal management
- InfoTree recording (tactic before/after states)
- Metavariable-based proof construction
- Independent kernel verification
- Pantograph (2024): Extract proofs as programs

**Coq/MetaCoq Revolutionary Approach:**
- Reimplement Coq in Coq
- Verify type checker correctness
- Proven metatheory (PCUIC)
- TCB reduced to ~10k LOC

**Isabelle Unique Approach:**
- Integrate external ATPs (Z3, Vampire, E, CVC4)
- Sledgehammer: goal → ATP → proof reconstruction
- SMT proof parsing with type inference
- Isar structured proof generation

**Recent ML Research (2024-2025):**

1. **ProofOptimizer (ICLR 2025)**
   - Train LLM to simplify proofs without human demonstrations
   - Expert iteration + reinforcement learning
   - Results: 87% reduction (MiniF2F), 57% (PutnamBench), 72% (IMO 2025)
   - Symbolic linter + iterative shortening

2. **REFACTOR (ICLR 2024)**
   - Extract reusable theorems from proofs
   - Automatic lemma discovery
   - Proof library organization

3. **PACT (NeurIPS 2021)**
   - Mine kernel-level proof terms
   - Self-supervised learning from elaboration traces
   - LEANSTEP dataset

**Program Extraction:**

1. **Minlog (2025)** - Specialized for extraction
   - Theory of Computable Functionals
   - Extract to Haskell
   - Applications: verified number theory, factorization

2. **Isabelle/HOL** - Controlled extraction
   - Example: Pigeonhole principle
     - Direct proof → polynomial program
     - Elegant proof → exponential program
   - Mathematical elegance ≠ computational efficiency!

**Proof Mining (Kohlenbach 2020-2025):**
- Functional interpretation (Gödel's Dialectica)
- Extract quantitative bounds from non-constructive proofs
- Applications: fixed-point theory, ergodic theory, optimization
- **2025 Breakthrough:** First proof mining in probability theory
- Dykstra's algorithm: Expected bar-recursive, got primitive recursive

**Bidirectional Type Checking:**
```
Γ ⊢ e ⇒ A ⊣ e'   (Synthesize: infer type, output elaborated term)
Γ ⊢ e ⇐ A ⊣ e'   (Check: verify type, output elaborated term)
```
- Proof-relevant formulation (Dunfield & Krishnaswami 2021)
- Generic framework (Felicissimo et al. 2023)
- MetaCoq completeness proof (Maillard et al. 2021)

**Proof-Carrying Hardware (2020-2024):**

1. **Formal-PCH (2022)**
   - Verify untrusted IP cores at SoC integration
   - Model checker + theorem prover
   - System-level security properties

2. **VERICA (2022)**
   - Combined attack verification (side-channel + fault injection)
   - First framework for combined physical attacks

3. **Parfait (2024)**
   - 5 abstraction levels: Spec → F★ → C → Asm → Circuit
   - Certified compilation (CompCert, KaRaMeL)
   - Case study: Hardware Security Modules

4. **Foundational PCC (FPCC)**
   - No type-specific axioms
   - Pure mathematical logic
   - Minimal trusted code base

**Extraction vs. Distillation:**
- **Extraction:** Proof → Program (computational content)
- **Distillation:** Proof → Simpler Proof (readability)
- **Dual operations** in Foundational Proof Certificates
  - Elaboration: Certificate → Full proof (fill details)
  - Distillation: Full proof → Certificate (remove redundancy)

**HWML Recommendations:**

**Current State:**
- ✅ Bidirectional type checking
- ✅ Constraint solving with provenance
- ✅ Salsa incremental computation
- ✅ Elaboration/kernel separation

**Proposed Architecture:**
```
User Code → Elaboration + Trace Recording
          ↓
   Elaborated AST + ElaborationTrace
          ↓
   Proof Term Generation (fully explicit)
          ↓
   Trusted Kernel (< 5k LOC)
          ↓
   Accept/Reject
```

**Implementation Phases:**
1. **Phase 1 (2-3 weeks):** Extend provenance to full elaboration trace
   - Constraint records, unification steps, meta assignments
   - Type checking judgments with reasons

2. **Phase 2 (1-2 weeks):** Proof term printer
   - Convert Expr → KernelTerm (fully explicit)
   - Insert all implicit arguments
   - Add all type annotations

3. **Phase 3 (3-4 weeks):** Trusted kernel
   - Simple type checker (no unification, no inference)
   - Auditable < 5k LOC
   - Independent verification

4. **Phase 4 (2-3 weeks):** External proof export
   - Export to Coq, Lean, Dedukti
   - Enable cross-checker verification

**Advanced Features (Future):**
- Proof compression (remove redundant steps)
- Proof explanation (human-readable summaries)
- Proof mining (extract complexity bounds)
- Proof-carrying hardware modules

**Key Papers Referenced:**
- de Moura et al. (2015) - Elaboration in Dependent Type Theory
- Sozeau et al. (2020) - The MetaCoq Project
- Blanchette et al. (2015) - Hammering towards QED
- ProofOptimizer (2024) - Training LLMs to Simplify Proofs
- Kohlenbach et al. (2025) - Proof Mining and Probability Theory
- Miller & Pimentel (2013) - Foundational Proof Certificates

**HWML-Specific Opportunities:**
- Constraint provenance → proof certificates
- Bidirectional checking → certified elaboration
- Salsa incremental → proof caching/reuse
- Hardware focus → proof-carrying RTL modules

**Cross-References:**
- Diagnostic framework design (elaboration backtrace ⇄ proof trace)
- Provenance system (already tracks constraint causality!)
- Type checking architecture (bidirectional already implemented)

---

## [2026-05-08] research | Diagnostic Post-Processing & Rendering

**Status:** NEW RESEARCH - Holistic error analysis and multi-format output
**Impact:** **HIGH** - Addresses user requirements for error processing, source rendering, and output formats
**File:** `wiki/research/diagnostic-post-processing.md` (606 lines)

**Context:** Extension to diagnostic framework design addressing specific requirements:
1. Post-processing pipeline for holistic error analysis
2. Source code rendering with multi-line highlighting
3. Multiple output formats (Terminal, LSP, JSON, HTML)
4. Diagnostic sorting and grouping by file
5. Error deduplication and cascading analysis

**Post-Processing Pipeline:**
1. **Deduplication** - Remove duplicate errors
2. **Cascading Analysis** - Find root causes vs. cascading errors using constraint graph
3. **Intelligent Sorting** - By severity, file, line, column
4. **Pattern Detection** - Recognize typos, missing returns, wrong arity
5. **Suggestion Generation** - Automated fix suggestions
6. **Source Gathering** - Pre-load files for rendering

**Source Rendering Features:**
- Line number gutter with proper width
- Context lines (2 before/after error)
- Caret underlines (`^^^`) with message
- ANSI color highlighting
- Multi-line error spans
- Unicode-aware visual column calculation
- Tab expansion (4 spaces)

**Output Formats:**
- **Terminal:** Human-readable with ANSI colors, summary statistics, file grouping
- **LSP:** Rich IDE integration with related information, code descriptions
- **JSON:** Machine-readable for CI/CD tools, structured data export
- **HTML:** Web-based error reports with CSS styling

**Example Terminal Output:**
```
error[E001]: type mismatch
  --> src/main.hwml:42:10

   40 | fn process(x: Nat) -> Nat {
   41 |     let y = x + 1;
   42 |     return true;
      |            ^^^^ expected Nat, found Bool
   43 | }

elaboration backtrace:
  0: checking expression against Nat at src/main.hwml:42:10
  1: checking function return type at src/main.hwml:40:23

help: consider using an if expression
```

**Architecture:**
```
Elaboration → Vec<ElabError> → Post-Processing → DiagnosticSet
                                                       │
                    ┌──────────────┬──────────────────┼──────────────┐
                    ▼              ▼                  ▼              ▼
               Terminal          LSP              JSON            HTML
```

**Implementation Checklist:**
- Week 1: Post-processing (dedup, cascading, sorting, patterns)
- Week 2: Rendering (source snippets, colors, Unicode handling)
- Week 3: Output formats (Terminal, LSP, JSON, HTML, stats)
- Week 3: Integration (CLI flags, LSP, tests)

**Current State:**
- ✅ Lenient error collection already implemented in `elab_library_with_sccs`
- ✅ `ElabProgramResult` with `errors: Vec<ElabError<'db>>`
- 🔄 Need post-processing and rendering infrastructure

**Related Files:**
- `diagnostic-framework-design.md` - Complete framework (1717 lines, now includes post-processing)
- `DIAGNOSTIC-SYSTEM-SUMMARY.md` - Executive summary (327 lines)
- Current implementation: `crates/hwml-elab/src/error.rs`, `crates/hwml-elab/src/program.rs`

---

## [2026-05-06] decision | ADR-013: UTF-8 Internal Representation

**Status:** NEW ADR - Validate UTF-8 at lexer, use Box<str> internally
**Impact:** **HIGH** - Affects lexer, parser, elaborator (15+ call sites)
**File:** `wiki/decisions/ADR-013-utf8-internal-representation.md`

**Decision:** Validate UTF-8 at lexer boundary, use `Box<str>` in surface syntax, eliminate silent `from_utf8_lossy` failures

**Rationale:**
- Production compilers (rust-analyzer, GHC, Lean 4) all validate at boundary and store validated strings
- Current code uses `String::from_utf8_lossy` (15 sites) which silently masks errors with `�`
- Type-safe `Box<str>` prevents invalid UTF-8 from propagating through pipeline

**Architecture:**
```
Input [u8] → Lexer VALIDATES → Parser from_utf8_unchecked → Surface Box<str> → Word Box<str>
               UTF-8 ✓                  (grammar)              (type-safe!)     (interned)
```

**Changes Required:**
- Surface syntax: `Id.value: Box<[u8]>` → `Box<str>`
- Lexer: Add UTF-8 validation for Identifier/Number tokens
- Parser: Use `from_utf8_unchecked` in LALRPOP grammar (2 sites)
- Elaborator: Remove `from_utf8_lossy` (15 sites), work with `&str` directly

**Supporting Research:**
- `PRODUCTION_COMPILERS_UTF8_STORAGE.md` - How rust-analyzer, GHC, Lean 4 handle strings
- `UTF8_CONVERSION_AUDIT.md` - Audit of 15 problematic conversion sites
- `IMPLEMENTATION_PLAN_UTF8_VALIDATED_STRS.md` - Complete implementation plan

**Implementation:** 7 tasks created for phased rollout

---

## [2026-05-06] research | UTF-8 Diagnostics Rendering: Graphemes, LSP Encoding, Terminal Alignment

**Status:** NEW DEEP RESEARCH - Comprehensive UTF-8 handling in compiler internals
**Impact:** **HIGH** - Critical for LSP correctness and CLI diagnostic quality
**File:** `wiki/research/utf8-diagnostics-rendering.md` (1,709 lines)

**Scope:** Complete research on UTF-8 character representation, diagnostic rendering, and LSP integration:

**Key Topics:**
1. **UTF-8 Spectrum** - Bytes vs code points vs grapheme clusters vs terminal cells
2. **Byte-Level Lexing** - Safe lexing with `&[u8]` and `bstr` crate, validation strategy
3. **Three Position Systems** - Internal (byte offsets), LSP (UTF-16 trap), Terminal (graphemes)
4. **Diagnostic Rendering** - CLI (`miette`), LSP (structured ranges), `asai`-style separation
5. **LSP InfoTree** - Lean 4's approach for interactive elaboration state queries
6. **Production Examples** - rust-analyzer `LineIndex`, GHC source locations, Lean 4 UTF-16 conversion

**Critical Findings:**
- **LSP UTF-16 trap:** Pre-3.17 LSP requires UTF-16 code units, not bytes; must negotiate UTF-8 or maintain translation
- **Terminal rendering fragile:** Emoji width calculation unreliable across terminals; accept best-effort
- **Escape hatch:** LSP sends ranges, editors handle display (no ASCII-art needed)
- **Structured diagnostics:** Generate once (byte-based), render many ways (CLI, LSP, JSON)
- **InfoTree for DT:** Custom RPC endpoints needed for dependent type interactivity (metavars, goal state)

**HWML Status Assessment:**
- ✅ Has: Byte-level lexing, lossless grammar, line break tracking
- ❌ Lacks: UTF-16 conversion, structured diagnostics, LSP InfoTree, invalid UTF-8 handling
- **Priority:** High (UTF-16 for LSP), High (`miette` for CLI), Medium (InfoTree)

**Implementation Roadmap:**
- **Phase 1 (Week 1):** Fix lexer error handling, add UTF-8 validation, Unicode tests
- **Phase 2 (Week 2):** `LineIndex` struct, UTF-16 conversion, LSP negotiation
- **Phase 3 (Week 3):** Structured diagnostics, `miette` CLI renderer, LSP renderer
- **Phase 4 (Weeks 4-5):** InfoTree, custom RPC (`$/hwml/metavarInfo`, `$/hwml/goalState`)
- **Phase 5 (Week 6):** Grapheme clusters, lazy caching, pathological Unicode tests

**Complements:** [[research/elaboration-error-messages]] (error reporting philosophy)
**Builds On:** [[implementation/location/streaming-lexer-advantage]] (lossless lexing)
**Informs:** Future ADR on diagnostic architecture

**References:**
- Unicode Standards: UAX#11 (width), UAX#29 (graphemes), UAX#31 (identifiers)
- LSP Spec 3.17: Position encoding negotiation
- rust-analyzer: `line_index.rs` implementation
- Lean 4: `Lean.Data.Lsp.Utf16`, InfoTree architecture
- Crates: `bstr`, `miette`, `unicode-segmentation`, `unicode-width`, `tower-lsp`

---

## [2026-05-04] research | Sterling's Structures: Bundled/Unbundled, Refinements, Dependencies

**Status:** NEW RESEARCH - Jon Sterling's Pterodactyl approach to structures
**Impact:** **CRITICAL** - Practical design patterns for HWML structures
**File:** `wiki/research/sterling-structures-bundled-unbundled.md` (984 lines)

**Scope:** Comprehensive analysis of Jon Sterling's innovations for structures in dependent types:

**Part I: Large-by-Default Structures (Fuss-Free Universes)**
- Problem with traditional universe hierarchies (6+ universe variables per definition)
- Sterling's solution: Work from top down, constrain only when needed
- Dream code: `theory Category` (no universe constraints!)
- Specialize later: `LocallySmallCategory`, `SmallCategory`
- Automatic implicit coercions in theory hierarchy
- **HWML benefit:** Hardware structures naturally large, only constrain for synthesis

**Part II: Theory Refinements**
- Refinement syntax: `Theory / {field => value, ...}`
- Example: `Monoid / {car => Nat}` (monoid on natural numbers)
- Telescope interpretation (remaining fields become constructor)
- Multiple fields: Eckmann-Hilton argument (two monoids sharing carrier)
- **HWML application:** `AXI4Stream / {dataWidth => 32}` for specific widths

**Part III: Canonical Coercions for Refined Theories**
- Problem: Naive coercion causes eager η-expansion (term size blowup)
- Solution: Canonical coercion via commuting diagrams
- Algorithm: Check squares commute, use syntactic constructor (no expansion)
- Benefit: Transparent, avoids term blowup
- Concrete example: `Monoid/{car=>Nat} → Semigroup/{car=>Nat}`

**Part IV: Selfification - Avoiding Dependent Coercions**
- Problem: Dependent coercions (Luo & Soloviev, Lean) have issues
- Luo & Soloviev: Most expressive rules break transitivity
- Lean: Explicitly doesn't support chaining
- **Sterling's trick (from ML Modules):** Transform to non-dependent!
- Algorithm: Maximal singleton refinement → non-dependent coercion
- Example: `cool (X : Monoid) : Semigroup/{car => X.car}` elaborates cleanly
- Heritage: Harper & Lillibridge VALUE rules, Leroy signature strengthening

**Part V: Bundled vs Unbundled Structures**
- Bundled: All data in record (Sterling's default)
- Unbundled: Carrier separate (type class style)
- Sterling: Bundled with refinements for unbundled effect
- Automatic coercions between bundled ↔ unbundled
- **HWML:** Both styles natural for hardware (interfaces vs operations)

**Part VI: Field Dependencies - Forward and Backward?**
- Standard (forward): `data : Array length` (depends on earlier field) ✅
- Question: Can type depend on **future** field?
- **Answer: No, not directly** in standard dependent type theory
- Reasons: Sequential Σ-types, elaboration order, decidability
- Contrast with mutual data types (those work differently)

**Part VII: What Would Backward Dependencies Require?**
- Unordered telescopes (dependency graphs)
- Bidirectional elaboration (3-pass: collect names, resolve deps, type check)
- Type-level constraint solving (quickly undecidable!)
- Implementation challenges (mapping user order ↔ elaboration order)
- **Conclusion:** Theoretically possible, practically challenging

**Part VIII: Proposal for HWML**
- **Conservative (recommended):** Forward dependencies only
  - Decidable, predictable, matches Lean/Agda/Coq
- **Pragmatic middle ground:** Automatic reordering
  - User writes any order, elaborator reorders, remembers mapping
  - Error messages use user order
- **Experimental (future research):** True backward dependencies
  - Dependency graph elaboration, bidirectional constraints
  - Research project, not production ready

**Part IX: Sterling's Unified Treatment**
- Theory hierarchy + Refinements + Coercions + Explicit casts
- All fit together coherently
- Hardware hierarchy example with automatic coercions
- Explicit casts when ambiguous

**Key Innovations:**
1. **Large-by-default** eliminates universe bureaucracy
2. **Refinements** provide flexible partial instantiation
3. **Selfification** avoids dependent coercion issues
4. **Bundled + Refinements** = best of both worlds
5. **Explicit casts** for reliability (see [[disentangling-unification-coercion]])

**Backward Dependencies Conclusion:**
- **Theoretically possible** with elaborator extensions
- **Not practically necessary** - reordering + parameters solve most cases
- **HWML recommendation:** Phase 1 forward-only, Phase 2 auto-reorder, Phase 3+ research

**Sources:**
- Sterling's Pterodactyl worklog (jonmsterling.com/01HC)
- [01HX] Fuss-free universes
- [01JQ] Disentangling unification and coercion
- [01HN] Lifting coercions to theory refinements
- ML Modules literature (Harper, Leroy, Stone, Crary)
- Dependent coercion issues (Luo & Soloviev, Lean)

**Cross-references:**
- [[disentangling-unification-coercion]] (Sterling's explicit casts - already in wiki)
- [[structure-types-theory-implementation]] (Type theory foundations)
- [[type-unification-structures-implementation]] (Unification algorithms)
- [[crude-but-effective-stratification]] (McBride's universes)

**Confidence:** 0.95 (Sterling's published work + established type theory)

---

## [2026-05-04] research | Structure Types - Type Theory & Implementation Deep Dive

**Status:** NEW RESEARCH - Comprehensive treatment of records/Σ-types
**Impact:** **FOUNDATIONAL** - Core understanding for HWML's type system
**File:** `wiki/research/structure-types-theory-implementation.md` (1,812 lines!)

**Scope:** Complete deep dive into structure types covering:

**Part I: Type-Theoretic Foundations**
- Σ-types: Formation, introduction, elimination, computation rules
- From binary Σ-types to n-ary records
- Dependent records (later fields depend on earlier ones)
- Telescopes as generalization (sequences of dependent types)
- Σ-types vs Products vs Records (detailed comparison)
- Subtyping and subsumption (3 approaches analyzed)

**Part II: The Eta-Equality Decision** ⚠️ **CRITICAL SECTION**
- What eta equality means for records
- With eta: Extensionality, automatic coercions, simpler equality (but slower)
- Without eta: Faster, pattern matching, explicit construction
- Trade-off analysis with performance numbers
- Impact on unification algorithm (decomposition, η-contraction)
- **HWML recommendation:** User-controllable per-record (like Agda)

**Part III: Implementation Strategies**
- Memory representation (flat tuple vs boxed vs hybrid)
- Projection compilation (direct offset vs field index vs generated functions)
- Term representation in type checker (Rust code sketches)
- Lean 4 implementation details (C++ internals, structure compilation)
- Agda implementation details (Haskell internals, eta-expansion)
- Hash consing for records (6x speedup demonstrated)

**Part IV: Categorical Semantics**
- Records as products (universal property)
- Dependent products (Σ-types as indexed coproducts)
- Fibration perspective
- Explanation of Abel & Pientka's isomorphisms via category theory
- Logical relations for records (strong normalization proofs)

**Part V: Advanced Topics**
- Recursive records (positivity checking)
- Mutually defined records
- Record update syntax (functional updates)
- Type classes as records (Lean 4 approach)
- Hierarchies and inheritance (mathematical structures, diamond problem)

**Part VI: Pattern Matching on Records**
- Copatterns vs patterns (two ways to define projections)
- Irrefutable patterns (single constructor)
- Dependent pattern matching (type refinement)
- Critical for hardware: bit-width guarantees via patterns

**Part VII: Normalization and Conversion**
- Weak head normal form (WHNF) for records
- Conversion checking (with vs without eta)
- Normalization by evaluation (NbE) for records
- Eta normalization via eval-reify cycle

**Part VIII: HWML-Specific Considerations**
- Hardware structures (AXI4-Stream example with 6 fields)
- Clock domain tracking (prevent mixing via dependent types)
- Bit-accurate types (exact widths, type-level arithmetic)
- Stateful vs stateless records (sequential vs combinational)
- Synthesis pragmas (always_comb, always_ff annotations)

**Part IX: Performance Analysis**
- Benchmarking record operations (comparison table)
- Large record optimization (lazy fields, incremental update, chunking)
- Cache-friendly layout (hot fields first, SoA vs AoS)

**Part X: Correctness Properties**
- Type safety (preservation + progress proofs)
- Canonicity (closed terms normalize to canonical form)
- Decidability (type checking, conversion, pattern coverage)

**Part XI: Comparison with Other Approaches**
- OOP objects vs dependent records (mutability, inheritance, memory model)
- C structs vs type theory records (dependent fields, type-level computation)
- Row polymorphism vs records (structural vs nominal)

**Part XII: Implementation Checklist for HWML**
- Phase 1: Basic records (parsing, elaboration, type checking)
- Phase 2: Eta equality (user-controlled, unification, conversion)
- Phase 3: Advanced features (updates, extension, inheritance)
- Phase 4: Performance (hash consing, memoization, NbE)
- Phase 5: Hardware-specific (clock tracking, bit-widths, synthesis)

**Key Theoretical Results:**
- Eta equality ≡ Universal property of products (category theory)
- Records preserve type safety, canonicity, decidability
- With eta: Unique normal forms, extensional equality
- Without eta: Faster normalization, pattern matching available

**Implementation Insights:**
- **Lean 4 approach:** Structures as special inductives (recommended for HWML)
- **Generated projections:** One function per field (inlinable, type-safe)
- **Hash consing:** Essential for large hardware structures (sharing + fast equality)
- **Eta control:** Must be user-selectable (mathematical vs hardware needs differ)

**Performance Numbers:**
- Hash consing: 0.5-0.7x memory usage (sharing)
- Eta equality: 3-5x slower comparison, 5-10x slower normalization
- Pointer comparison with hash consing: O(1) equality check

**Hardware Applications:**
- Standard interfaces (AXI4, AMBA, APB) as records
- State machines (bundled state + signals)
- Configuration records (parameters + constraints)
- Clock domain safety via dependent records

**Confidence:** 0.95 (formal type theory + Lean 4/Agda/Coq source code analysis)

**Complete Bibliography:**
- Type theory: Martin-Löf, HoTT Book, Nordström et al.
- Records: Coquand, Pollack, AUTOMATH
- Eta equality: Goguen/McKinna/McBride, Abel copatterns
- Categorical semantics: Jacobs, Awodey, Seely, Bénabou
- Implementation: Lean 4, Agda, Coq, Idris 2 source code
- Performance: Filliatre/Conchon hash consing, Abel NbE

**Cross-References:** Links to 6 existing wiki pages (unification, Tog⁺, Sterling, ExEl, NbE, ADRs)

---

## [2026-05-04] research | Type Unification with Structures - Comprehensive Survey

**Status:** NEW RESEARCH - Deep dive into efficient unification algorithms
**Impact:** Critical for HWML elaborator implementation
**File:** `wiki/research/type-unification-structures-implementation.md` (842 lines)

**Scope:** Comprehensive survey of type unification in dependent types, focusing on:

1. **Σ-types (dependent pairs/records)** - Abel & Pientka's isomorphism-based algorithm
2. **Implementation in production systems** - Agda, Lean 4, Coq, Epigram
3. **Module systems** - ML modules, Mathematical Components, 1ML
4. **Performance optimizations** - Hash consing (6x), occurs check optimization (4.4x)

**Key Findings:**

**Algorithm Choice:**
- **Primary:** Abel & Pientka (2011) constraint-based unification for λΠΣ-calculus
- **Core insight:** Use type isomorphisms to flatten Σ-types into Π-types during unification
- **Extensions:** Kovács's nested patterns, Tog⁺ twin types (Phase 2)

**Performance Critical Optimizations:**
- Hash consing: 131s → 22s (6x speedup on Tog⁺ setoid benchmark)
- Syntactic equality fast path: O(1) with hash consing
- Linearization (occurs check): Up to 445% improvement (Pientka & Pfenning)
- Spine representation: Direct head access for pattern matching

**Structure Representation:**
- **Recommendation:** Lean 4-style structures (single constructor inductives)
- Auto-generated projections
- Eta-equality controlled per-structure
- Clean interaction with unification algorithm

**HWML-Specific Considerations:**
- Hardware structures often regular → excellent candidates for hash consing
- Clock domains: Should participate in unification as type-level constraints
- Bit-width inference: Hybrid approach (local inference, required annotations at boundaries)
- Flattening strategy: Lazy on-demand during unification (not eager)

**Implementation Roadmap:**
1. **Phase 1:** Basic Miller pattern unification (current)
2. **Phase 2:** Add Σ-type transformations (Abel & Pientka)
3. **Phase 3:** Performance optimizations (hash consing, memoization)
4. **Phase 4:** Advanced features (twin types, explicit casts - only if needed)

**Research Sources:**
- Abel & Pientka (TLCA 2011) - Primary algorithm
- Kovács (2020-2026) - Nested patterns, observational postponement
- Pientka & Pfenning (CADE 2003) - Occurs check optimization
- Agda, Lean 4, Coq source code - Production implementations
- Epigram, 1ML, Mathematical Components - Module system designs

**Cross-References:**
- Links to [[togt-heterogeneous-unification]] (twin types)
- Links to [[disentangling-unification-coercion]] (Kovács's work, Sterling's casts)
- Links to [[extensible-elaborator]] (constraint-based architecture)
- Links to [[ADR-010-metavariable-scoping-constraint-solver]] (HWML's current solver)

**Confidence:** 0.9 (based on published papers + battle-tested implementations)

---

## [2026-05-03] decisions | Critical Fix to ADR-008 VFS Architecture 🚨

**Status:** CRITICAL BUG FIX - ADR-008 completely rewritten
**Impact:** Prevents catastrophic cache invalidation failure

**Problem Identified:** The original ADR-008 design would have **completely broken Salsa's incremental caching**. The proposed architecture stored VFS in `Arc<RwLock<>>` inside `HwmlDatabase` and had queries pull from it:

```rust
// ❌ CATASTROPHICALLY BROKEN (original design)
#[salsa::db]
pub struct HwmlDatabase {
    vfs: Arc<RwLock<Box<dyn Vfs>>>,  // ← Hidden state
}

#[salsa::tracked]
pub fn file_text(db: &dyn Db, file: File) -> String {
    db.vfs().file_text(file.id(db))  // ← Side-effect!
}
```

**Why this breaks:**
- Salsa tracks query inputs to invalidate cache
- Input to `file_text(File(42))` is ID `42` (never changes)
- Actual file content hidden behind RwLock side-effect
- LSP updates text via `vfs.update_file()` → **Salsa has no idea data changed**
- Cache never invalidated → LSP stuck on first keystroke

**The Fix:** VFS feeds Salsa inputs, doesn't hide behind RwLock:

```rust
// ✅ CORRECT (revised design)
#[salsa::input]
pub struct SourceFile {
    #[return_ref]
    pub path: PathBuf,
    #[return_ref]
    pub text: String,  // Salsa INPUT, tracked directly
}

pub struct CompilerSession {
    db: HwmlDatabase,  // No VFS inside!
    vfs: Box<dyn Vfs>, // Lives outside, feeds Salsa
}

impl CompilerSession {
    pub fn update_file(&mut self, path: &Path, new_text: String) {
        let file = self.vfs.get_file(path);
        file.set_text(&mut self.db).to(new_text);  // ← Pushes into Salsa!
    }
}
```

**Key Architectural Change:** VFS inverted from "Salsa queries VFS" to "VFS feeds Salsa inputs"

---

## [2026-05-03] decisions | State-of-the-Art Frontend Architecture ADRs

**Status:** Architecture decisions codified (with critical ADR-008 fix applied)
**Goal:** Document architectural decisions for multi-file compilation and LSP, incorporating modern compiler construction best practices

**Pages Created:**
- [[decisions/ADR-007-salsa-driven-compilation]] - Demand-driven compilation (no manual topological sorting)
- [[decisions/ADR-008-vfs-abstraction]] - Virtual File System for unified CLI/LSP execution
- [[decisions/ADR-009-rkyv-zero-copy-serialization]] - Zero-copy deserialization for `.hwmli` artifacts
- [[decisions/ADR-010-metavariable-scoping-constraint-solver]] - **Metavariables never escape Salsa queries** ⭐ **CRITICAL**

**Pages Updated:**
- [[wiki/FRONTEND-IMPLEMENTATION-PLAN.md]] - Refactored to incorporate all four ADRs
  - Added Phase A0: VFS Infrastructure (prerequisite for all multi-file work)
  - Replaced manual topological sorting with Salsa-driven recursive queries
  - Changed from bincode to rkyv for artifact serialization
  - Added detailed LSP VFS integration steps
  - **Added three-level architecture:** Salsa (cross-library), SCC solver (intra-library), LCF kernel (verification)
  - Detailed constraint solver implementation with worklist algorithm
- [[wiki/index.md]] - Updated statistics (8 ADRs now, 36% complete), added new ADRs to index
- [[decisions/ADR-007-salsa-driven-compilation]] - Added references to ADR-010, clarified elaboration boundary

**Decision Summary:**

### ADR-007: Salsa-Driven Compilation

**Problem:** How to orchestrate multi-library compilation? Traditional batch compilers use manual topological sorting.

**Decision:** Use Salsa's demand-driven query system throughout. NO manual topological sorting.

**Rationale:**
1. **Salsa IS a dependency graph engine**: Implementing topo-sort duplicates Salsa's functionality poorly
2. **Better cycle detection**: Salsa provides precise stack traces, not just "cycle exists"
3. **Automatic incrementality**: File change → Salsa recomputes only affected queries
4. **Unified CLI/LSP**: Both frontends use identical query paths
5. **Future parallelism**: When Salsa supports parallel queries, we get it for free

**Key pattern:**
```rust
#[salsa::tracked]
pub fn library_interface(db: &dyn Db, workspace: WorkspaceRoot, lib_name: String)
    -> Result<Hwmli, ElabError>
{
    // Recursively query dependencies
    for dep in &manifest.dependencies {
        let _dep_interface = library_interface(db, workspace, dep.name.clone())?;
        // Salsa memoizes, handles order, detects cycles
    }
    // Elaborate this library
}
```

**Execution is query-driven:** Call `library_interface(db, ws, "top-level-lib")` and Salsa handles execution order.

---

### ADR-008: VFS Abstraction

**Problem:** LSP must typecheck unsaved files (in editor buffers), but compiler reads from disk.

**Decision:** Introduce VFS abstraction layer. Compiler NEVER directly accesses filesystem.

**Rationale:**
1. **LSP requires unsaved file access**: Must show errors as user types, before saving
2. **Unified testing**: Unit tests use `MemoryVfs` (no disk I/O, no tempfiles)
3. **Industry best practice**: rust-analyzer, Sorbet, LSP spec all recommend VFS
4. **Future features**: Enables caching, remote filesystems, overlay filesystems

**Architecture:**
```rust
pub trait Vfs {
    fn file_text(&self, id: FileId) -> Option<String>;
    fn create_file(&mut self, path: PathBuf, text: String) -> FileId;
    fn update_file(&mut self, id: FileId, text: String);
}

// Three implementations:
// - OsVfs: Reads from disk (CLI)
// - LspVfs: In-memory buffers (LSP)
// - MemoryVfs: Pure in-memory (testing)
```

**Integration:** VFS injected into Salsa database at creation time. Queries read files via VFS.

---

### ADR-010: Metavariable Scoping and Constraint Solver Integration ⭐ **CRITICAL**

**Problem:** Dependent type elaboration uses metavariables (type holes) and constraint solving, which is inherently stateful. Salsa requires pure, deterministic functions. How do we integrate constraint solving with Salsa?

**The Disaster Scenario:** If you try to make constraint solving into Salsa queries, the compiler crashes:
- **Cycle panics:** Constraint A → Constraint B → Constraint A (Salsa detects false cycle)
- **Cache defeats:** Metavariable unifications mutate global state (Salsa cache invalidated constantly)
- **Non-determinism:** Constraint ordering varies (different outputs from same inputs, Buck2 caching breaks)

**Decision:** **The Golden Rule: Metavariables Never Escape Salsa Queries**

**Three-level architecture:**

**Level 1: Cross-Library Dependencies (Salsa-Driven)**
```rust
#[salsa::tracked]
pub fn library_interface(db: &dyn Db, root: WorkspaceRoot, lib_name: String)
    -> Result<Hwmli, ElabError>
{
    // Pure, cacheable cross-library dependency handling
    for dep in &manifest.dependencies {
        library_interface(db, root, dep.name.clone())?;
    }

    elaborate_library_with_local_solver(db, root, lib_name, files)
}
```

**Level 2: Within-Library Elaboration (Local Solver)**
```rust
#[salsa::tracked]
pub fn elaborate_library_with_local_solver(...) -> Result<Hwmli, ElabError> {
    let sccs = compute_declaration_sccs(db, files)?;

    for scc in sccs.topo_order() {
        // Fresh ElabState per SCC
        elaborate_scc_with_local_state(db, root, lib_name, scc)?;
    }

    // Return pure, metavariable-free declarations
}
```

**Level 3: SCC Elaboration (The "Async" Solver)**
```rust
fn elaborate_scc_with_local_state(...) -> Result<HashMap<DeclId, Declaration>> {
    // Local metavariable context (lives only for this SCC)
    let mut elab_state = ElabState { metas, worklist };

    // Phase 1: Elaborate signatures → solve → zonk
    // Phase 2: Elaborate bodies → solve → zonk
    // Phase 3: Kernel verification

    // ElabState destroyed, return pure CoreTerms
}
```

**The Worklist Solver ("Async" = Iterative, NOT Rust async/await):**
```rust
fn solve_constraints_to_fixpoint(state: &mut ElabState) -> Result<()> {
    loop {
        let mut progressed = false;
        let mut stalled = Vec::new();

        for constraint in state.worklist.drain(..) {
            match try_solve(constraint, &mut state.metas) {
                Solved => { progressed = true; }
                Stalled(c) => { stalled.push(c); } // Blocked, retry next iteration
                Error(e) => { return Err(e); }
            }
        }

        state.worklist = stalled;
        if !progressed { break; } // Done or stuck
    }
}
```

**Why this works:**
1. **Perfect caching:** Salsa caches (Surface AST → Core AST), not metavariable soup
2. **Deterministic:** Same inputs → same constraint solving order → same outputs
3. **No cycle panics:** Constraint iteration is local, not via Salsa queries
4. **LCF boundary:** Kernel never sees metavariables, catches elaborator bugs

**Matches state-of-the-art:**
- rust-analyzer + chalk: Trait solving local to query execution
- Lean 4: MetavarContext per elaboration
- GHC 9+: Constraint solving within module compilation

---

### ADR-009: rkyv Zero-Copy Serialization

**Problem:** LSP must load dozens of `.hwmli` interface files quickly (<100ms total startup).

**Decision:** Use `rkyv` for zero-copy deserialization of `.hwmli` files.

**Rationale:**
1. **Performance critical for LSP**: rkyv load <1ms per file (20x faster than bincode)
2. **Memory-mapped files**: OS manages paging, only accessed pages loaded
3. **Schema evolution**: Can add fields without breaking old files
4. **Validation**: Runtime checks prevent crashes from corrupted files
5. **Industry adoption**: Discord, Mozilla servo, multiple blockchain projects

**Benchmark comparison:**
```
Serialize:   bincode: 184ns   rkyv: 96ns    (1.9x faster)
Deserialize: bincode: 370ns   rkyv: 0ns     (instant!)
Size:        bincode: 118 B   rkyv: 110 B   (7% smaller)
```

**Usage pattern:**
```rust
// Write
let bytes = hwmli.to_bytes()?;
std::fs::write("lib.hwmli", bytes)?;

// Zero-copy load
let file = File::open("lib.hwmli")?;
let mmap = unsafe { Mmap::map(&file)? };
let archived = rkyv::check_archived_root::<Hwmli>(&mmap)?;
// `archived` usable immediately, no deserialization!
```

---

**Why These Decisions Matter:**

These three ADRs form a **cohesive state-of-the-art architecture**:

1. **Salsa + VFS** = CLI and LSP share identical code paths
   - Change file → VFS updated → Salsa invalidates → Recompute affected queries
   - Same flow for both frontends (CLI reads from disk, LSP from memory)

2. **Salsa + rkyv** = Blazing fast incremental compilation
   - Query dependency libs → rkyv loads instantly (<1ms each)
   - Salsa memoizes, only recomputes what changed
   - LSP startup <100ms even with 50 libraries

3. **VFS + rkyv** = Robust testing and deployment
   - Unit tests use MemoryVfs (fast, no cleanup)
   - Artifacts validated on load (prevents corruption crashes)
   - Schema evolution (add fields without breaking old files)

**Together:** Matches or exceeds architectures in rust-analyzer, Sorbet, GHC 9+, and Scala's Bloop.

---

**Implementation Priority:**

Phase A0 (VFS) MUST be done first before any multi-file work:
- Week 1, Days 1-2: Implement VFS infrastructure
- Then: Manifest parsing, .hwmli format, Salsa queries
- Rationale: VFS is prerequisite for both CLI and LSP. Doing it early prevents rework.

---

**Success Metrics:**
- [ ] No `std::fs::read_to_string` in `hwml-core` or `hwml-elab` (all via VFS)
- [ ] No topological sort code in codebase (Salsa handles ordering)
- [ ] LSP startup <100ms for 50 libraries (rkyv instant loading)
- [ ] LSP typechecks unsaved files correctly (VFS provides in-memory text)
- [ ] Unit tests use MemoryVfs (no disk I/O)

---

## [2026-05-03] research | Buck2 integration patterns for language compilers

**Status:** Research complete
**Goal:** Extract Buck2 integration best practices from design/buck2-integration.md and synthesize with existing build system research

**Pages Created:**
- [[research/buck2-integration-patterns]]

**Pages Updated:**
- [[decisions/ADR-006-multi-layer-build-configuration]] - Added persistent worker support section and references
- [[wiki/index.md]] - Added new research page to index

**Research Focus:**

**Source:** `design/buck2-integration.md` - Comprehensive guide to integrating language compilers with Buck2

**Key Findings:**

1. **Four-Layer Architecture** (industry best practice):
   - **Layer 1**: Pure compiler core (`libmylang`) with query engine (Salsa/DICE)
   - **Layer 2**: Interface layer (VFS, source database)
   - **Layer 3**: Three execution frontends:
     - Cold-start CLI (remote execution, one-off builds)
     - Persistent worker (fast local Buck2 builds)
     - Language server (LSP for editors)
   - **Layer 4**: Build system bridge (Starlark rules, BXL project generator)

2. **Persistent Worker Protocol** (critical for performance):
   - **Problem**: Warm daemon (2ms recompiles) vs stateless CLI (Buck2 requirement)
   - **Solution**: `--persistent_worker` mode with stdin/stdout protocol
   - Keeps ASTs in memory between Buck2 requests
   - 10-100x faster than cold-start per module
   - Used successfully by Java, Scala, Rust in Buck2/Bazel

3. **LSP Integration via BXL** (recommended path):
   - Write `generate_project.bxl` script
   - Traverses Buck2 build graph
   - Generates `hwml-project.json` (like `rust-project.json`, `compile_commands.json`)
   - LSP reads JSON on startup → understands workspace
   - Alternative: Build Server Protocol (BSP) - less mature in Buck2

4. **Reference Implementations**:
   - **Rust + rust-analyzer**: Salsa framework, Buck2 generates `rust-project.json`
   - **Hack**: `hh_server` daemon + `hh_client` CLI, saved states from remote cache
   - **Zig**: Compiler as build system, content-addressed caching built-in
   - **Sorbet**: Bazel-first typechecker, 100k+ lines/sec via strict hermeticity

5. **Compiler Requirements**:
   - Dependency emitting: `--emit-deps out.d` (machine-readable file list)
   - Response files: `@args.txt` (handle long command lines)
   - JSON diagnostics: `--message-format=json` (parseable errors)
   - Zero implicit state: No `~/.mylangconfig`, no hidden caches

6. **Anti-Pattern: `ccache`**:
   - Why impure: Hidden `~/.ccache` directory outside Buck2's control
   - Breaks hermeticity: Different results based on cache state
   - HWML solution: In-memory caching only (persistent worker), let Buck2 handle disk caching

**Integration with ADR-006:**
- ADR-006 defines three-layer build config (manifest, build, lock)
- Buck2 integration adds execution model (persistent workers, remote execution)
- Synergy: Standalone HWML uses `hwml build`, Buck2 integration uses Buck2's CAS
- LSP works in both modes (reads `hwml-project.json` or `hwml-workspace.toml`)

**Implementation Roadmap:**
- Phase 1 (M1-3): Pure compiler core with Salsa
- Phase 2 (M4-5): Persistent worker protocol
- Phase 3 (M6-8): LSP server
- Phase 4 (M9-10): Buck2 Starlark rules
- Phase 5 (M11-12): BXL project generator

**Related Research:**
- [[research/build-system-caching-synthesis]] - Persistent worker details, three-tier caching
- [[research/modern-build-systems]] - Buck2/Bazel/Nix overview
- [[decisions/ADR-006-multi-layer-build-configuration]] - HWML build configuration layers

---

## [2026-05-04] analysis | Compiler, Package Manager, and Build System Separation

**Status:** Architecture alignment analysis
**Goal:** Clarify the boundary between compiler, package manager, and build system responsibilities

**Pages Created:**
- [[analysis/compiler-package-manager-build-system-separation]]

**Analysis Focus:**

**User Input:** "It is completely normal to be confused here. You have hit the exact boundary where the responsibilities of a Package Manager, a Build System, and a Compiler collide. In mainstream tools like cargo or npm, these three things are mashed into a single binary. But when you move to an enterprise-grade, deterministic architecture (Buck2/Bazel + Salsa + LSP), you have to strictly separate them."

**Key Finding:** HWML's existing ADRs (ADR-004, ADR-006, ADR-007) already implement this separation correctly. The proposed "fetch phase" + "persistent artifacts" strategy fits perfectly into our existing architecture but clarifies some missing implementation details.

**The Three Responsibilities:**

### 1. Package Manager: Library Downloading (Fetch Phase)

**What it does:** Resolve dependencies, download libraries, populate local cache
**What it NEVER does:** Compile code, type-check, touch network during builds

**Existing Design:**
- ADR-004 (MVS): Defines resolution algorithm
- ADR-006 Layer 1 (`hwml.toml`): Per-library dependencies
- ADR-006 Layer 3 (`hwml.lock`): Exact resolved versions

**Missing (Now Clarified): The Fetch Phase**

```bash
# Phase 1: Fetch (network-touching, non-hermetic)
$ hwml fetch
# Downloads tarballs from registry
# Unpacks to ~/.hwml/registry/std-v1.4.2/
# Generates hwml.lock (if not exists)
# Writes .hwml/resolved-deps.json (path mapping)

# Phase 2: Build (hermetic, no network)
$ hwml build  # OR buck2 build
```

**Two Options:**

**Option A: Native Buck2 Way**
```python
http_archive(
    name = "hwml_std",
    url = "https://hwml.org/packages/std-1.4.2.tar.gz",
    sha256 = "abc123...",
)
```

**Option B: `hwml fetch` Command (Hybrid)**
```bash
$ hwml fetch  # cargo-like UX
# Reads hwml.toml + hwml.lock
# Downloads to ~/.hwml/registry/
# Generates .hwml/resolved-deps.json
```

**Recommendation:** Start with Option B (simpler for users), add Option A for Buck2 power users.

### 2. Compiler: Pure Transformation

**What it does:** Transform source → typed IR → artifacts
**What it NEVER does:** Download libraries, touch network, read arbitrary files

**Existing Design (Already Correct):**

```rust
// From ADR-007
#[salsa::tracked]
pub fn library_interface(
    db: &dyn Db,
    workspace: WorkspaceRoot,
    lib_name: String,
) -> Result<Hwmli, ElabError> {
    // ✅ Takes explicit workspace root
    // ✅ Recursively queries dependencies (pure, memoized)
    // ✅ No network, no ambient state

    let manifest = &workspace_libraries(db, workspace)[&lib_name];
    for dep in &manifest.dependencies {
        library_interface(db, workspace, dep.name.clone())?;
    }
    elaborate_library_with_local_solver(db, workspace, lib_name)
}
```

**Compiler API (Hermetic):**
```bash
$ hwml-compiler \
    --workspace=/abs/path/to/workspace \
    --library=uart \
    --output=uart.hwmli \
    --dep-file=uart.d
```

### 3. Build System: Orchestration & Caching

**What it does:** Schedule builds, deduplicate work, cache artifacts
**What it delegates:** Actual compilation to compiler

**Existing Design:**
- ADR-006 Layer 2 (`hwml-build.toml`): Build config
- Research: Buck2 integration, REapi v2, CAS

**Integration Points:**

**CLI Mode:**
```bash
$ hwml fetch  # Download deps
$ hwml build  # Compile
# Uses local cache: ~/.hwml/cache/
```

**Buck2 Mode:**
```python
hwml_library(
    name = "uart",
    srcs = glob(["*.hwml"]),
    deps = ["//lib/fifo:fifo", "@hwml_std//:lib"],
)
# Buck2 calls compiler with explicit paths
# Uploads .hwmli to remote cache (REapi v2)
```

---

## The LSP Cold-Start Problem (Solved)

**Problem:** Salsa is in-memory. LSP restart → re-elaborate all 50 libraries (30-60s).

**Solution:** Persistent `.hwmli` artifacts + hash-based validation.

**LSP Boot Sequence:**

```rust
fn initialize_workspace(workspace_root: PathBuf) -> HwmlDatabase {
    let db = HwmlDatabase::new();
    let workspace = WorkspaceRoot::new(&db, workspace_root);

    // Load .hwmli artifacts from cache
    for (name, manifest) in workspace_libraries(&db, workspace) {
        let cache_path = hwmli_cache_path(&manifest);

        if let Some(cached) = load_hwmli_if_valid(&manifest, &cache_path) {
            // ✅ CACHE HIT: Deserialize .hwmli into Salsa
            db.set_library_interface_from_cache(name, cached);
        } else {
            // ❌ CACHE MISS: Elaborate from source
            library_interface(&db, workspace.clone(), name)?;
        }
    }
    db
}

fn load_hwmli_if_valid(manifest: &Manifest, cache_path: &Path) -> Option<Hwmli> {
    let cached = read_hwmli(cache_path)?;
    let current_hash = blake3::hash(&concat_files(&manifest.sources));

    if cached.source_hash == current_hash {
        Some(cached)  // ✅ Valid
    } else {
        None  // ❌ Stale
    }
}
```

**Cache Locations:**
```
~/.hwml/cache/
├── objects/ab/cd/abcdef123456...  # .hwmli files
└── index.db  # SQLite: source_hash → path

# Remote (Buck2): REapi v2 action cache
```

**Performance:**

| Scenario | Without Cache | With Cache | Speedup |
|----------|---------------|------------|---------|
| Cold start (50 libs) | 30-60s | 0.5-2s | **15-120x** |
| One file edited | 0.5s (Salsa) | 0.5s | 1x |

**Key Insight:** Cache helps **clean boots**, not incremental edits (Salsa already fast).

---

## Sharing Cache Between CLI, LSP, Buck2

**The Magic:** All use same `.hwmli` format, same cache location.

**Workflow:**

1. **Alice runs CLI:** `hwml build`
   - Elaborates `fifo.hwmli`
   - Saves to `~/.hwml/cache/`
   - Buck2 uploads to remote cache

2. **Bob pulls, opens VS Code:**
   - LSP checks cache: `fifo.hwmli` exists, hash matches
   - **Instant load** (deserialize, no elaboration)

3. **Bob runs Buck2:**
   - Downloads `fifo.hwmli` from remote (built by Alice)
   - **Instant build**

**Cache Key:**
```rust
struct CacheKey {
    source_hash: Blake3Hash,     // All .hwml files
    compiler_version: String,    // "hwml-0.3.0"
    config_hash: Blake3Hash,     // Features, flags
}
```

---

## How This Fits Into Existing Architecture

### ADR-004 (MVS Package Manager) — ✅ No Changes

- MVS runs during **fetch phase**
- Compiler never runs MVS (just reads `hwml.lock`)

### ADR-006 (Multi-Layer Build) — ✅ Minor Additions

**Add section: "Library Fetching and Resolution"**

- Document `hwml fetch` command
- `.hwml/resolved-deps.json` format
- Interaction with Buck2 `http_archive`

### ADR-007 (Salsa-Driven) — ✅ Minor Additions

**Add section: "Persistent Artifact Caching for LSP"**

- Cache structure (`~/.hwml/cache/`)
- LSP boot sequence
- Cache validation (source hash)
- Sharing with Buck2

---

## Implementation Roadmap

### Phase 1: Local Fetch + Local Cache (MVP)

**Components:**
1. `hwml fetch` command (MVS + download + unpack)
2. Local `.hwmli` cache (rkyv serialization)
3. LSP persistent loading

**Success Metrics:**
- `hwml fetch` 50 libs in <10s
- LSP cold start: <2s (vs 30s)
- `hwml build` after `git clean`: <5s

### Phase 2: Remote Cache (Buck2 Integration)

**Components:**
1. REapi v2 client
2. Buck2 rules (`hwml_library()`)
3. Remote cache upload/download

**Success Metrics:**
- Remote cache hit: >90%
- Build time (cached): <1min for 100+ libs

### Phase 3: Persistent Worker Protocol

**Components:**
1. Long-running daemon (Salsa in memory)
2. Buck2 integration (persistent worker protocol)

**Success Metrics:**
- Incremental: <10ms for 1-file change

---

## Answers to Questions

### Q: How to download without violating hermetic builds?

**A:** Separate **fetch phase** (network) from **build phase** (hermetic).

- `hwml fetch` → downloads, generates `.hwml/resolved-deps.json`
- `hwml build` → reads paths, no network

### Q: How to solve LSP cold-start?

**A:** Persistent `.hwmli` artifacts validated by source hash.

- Cache: `~/.hwml/cache/`
- Key: `BLAKE3(sources) + compiler_version`
- LSP deserializes into Salsa inputs

**Result:** 15-120x faster cold start.

### Q: How to share cache between CLI and LSP?

**A:** Same cache directory.

- CLI writes `.hwmli`
- LSP reads `.hwmli`
- Buck2 uploads to remote

### Q: Git repos or tarballs?

**A:** Tarballs primary, Git fallback.

```
https://hwml.org/packages/
├── std-1.4.2.tar.gz  # Primary
├── index.json

[dependencies]
experimental = { git = "...", tag = "v0.1.0" }  # Fallback
```

---

## Summary

**Your proposal is 100% correct and fits perfectly into existing architecture.**

**Key Clarifications:**

1. **Fetch Phase:** Explicitly separate `hwml fetch` from `hwml build`
2. **Persistent Artifacts:** `.hwmli` IS the cache format (already in ADR-009)
3. **LSP Boot:** Deserialize `.hwmli` into Salsa inputs (not bypassing Salsa)
4. **Cache Sharing:** CLI, LSP, Buck2 all use same cache

**No major architecture changes needed.** Just:
- Add `hwml fetch` implementation
- Add cache serialization/deserialization to LSP
- Document separation clearly

**Next Steps:**
1. Add "Fetch Phase" section to ADR-006
2. Add "Persistent Caching" section to ADR-007
3. Implement `hwml fetch` (Phase 1)

**Related:**
- [[decisions/ADR-004-mvs-package-manager]] - MVS algorithm
- [[decisions/ADR-006-multi-layer-build-configuration]] - Build config layers
- [[decisions/ADR-007-salsa-driven-compilation]] - Query architecture
- [[decisions/ADR-009-rkyv-zero-copy-serialization]] - `.hwmli` format
- [[research/buck2-integration-patterns]] - Buck2 best practices
- [[research/build-system-caching-synthesis]] - 3-tier caching

**Notes:**
- 583-line analysis document
- Confirms architectural correctness
- Clarifies missing implementation details
- Provides concrete roadmap

---

## [2026-05-03] research | Hardware compiler artifact taxonomy and build system integration

**Status:** Research complete
**Goal:** Design comprehensive artifact taxonomy for HWML covering all compilation stages from source to bitstream

**Pages Created:**
- [[research/hardware-compiler-artifact-taxonomy]]

**Research Focus:**

**User Question:** "We produce multiple kinds of artifacts (Verilog, TCL, compiled simulators, test results, waveforms, formal verification results). What other artifacts might we produce, and how do we hook this up to incremental compilation and build systems?"

**Key Finding:** Hardware compilation produces a **highly heterogeneous artifact graph** with 11+ distinct artifact types, each requiring different rebuild strategies and caching approaches. Modern build systems (Buck2, Bazel, Shake) provide the primitives needed, but HWML needs a custom integration strategy combining Salsa (in-memory incremental), local CAS (persistent cache), and remote CAS (distributed builds).

**Systems Studied:**

1. **Verilator (Simulation):**
   - Hierarchical builds: Per-module compilation for better caching
   - Dep files: 95% ccache hit rate on small Verilog changes
   - PR #3071: Partition functions by header dependencies
   - PCH issues: Can break ccache (needs tuning)
   - Result: Best-in-class incremental simulation

2. **Yosys + OpenROAD (Synthesis & P&R):**
   - Checkpoint-based flow: Cache each stage independently
   - Bazel integration: rules_hdl provides hermetic builds
   - Canonicalization: Dedup common structures before synthesis
   - OpenROAD stages: Floorplan → Place → CTS → Route → GDS
   - Result: Each stage cached separately in CAS

3. **CIRCT (MLIR for Hardware):**
   - Internal caches: CircuitTargetCache, FieldRefCache, HierPathCache
   - Annotation tracking: Cache target lookups
   - Incremental invalidation: Replace ops without full rebuild
   - Chisel integration: FIRRTL dependency API (unused for caching)
   - Result: Fine-grained caching within compiler passes

4. **Chisel + FIRRTL:**
   - Dependency API: Tracks prerequisites, invalidates, optional prereqs
   - Phase ordering: DependencyManager resolves transform order
   - Incremental discussion: Possible but not implemented
   - Problem: Custom transforms hard to make incremental
   - Result: No built-in incremental compilation

5. **Calyx (Accelerator IR):**
   - Three-section components: Cells, wires, control
   - Group-based execution: Explicit scheduling
   - Primitive libraries: `.futil` + `.sv` pairings
   - Compilation to Verilog: Standard RTL output
   - Result: Clean IR but no caching infrastructure

6. **Buck2 (Meta's build system):**
   - Dynamic dependencies: Read artifact contents to discover deps
   - Dep files: Narrow dependencies to actual usage
   - Remote dep files: Upload to cache for team sharing
   - Deferred materialization: Don't download until needed
   - REapi integration: Action cache + CAS
   - Result: Production-grade distributed caching

7. **Bazel (Google's build system):**
   - Hermetic builds: Everything explicit (no hidden dependencies)
   - Custom rules: Hardware-specific (synthesize_rtl, place_and_route)
   - Hierarchical builds: Module-level granularity
   - Remote execution: Offload heavy synthesis to cloud
   - rules_hdl: ASIC/FPGA synthesis integration
   - Result: Industry standard for large-scale builds

8. **Shake (Haskell build system):**
   - Monadic dependencies: Discover deps *after* running rules
   - Oracles: Non-file dependencies (tool versions, configs)
   - Polymorphic dependencies: Depend on anything with a hash
   - Example: Read dep file, then `need` additional deps
   - Result: Most flexible dependency model

9. **Waveform Formats:**
   - VCD: ASCII, slow, huge (1-10GB for 10ms @ 100MHz)
   - FST: Binary, fast, compressed (100-500MB, 10x smaller)
   - EVCD: Extended VCD (9-state), same issues as VCD
   - GHW: GHDL-specific, binary, fast
   - Conversion: VCD ↔ FST (lossless)
   - Result: FST is best default (GTKWave native)

10. **Formal Verification:**
    - SVA properties: SystemVerilog assertions
    - Proof caching: Cache successful proofs by source hash
    - Unsat cores: Reuse for similar queries
    - SymbiYosys: Yosys + SMT solvers (Z3, Yices)
    - Cache invalidation: Source or property change
    - Result: Proof caching critical for large designs

11. **UPF (Power Intent):**
    - Power domains: Voltage islands, gating strategies
    - Tool flow: RTL+UPF → Synthesis → P&R → Signoff
    - Hierarchical UPF: Per-module + top-level integration
    - Auto-insertion: Isolation cells, level shifters, retention
    - Result: Generate from HWML annotations

**Artifact Taxonomy (11 Types):**

### 1. Elaboration Artifacts
- `.hwmli`: Binary IR (content-addressable, BLAKE3)
- Dep graph: Embedded in `.hwmli`
- Logs: Timestamp-based (ephemeral)

### 2. Verilog Generation
- `.sv` files: Content-addressable
- Module hierarchy: JSON metadata
- Rebuild: On `.hwmli` or config change

### 3. UPF (Power Intent)
- UPF constraints: TCL/UPF format
- Power domain hierarchy: Generated from annotations
- Rebuild: On power annotation or template change

### 4. TCL Scripts
- Synthesis TCL: Template + config hash
- SDC (clock constraints): Content-addressable
- Floorplan/P&R: Tool-specific configuration

### 5. Simulation Artifacts
- Compiled simulator: C++/SystemC binary (~100MB)
- Dep files: Narrow C++ dependencies (ccache 95% hit)
- Test results: JSON (cached in CAS)
- Coverage DB: Binary (cached)
- Waveforms: VCD/FST (ephemeral, not cached)

### 6. Synthesis Artifacts
- Gate netlist: Verilog (~10MB, cached)
- Timing reports: Text (~5MB, cached)
- Area/power reports: JSON (~1MB, cached)
- Checkpoints: Tool binary (~50MB, cached)

### 7. Place & Route Artifacts
- Placed design: DEF (~50MB, cached)
- Routed design: DEF (~100MB, cached)
- GDS layout: GDSII (~500MB, cached)
- Checkpoints: Each stage cached independently

### 8. Formal Verification
- SVA properties: SystemVerilog (cached)
- Proof results: JSON (cached if proven)
- Counterexamples: VCD (optional cache)
- Unsat cores: Reused for incremental proofs

### 9. Waveforms
- VCD: ASCII, slow, huge (don't cache)
- FST: Binary, fast, 10x smaller (optional cache)
- GTKWave: Universal viewer

### 10. Test Results
- JUnit XML: Test pass/fail (cached)
- Coverage: LCOV format (cached)
- Performance metrics: JSON (cached)
- Logs: Ephemeral (not cached)

### 11. FPGA Bitstreams
- .bit file: Binary (~10MB, cached)
- .bin/.mcs: Flash formats (cached)
- Metadata: JSON (embedded in CAS)

**Build System Integration Strategies:**

**1. Buck2 Approach:**
```python
# Dynamic dependencies
def _generate_verilog(ctx):
    def _codegen(ctx, artifacts, outputs):
        metadata = artifacts[hwmli].read_json()
        for dep in metadata["dependencies"]:
            artifacts.require(dep)  # Discover deps dynamically
        # ... generate Verilog
    return ctx.actions.dynamic_output(f=_codegen)

# Dep files
ctx.actions.run(
    ["verilator", "--cc", verilog],
    dep_files={"verilator_deps": depfile},
)
```

**2. Bazel Approach:**
```python
# Hermetic hardware rules
synthesize_rtl(
    name = "uart_synth",
    top_module = "uart",
    deps = [":verilog_uart"],
    toolchain = "@hwml//:compiler_v1.0",
)

# Hierarchical Verilator builds
verilator_hierarchical_cc_library(
    name = "uart_module",
    srcs = ["uart.sv"],
)
```

**3. Shake Approach:**
```haskell
-- Monadic dependencies
"*.hwmli" %> \out -> do
    let src = out -<.> "hwml"
    need [src]
    -- Parse to discover dependencies
    imports <- parseImports src
    need [imp <.> "hwmli" | imp <- imports]
    -- Elaborate
    cmd "hwml-elaborate" [src] ["-o", out]

-- Oracles (non-file deps)
addOracle $ \(ToolVersion tool) -> do
    Stdout ver <- cmd tool ["--version"]
    return (trim ver)
```

**4. Salsa + CAS Approach (HWML):**
```rust
// In-memory incremental (Salsa)
#[salsa::tracked]
fn elaborate_library(db: &dyn HwmlDb, source: SourceFile) -> Library;

// Persistent cache (CAS)
#[salsa::tracked]
fn synthesize_verilog(
    db: &dyn HwmlDb,
    verilog: VerilogArtifact,
) -> NetlistArtifact {
    let key = blake3::hash([verilog.hash(), tool_version().hash()]);
    if let Some(cached) = db.cas().get(key) {
        return cached;
    }
    let netlist = run_yosys(verilog);
    db.cas().put(key, netlist.clone());
    netlist
}
```

**Dependency Types:**

| Type | Example | Detection | Rebuild Strategy |
|------|---------|-----------|------------------|
| File content | `.hwml` source | BLAKE3 hash | Content change |
| Interface | `.hwmli` exports | Early cutoff hash | Public API change only |
| Configuration | Synthesis flags | Config hash | Config change |
| Tool version | Verilator 5.x | Version query | Version change |
| PDK/Library | ASAP7 v1.2 | Library hash | Library change |
| Discovered | `#include` | Dep file | Actual usage |
| Time-based | Logs | Timestamp | Always regenerate |

**HWML Implementation Plan:**

**Phase 1: Salsa + Local CAS (MVP)**
- Salsa queries for elaboration + Verilog gen
- Local CAS (`~/.hwml/cache/`)
- Artifacts: `.hwmli`, Verilog, test results
- Target: 10x speedup on incremental builds

**Phase 2: Remote CAS + Dep Files**
- REapi v2 integration (Buck2-compatible)
- Verilator with dep files
- Simulator caching with ccache
- Target: 90%+ remote cache hit rate

**Phase 3: Full Pipeline**
- Synthesis (Yosys) with caching
- P&R (OpenROAD) with checkpoint caching
- Formal verification proof caching
- FPGA bitstream generation
- Target: <10min full ASIC flow (with cache)

**Caching Strategy:**

**Cache Everything:**
- `.hwmli` (elaborated IR)
- Verilog (generated RTL)
- Test results (pass/fail, coverage)
- Synthesis netlists
- P&R checkpoints
- Formal proofs (if proven)
- Bitstreams

**Don't Cache:**
- Waveforms (too large, regenerate on demand)
- Logs (ephemeral)
- Failed proofs (may succeed with more resources)

**Selective Cache:**
- FST waveforms (optional, for CI debugging)
- Counterexamples (optional, for regression tests)

**Full Pipeline:**
```
SOURCE (.hwml)
    ↓ [Salsa: elaborate_library]
ELABORATED IR (.hwmli)  ← CAS cache
    ↓ [Salsa: generate_verilog]
VERILOG (.sv)  ← CAS cache
    ↓
    ┌─────────┴─────────┐
    ↓                   ↓
SIMULATION         SYNTHESIS
    ↓                   ↓
[Verilator]        [Yosys]
    ↓                   ↓
SIMULATOR          NETLIST  ← CAS
    ↓                   ↓
TEST RESULTS ← CAS  [OpenROAD]
COVERAGE ← CAS          ↓
WAVEFORMS ✗ NO     GDS  ← CAS
                        ↓
                   BITSTREAM ← CAS
```

**Key Insights:**

1. **Heterogeneous artifacts require heterogeneous strategies**
   - Salsa: In-memory incremental (fast iteration)
   - Local CAS: Persistent cache (clean builds)
   - Remote CAS: Distributed builds (CI, team sharing)

2. **Don't cache everything blindly**
   - Waveforms: 1-10GB, regenerate on demand
   - Test results: 1MB, always cache
   - Synthesis: 10-100MB, always cache

3. **Dep files are critical for external tools**
   - Verilator: 95% ccache hit rate
   - Narrow dependencies to actual usage
   - Remote dep files for team sharing

4. **Checkpoint caching enables fast iteration**
   - P&R stages: Floorplan → Place → CTS → Route
   - Each stage cached independently
   - Change floorplan → skip re-synthesis

5. **Salsa + CAS is the right architecture**
   - Salsa: Pure Rust, incremental queries
   - CAS: External tools, content-addressable
   - Hybrid: Best of both worlds

**Comparison:**

| System | Incremental | Caching | Remote | Dep Files | Dynamic Deps |
|--------|-------------|---------|--------|-----------|--------------|
| Chisel/FIRRTL | ❌ | ❌ | ❌ | ❌ | ⚠️ API only |
| Verilator | ✅ Hierarchical | ✅ ccache | ❌ | ✅ 95% hit | ❌ |
| Bazel | ✅ | ✅ CAS | ✅ REapi | ✅ | ❌ |
| Buck2 | ✅ | ✅ CAS | ✅ REapi | ✅ | ✅ |
| Shake | ✅ | ⚠️ Manual | ❌ | ✅ | ✅ Monadic |
| **HWML** | ✅ Salsa | ✅ CAS | ✅ REapi | ✅ Planned | ✅ Salsa |

**Related:**
- [[research/build-system-caching-synthesis]] - 3-tier caching architecture
- [[research/content-addressable-storage-systems]] - BLAKE3, CAS design
- [[research/dependent-types-object-file-formats]] - `.hwmli` format
- [[decisions/ADR-006-multi-layer-build-configuration]] - Build system

**Notes:**
- Comprehensive 1300-line research document
- Covers 11 artifact types (elaboration → bitstream)
- Analyzes 8 build systems and hardware tools
- Detailed implementation roadmap (3 phases)
- Integration strategies for Salsa + CAS + REapi

---

## [2026-05-03] research | Object file formats for dependent types

**Status:** Research complete
**Goal:** Investigate serialization strategies for dependent type systems, focusing on type interning and `.hwmli` format design

**Pages Created:**
- [[research/dependent-types-object-file-formats]]

**Research Focus:**

**Question from user:** HWML is dependently typed - András Kovács says in smalltt that interning, especially for types, has limited value. Should `.hwmli` intern types? How should we design the object file format where types are values?

**Key Finding:** In dependent type systems, aggressive type interning provides minimal benefit due to:
1. **Unique types**: Most types are computed from different contexts (low duplication)
2. **Hash table overhead**: Lookup cost dominates small savings
3. **Exponential blowup**: Type-level computation can explode size despite interning
4. **Implementation complexity**: GC, incremental updates, concurrency all complicated

**Systems Studied:**

1. **smalltt (András Kovács)**:
   - Explicit anti-interning stance in README
   - "Hash consing overhead > benefits for dependent types"
   - Direct tree representation, lazy evaluation, no global tables
   - Result: Competitive with Lean/Agda despite no interning

2. **Lean 4 (.olean files)**:
   - Compact regions: serialized heap with contiguous layout
   - `mmap()` for zero-copy loading (deterministic addresses)
   - Post-order traversal for reproducible serialization
   - Interns: strings, names, constants (but NOT types/values)

3. **Agda (.agdai files)**:
   - Structure sharing via explicit memoization tables
   - Interns: strings, names, integers, AST nodes
   - ~50-70% space savings from sharing
   - Overhead: hashtable lookups during serialization

4. **Coq (.vo files)**:
   - OCaml Marshal (automatic serialization)
   - Implicit sharing via runtime
   - Pain: version brittleness (any type change breaks format)
   - Segmented format (summary, library, opaques, tasks)

5. **Idris**:
   - Idris 1: JSON (portable, slow, large)
   - Idris 2: Binary format (Lean-inspired)

**What to Intern (Recommendation for HWML):**

✅ **DO intern:**
1. **Strings** (names, literals)
   - High duplication (names reused constantly)
   - Fast lookup (small keys)
   - Universal practice (Lean, Agda, Coq, smalltt all do this)
   - ~60-80% memory reduction for name storage

2. **Qualified names** (module paths)
   - `std::Vec::new` → intern("std::Vec") + intern("new")
   - Fast equality (u32 comparison vs string comparison)
   - Compact representation (4 bytes vs ~40 bytes)

3. **Global constants** (top-level definitions)
   - High reuse (every use of `std::Vec` references same constant)
   - Small table (thousands, not millions)
   - Fixed after elaboration (immutable)

❌ **DO NOT intern:**
1. **Types** (follows Kovács' advice)
   - Most types unique (computed from context)
   - Overhead > benefit
   - Complexity not worth it

2. **Values** (closures, computed values)
   - Similar to types (unique contexts)
   - Runtime representation issues

3. **Elaborated expressions** (except optional structure sharing)
   - Direct tree representation simpler
   - Structure sharing can be added later if profiling shows benefit

**HWML `.hwmli` Format Design:**

```rust
pub struct Hwmli {
    // Header
    version: u32,
    hwml_compiler_hash: Blake3Hash,

    // Interning tables
    strings: StringTable,
    qnames: QNameTable,

    // Library metadata
    library_name: QName,
    dependencies: Vec<Dependency>,

    // Declarations (not interned - direct trees)
    declarations: Vec<Declaration>,

    // Early cutoff (Phase 4)
    export_interface_hash: Blake3Hash,
    declaration_fingerprints: HashMap<DeclId, Blake3Hash>,
    usage_map: HashMap<QName, HashSet<DeclId>>,
}

pub enum Expr {
    Var(DeBruijnIndex),
    Global(ConstId),  // ← Interned constant reference
    App(Box<Expr>, Box<Expr>),
    Lam(QName, Box<Expr>, Box<Expr>),
    Pi(QName, Box<Expr>, Box<Expr>),
    // ... NOT interned (direct tree)
}
```

**Binary Encoding (MessagePack-like):**
- Tag system for compact representation
- Variable-length integers
- String references (interned)
- Optional structure sharing during serialization
- Estimated: ~10-15 bytes for small lambda (vs 115 bytes JSON)

**Implementation Phases:**

1. **Phase 1 (MVP)**: String/QName interning, binary serialization, no structure sharing
   - Simple, debuggable
   - ~500-1000 lines of code
   - Success: .hwmli <5x source size, deserialize <100ms

2. **Phase 2 (Optional)**: Structure sharing during serialization
   - Only if profiling shows >30% duplication
   - HashMap-based sharing detection
   - ~30% file size reduction

3. **Phase 3 (Future)**: Compact regions (Lean-style)
   - Only if loading time becomes bottleneck
   - Requires pointer → offset conversion
   - Probably not needed for <100kloc projects

**Key Insights:**

1. **Types are values in HWML** → One serialization strategy for both
2. **Kovács is right** → Don't intern types/values (overhead > benefit)
3. **Strings are special** → Interning names is universally beneficial
4. **Lean's approach is pragmatic** → Intern identifiers, serialize values directly
5. **Keep it simple** → Add complexity only when measurements prove need

**Comparison Table:**

| System | Strings | Names | Types | Values | AST | Rationale |
|--------|---------|-------|-------|--------|-----|-----------|
| Lean 4 | ✅ | ✅ | ❌ | ❌ | ❌ | Compact region |
| Agda | ✅ | ✅ | ✅ | ✅ | ✅ | Full sharing |
| Coq | ✅ | ✅ | Auto | Auto | Auto | OCaml Marshal |
| smalltt | ✅ | ✅ | ❌ | ❌ | ❌ | Anti-interning |
| **HWML** | ✅ | ✅ | ❌ | ❌ | ⚠️* | Follow Kovács |

*⚠️ Optional structure sharing during serialization only (not in-memory)

**Related:**
- [[research/content-addressable-storage-systems]] - BLAKE3 hashing for .hwmli
- [[research/build-system-caching-synthesis]] - CAS integration
- [[decisions/ADR-006-multi-layer-build-configuration]] - Build system architecture

**Notes:**
- Comprehensive 770-line research document
- Covers all major dependent type systems
- Clear recommendations backed by theory and practice
- Implementation plan with 3 phases

---

## [2026-05-03] research | Content-addressable storage and build system caching

**Status:** Research complete
**Goal:** Comprehensive investigation of CAS, build databases, and persistent stores for modern build systems

**Pages Created:**
- [[research/content-addressable-storage-systems]]
- [[research/build-system-caching-synthesis]]

**Research Areas:**

1. **Content-Addressable Storage (CAS) Systems:**
   - Git object store (SHA-1, moving to SHA-256, loose objects + packfiles)
   - Nix store (input-addressed + RFC 0062 content-addressed experimental)
   - Bazel/Buck2 REapi v2 (Action Cache + CAS separation, SHA-256)
   - IPFS (CIDv1, multihash, content-defined chunking, Bitswap)

2. **Hash Functions for Build Systems:**
   - Comparison: MD5 (broken), SHA-1 (deprecated), SHA-256 (standard), BLAKE2b, BLAKE3
   - **BLAKE3 chosen**: 10x faster than SHA-256 (10+ GB/s), parallel, secure
   - Incremental hashing, SIMD optimization (SSE2, AVX2, AVX-512, NEON)
   - Rust `blake3` crate + C reference implementation

3. **Storage Strategies:**
   - **Sharding**: First 2 hex chars = directory (256 dirs, ~4K files/dir for 1M artifacts)
   - **Hardlinking**: Zero-copy materialization (same filesystem requirement)
   - **Three-tier caching**: Local build dir → User-global CAS → Remote shared cache
   - **Garbage collection**: LRU with size limit + recency protection

4. **Buck2's DICE (Deterministic Incremental Computation Engine):**
   - In-process incremental computation (like Salsa)
   - Dynamic dependencies, parallel evaluation, deduplication
   - Early cutoff: If value unchanged, skip downstream
   - Integration with CAS: DICE (hot cache) + CAS (cold cache)

5. **Salsa (Rust Analyzer's incremental framework):**
   - Tracked structs/functions with memoization
   - Revision-based invalidation
   - Durability system: volatile vs durable inputs (optimize for std lib)
   - Version vector for fine-grained checks

6. **Build System Databases:**
   - **Ninja**: `.ninja_log` (build history, command hashes), `.ninja_deps` (implicit deps, binary)
   - **Shake**: `.shake.database` (persistent traces, profiling data), Cloud Shake (experimental)
   - **Buck2/Bazel**: Rebuild graph in-memory, rely on remote CAS for persistence

7. **Academic Foundations:**
   - **"Build Systems à la Carte" (Mokhov et al., ICFP 2018)**: Systematic framework, scheduling vs rebuilding axes
   - **"A Sound and Optimal Incremental Build System" (Erdweg et al., OOPSLA 2015)**: Pluto system, dynamic deps, soundness + optimality proofs
   - **Persistent build information**: Mtimes (Make), traces (Shake), hashes (Bazel/Buck2)

8. **Early Cutoff (Critical Optimization):**
   - GHC's per-declaration fingerprints + usage tracking
   - Detects unchanged outputs despite changed inputs
   - Can reduce rebuilds by 10-100x for typical edits
   - **For HWML**: Store declaration fingerprints in `.hwmli`, track which decls were used

9. **Remote Execution API v2:**
   - Protocol: gRPC-based, Action → Command + Input Root
   - Content-Addressable Storage: FindMissingBlobs, BatchUpdate/ReadBlobs
   - Action Cache: Maps action hash → result (early cutoff at action level)
   - Implementations: BuildBuddy, Buildbarn, Google RBE, EngFlow

10. **HWML-Specific Recommendations:**
    - **Hash function**: BLAKE3 (primary), SHA-256 (REapi compat)
    - **Storage tiers**: `.hwml-build/` → `~/.cache/hwml/cas/` → Remote REapi
    - **In-process**: Salsa for LSP + incremental elaboration
    - **Persistent**: CAS for `.hwmli` artifacts across builds
    - **Early cutoff**: Per-declaration fingerprints (Phase 4)
    - **Remote exec**: REapi v2 for parallel elaboration (Phase 5)

**Key Insights:**

1. **Hybrid is optimal**: Combine in-process (Salsa/DICE) with persistent (CAS)
   - Salsa: Fast within-build, LSP responsiveness
   - CAS: Persist across builds, remote sharing

2. **BLAKE3 is the future**: 10x faster than SHA-256, widely adopted for new systems
   - Dropbox, 1Password, emerging build systems
   - Standardized Rust + C implementations

3. **Early cutoff is critical**: Can skip 90%+ of rebuilds
   - GHC model: per-declaration fingerprints + usage tracking
   - Phase 4 priority for HWML

4. **Three-tier caching**: Local → User-global → Remote
   - Hardlink for zero-copy (Tier 1 ↔ Tier 2)
   - REapi v2 for team-wide sharing (Tier 3)

5. **Content-addressing vs Input-addressing trade-off**:
   - Input: Easier build systems (know paths before building)
   - Content: Better dedup, early cutoff, unprivileged copying
   - **HWML**: Input-addressed paths + content-addressed CAS (best of both)

**Implementation Phases:**

1. **Phase 1 (Months 1-2)**: Local CAS (BLAKE3, Tier 1+2, hardlink, basic GC)
2. **Phase 2 (Months 2-3)**: Salsa integration (LSP, durability, tracked functions)
3. **Phase 3 (Months 4-5)**: Early cutoff (per-decl fingerprints, usage tracking)
4. **Phase 4 (Months 6-7)**: Remote cache (REapi v2, BuildBuddy/Buildbarn)
5. **Phase 5 (Months 8-10)**: Remote execution (parallel elaboration, hermetic actions)

**Related:**
- [[decisions/ADR-006-multi-layer-build-configuration]] - Build configuration architecture
- [[research/incremental-compilation-synthesis]] - Overall incremental strategy
- [[research/modern-build-systems]] - Build system comparison

**Notes:**
- Two comprehensive research documents created (802 + 900 lines)
- Covers everything from Git's object store to REapi v2 protocol
- Concrete recommendations with Rust code examples
- Clear implementation roadmap with success metrics

---

## [2026-05-03] decision | Multi-layer build configuration (ADR-006)

**Status:** ADR created and reconciled with existing design
**Goal:** Define separation between library manifests, build configuration, and lock files

**Pages Created:**
- [[decisions/ADR-006-multi-layer-build-configuration]]
- [[analysis/ADR-006-vs-package-manager-design-reconciliation]]

**Key Decisions:**
1. **Three-layer architecture:**
   - Layer 1: Library manifest (`hwml.toml`) - dependencies, features, metadata
   - Layer 2: Build/workspace config (`hwml-workspace.toml`, `builds/*.toml`) - targets, optimization, caching
   - Layer 3: Lock file (`hwml.lock`) - exact resolved versions

2. **Manifest schema standardized:**
   - Use `[package]` (not `[library]`) for consistency with Cargo/npm
   - Added `[sources]` for elaboration order control
   - Added `[lib]` and `[[bin]]` sections to distinguish library from testbenches
   - Features system for conditional compilation

3. **Build configuration separation:**
   - Build settings (target, optimization, cache) separate from library metadata
   - Multiple build configs from same codebase (FPGA, ASIC, simulation)
   - Build profiles (dev, release, ci)
   - LSP build discovery via `.hwml/active-build.toml`

4. **`hwml-workspace` crate design:**
   - Manifest parsing, dependency graph, topological sort
   - No dependency on `hwml-core` or `hwml-elab`
   - Integration points for LSP and CLI

5. **Buck2/Nix integration:**
   - Generator tools: `hwml generate buck`, `hwml generate nix`
   - `hwml.toml` as source of truth
   - External build systems orchestrate compilation

6. **Implementation phases:**
   - Phase 1: Basic workspace + multi-file
   - Phase 2: User-global CAS cache
   - Phase 3: Package manager + MVS
   - Phase 4: Build configuration layer
   - Phase 5: Remote cache + early cutoff
   - Phase 6: Buck2/Nix integration

**Reconciliation:**
- Compared ADR-006 with `design/package-manager.md`
- Added missing sections: `[sources]`, `[lib]`, `[[bin]]`
- Standardized terminology: `[package]` vs `[library]`
- Clarified cache config location (build files, not library manifests)
- Added `hwml-workspace` crate API design

**Related:**
- [[decisions/ADR-004-mvs-package-manager]] - MVS algorithm
- [[research/incremental-compilation-synthesis]] - Caching and remote execution
- [[research/modern-build-systems]] - Buck2, Nix, Bazel

**Notes:**
- ADR-006 supersedes the implicit workspace model in `design/package-manager.md`
- Both documents are now aligned; ADR-006 is canonical specification
- Future ADRs (007-009) renumbered to accommodate ADR-006

---

## [2026-05-02] bootstrap | Wiki initialization

**Status:** Starting bootstrap process
**Goal:** Process key design documents and establish wiki structure
**Structure:** Created directory layout per WIKI.md schema
**Directories:** entities/, decisions/, components/, research/, onboarding/, synthesis/

## [2026-05-02] ingest | ARCHITECTURE.md

**Sources:** `design/ARCHITECTURE.md`
**Pages Created:**
- [[decisions/ADR-001-lcf-kernel]]
- [[decisions/ADR-002-bidirectional-typing]]
- [[decisions/ADR-003-async-elaboration]]
- [[entities/lcf-pattern]]
- [[entities/bidirectional-typing]]
- [[entities/nbe]]
- [[components/kernel]]
- [[components/elaborator]]

**Notes:** Extracted core architectural decisions and type system concepts

## [2026-05-02] ingest | package-manager.md

**Sources:** `design/package-manager.md`
**Pages Created:**
- [[decisions/ADR-004-mvs-package-manager]]
- [[decisions/ADR-005-content-addressed-artifacts]]
- [[decisions/ADR-006-hwmli-format]]
- [[entities/mvs]]
- [[entities/content-addressed-storage]]
- [[entities/salsa]]
- [[components/package-manager]]
- [[research/go-mvs]]
- [[research/ghc-compilation]]

**Notes:** Multi-faceted document covering library system and compilation cache

## [2026-05-02] create | overview.md

**Sources:** Multiple (README.md, ARCHITECTURE.md, hwml.md)
**Pages Created:**
- [[overview]]

**Notes:** High-level synthesis of HWML project purpose and architecture

## [2026-05-02] create | ADR-002-bidirectional-typing

**Sources:** `design/ARCHITECTURE.md`, bidirectional typing research
**Pages Created:**
- [[decisions/ADR-002-bidirectional-typing]]

**Notes:** Documented choice of bidirectional type checking, integration with kernel

## [2026-05-02] create | index and status

**Pages Created:**
- [[index]] - Catalog of all pages with ingestion status
- [[BOOTSTRAP-STATUS]] - Progress report and next steps

**Notes:** Bootstrap phase complete - foundation established with ~10% of documents processed

---

## Bootstrap Summary (2026-05-02)

**Completed:**
- ✅ Directory structure created
- ✅ Core foundation pages (overview, index, log, status)
- ✅ 3 ADRs created (001, 002, 004)
- ✅ 1 entity page (nbe)
- ✅ 4 source documents fully processed
- ✅ Cross-references established
- ✅ Ready for queries and continued ingestion

**Status:** Foundation is solid. Can proceed with:
1. Completing core type system docs (high priority)
2. Creating component pages
3. Generating onboarding guides
4. Full batch ingestion of remaining docs


## [2026-05-02] research | Debug Information Systems

**Type:** Original research request
**Sources:** Web research (DWARF, LLVM, Rust, GHC) + codebase exploration
**Pages Created:**
- [[research/debug-info-systems]]

**Notes:** Comprehensive survey of debug information representation beyond simple source locations, covering DWARF, PDB, source maps, LLVM's approach, and implications for HWML's two-level type theory and dependent types. Includes analysis of current HWML infrastructure and recommendations for implementation phases.

---

## [2026-05-03] research | Hardware Debug Information

**Type:** Follow-up research request
**Sources:** Web research (VCS, Verdi, FSDB, Chisel/FIRRTL, synthesis tools)
**Pages Created:**
- [[research/hardware-debug-info]]

**Notes:** Deep dive into hardware-specific debug information systems. Covers waveform formats (VCD, FSDB), VCS/Verdi toolchain, Chisel source locators, synthesis debug (SynAlign, FPGA tools), and IDE integration (DVT). Provides concrete recommendations for HWML's dual debug strategy: DWARF for elaboration, source locators + waveforms for generated hardware.

---

## [2026-05-03] research | LLVM Debug Info Internals

**Type:** Follow-up research request
**Sources:** Web research (LLVM docs, GitHub issues, source code)
**Pages Created:**
- [[research/llvm-debug-info-internals]]

**Notes:** Comprehensive deep dive into LLVM's internal debug information mechanisms. Covers the three representations (IR metadata/debug records, SelectionDAG SDDbgValue, MachineInstr DBG_VALUE), preservation through optimization (salvaging, assignment tracking, debug info invariance), backend consumption (LiveDebugValues, instruction referencing, DWARF generation), and handling optimized-away variables. Includes best practices for pass writers and implications for HWML's elaborator (NbE preservation, metavariable tracking, dual debug strategy).

---

## [2026-05-03] research | Modern Debug Information Research

**Type:** Follow-up research request
**Sources:** Academic papers (PLDI 2020, ASPLOS 2023, Onward! 2024, arXiv 2024)
**Pages Created:**
- [[research/debug-info-research-modern]]

**Notes:** Survey of cutting-edge academic research on debug information (2020-2024). Key findings: debug info correctness is an **ill-posed problem** with no unique right answer, only trade-offs between density/height/fidelity. Covers CCMD (debug info shouldn't affect optimization), completeness metrics (liveness-based coverage), validation frameworks (actionable program transformation), and the state mapping framework. Identifies that current compilers have 60-70% variable visibility at -O2 with hundreds of DWARF bugs. Provides concrete implications for HWML: embrace ill-posed nature, measure completeness, test invariance, use residual computation for dependent types, and maintain dual debug strategy for elaboration vs hardware.

---

## [2026-05-03] decision | ADR-005: Debug Information Strategy

**Type:** Architecture Decision Record
**Sources:** Four research pages + existing ADRs
**Pages Created:**
- [[decisions/ADR-005-debug-information]]

**Notes:** Comprehensive ADR for HWML's debug information strategy based on extensive research. Adopts **dual debug strategy**: (1) Meta-level - SourceInfo metadata, metavariable tracking, residual computation, NbE preservation, three debug views (accurate/complete/balanced); (2) Object-level - Chisel-style source locators in Verilog, VCD/FSDB waveform generation, hierarchy preservation, bidirectional source mapping. Embraces ill-posed nature of debug info (no perfect answer), requires debug info invariance (CCMD), implements liveness-based quality metrics, and provides incremental implementation plan across 4 phases. Decision backed by PLDI, ASPLOS, Onward! research plus LLVM implementation and hardware debugging best practices (Chisel, VCS, Verdi).

---

## [2026-05-03] research | Elaboration Error Messages

**Type:** Research on error message quality in type inference systems
**Sources:** Academic papers (SHErrLoc, Flow-based errors POPL 2024), Rust/GHC/Lean/Agda implementations
**Pages Created:**
- [[research/elaboration-error-messages]]

**Notes:** Deep dive into how modern type systems produce high-quality error messages. **Key finding**: Metavariable origin tracking is NOT optional debug info—it's ESSENTIAL error reporting infrastructure. Research shows all modern systems (Rust, Lean 4, GHC, Agda) extensively track: (1) **Constraint origins** - WHY each constraint was created, not just WHAT; (2) **Metavar provenance** - WHERE/WHY each metavariable was introduced; (3) **Global diagnosis** - Analyze entire constraint graph to find real error source (not first failure point); (4) **Data flow explanations** - Users understand "value flows from X to Y" better than abstract type mismatches. Critical insight for HWML: `created_at`, `created_by`, `constrained_by` metadata should ALWAYS be present (even in production), as they're needed for basic error messages. Only advanced traces (unification steps, NbE residuals) should be optional `--debug=full` features. Includes comparative analysis of 7 type systems and best practices from 15+ years of research.

---

## [2026-05-03] update | ADR-005 Updated with Error Reporting Distinction

**Type:** Major clarification to existing ADR
**Pages Modified:**
- [[decisions/ADR-005-debug-information]]

**Notes:** Updated ADR-005 to reflect critical research finding: metavariable/constraint tracking is NOT "debug information" but rather **essential error reporting infrastructure**. Added clear distinction between: (1) **Error Reporting Infrastructure** (always present) - constraint origins, metavar provenance, source locations; needed for usable error messages when compilation fails; (2) **Optional Debug Information** (controlled by flags) - unification traces, NbE residuals, DWARF, waveforms; needed when debugging compiled output. Updated strategy diagram to show three tiers instead of two. Added new section on "Constraint Collection & Global Diagnosis" based on SHErrLoc research. Emphasized that this matches industry practice (Rust's `ObligationCause` always present, DWARF optional). Critical for implementation: Phase 1 must include constraint/metavar provenance as core feature, not optional debug mode.

## [2026-05-03] ingest | extensible-elaborator paper

**Sources:** `external/extensible-elaborator/paper/main.md`
**Pages Created:**
- [[research/extensible-elaborator]]

**Notes:** Comprehensive ingestion of ExEl paper on constraint-based extensible elaborators. Highly relevant to HWML's elaborator design - proposes modular architecture with pluggable constraint solvers instead of monolithic unifiers. Includes detailed case studies (type classes, implicit arguments, Pi-injectivity) and comparison to Agda/Idris/Lean/Coq. Document includes HWML-specific discussion on potential adoption and hardware-domain plugins.

## [2026-05-03] ingest | Tog⁺ heterogeneous unification

**Sources:** `external/togt/` (prototype), PhD thesis, research papers
**Pages Created:**
- [[research/togt-heterogeneous-unification]]

**Notes:** Ingestion of Tog⁺ research on heterogeneous unification using twin types for dependent type checking. Addresses the "spine problem" by allowing term unification before types are proven equal. Includes performance benchmarks, comparison to Agda/Coq/Idris/Lean, theoretical foundations, and HWML-specific discussion on integration with ExEl architecture. Referenced by ExEl paper regarding anti-unification approaches.

## [2026-05-03] ingest | Jon Sterling on unification/coercion

**Sources:** [jonmsterling.com/01JQ](https://www.jonmsterling.com/01JQ/) (blog post)
**Pages Created:**
- [[research/disentangling-unification-coercion]]

**Notes:** Ingestion of Jon Sterling's proposal for handling unification and implicit coercion in dependent type theory via explicit `cast` markers. Addresses fundamental tension between these features - argues fully implicit combination is inherently unreliable due to order-sensitivity. Proposes using reliable Kovács-style unification plus explicit casts for user-controlled coercion. Highly relevant to HWML elaborator design, especially for hardware type coercions. Complementary to ExEl (architecture) and Tog⁺ (unification technique).

## [2026-05-03] research | McBride's crude but effective stratification

**Sources:** McBride's Epilogue blog (2011-2012), Jon Sterling's blog (2025), Favonia et al. POPL 2023 paper
**Pages Created:**
- [[research/crude-but-effective-stratification]]

**Notes:** Research into Conor McBride's "crude but effective stratification" proposal for lightweight universe polymorphism. Core idea: define everything at lowest universe level, then use displacement operations to shift entire signature upward as needed. Formalized by Favonia, Angiuli, and Mullanix using displacement algebras. Provides middle ground between Set:Set hack (inconsistent) and explicit universe levels everywhere (verbose). Highly relevant to HWML as hardware naturally has hierarchical type structure. Mentioned in Sterling's Pterodactyl blog as potential future feature.

## [2026-05-03] decision | Universe polymorphism strategy (ADR-003)

**Type:** Architecture Decision Record
**Pages Created:**
- [[decisions/ADR-003-universe-polymorphism]]

**Notes:** Created ADR capturing decision on universe polymorphism approach for HWML. Proposes phased strategy: Phase 1 uses Agda-style explicit levels (proven, safe, straightforward to implement), Phase 2 evaluates McBride's crude but effective stratification based on empirical evidence of pain points. Decision driven by need for soundness (predicative type theory) balanced with usability (hardware engineers shouldn't need deep type theory knowledge). Includes detailed comparison of 4 options, success metrics, and implementation notes for both phases. Related to ADR-001 (kernel architecture) and ADR-002 (bidirectional typing).

---

## [2026-05-03] MAJOR RESEARCH | Incremental Compilation and Build Systems

**Type:** Comprehensive research project
**Duration:** 2026-05-03 (full day, expansive web + academic literature search)
**Motivation:** User request for research into modern incremental compilation, artifact caching, hermetic builds, remote execution, LSP integration, and cross-user deduplication

**Research Scope:**
- **Academic papers:** Adapton (PLDI 2014), PIE (IC 2019), incremental type-checkers (OOPSLA 2022), stateful compilers (CGO 2024)
- **Production systems:** Rust (rustc/cargo), GHC, Scala Zinc, Salsa (rust-analyzer)
- **Build systems:** Bazel, Buck2, Nix, Shake, PIE, Turborepo, Nx
- **Remote execution:** RE API v2, BuildBuddy, Buildbarn, NativeLink
- **LSP implementations:** rust-analyzer, clangd, gopls, Deno LSP
- **Caching strategies:** Content-addressable storage, deduplication scopes, GC policies

**Pages Created:**
- [[research/incremental-compilation-synthesis]] ← **PRIMARY DOCUMENT: Complete architecture + roadmap**
- [[research/modern-incremental-compilation]] - Survey of academic/industry systems
- [[research/modern-build-systems]] - CAS, RE API, hermetic builds
- [[research/lsp-and-remote-compilation]] - LSP performance patterns
- [[research/artifact-deduplication]] - Cross-user cache sharing strategies
- [[research/INCREMENTAL-COMPILATION-SUMMARY]] - Executive summary
- [[research/incremental-compilation-references]] - Complete bibliography

**Key Findings:**
1. **Content hashing essential** - Timestamps unreliable (network FS, git ops, Docker)
2. **Fine-grained tracking matters** - Definition-level (not file-level) dependencies reduce rebuilds by 50-90%
3. **Query-based computation wins** - Salsa/rustc model: memoized queries, red-green propagation
4. **LSP needs local analysis** - Type checking local (<100ms), code gen remote (parallel)
5. **Hermetic builds enable caching** - Reproducibility → cache reuse across users/machines/time

**Concrete Recommendations for HWML:**
- `.hwmli` metadata files (content-addressed, BLAKE3 hash)
- Fine-grained dependency tracking (definition-level)
- Remote CAS (S3 or BuildBuddy)
- LSP using Salsa with cached metadata
- Remote execution for Verilog generation (RE API v2)
- Hermetic CIRCT backend (Docker container)

**Implementation Roadmap:** 6 phases, ~24 weeks total
- Phase 1-2: Content-addressed artifacts + fine-grained deps (6 weeks)
- Phase 3-4: Remote CAS + LSP integration (8 weeks)
- Phase 5-6: Remote execution + cross-clone dedup (8 weeks)

**Performance Targets:**
- Null build: 60s → 2s (30x improvement)
- Single-file change: 45s → 5s (9x)
- LSP hover: 3s → 50ms (60x)
- Remote cache hit: - → 0.5s (120x vs rebuild)
- Full clean build: 15min → 2min (7.5x)

**References:** 38 academic papers + production system docs consulted

**Impact:** This research provides a complete blueprint for HWML's incremental compilation strategy, backed by proven academic research and battle-tested industry implementations. Ready for design decisions and implementation.
