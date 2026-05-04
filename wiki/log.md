# HWML Design Wiki Log

Chronological record of wiki updates.

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
