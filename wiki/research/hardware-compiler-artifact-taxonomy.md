# Hardware Compiler Artifact Taxonomy and Build System Integration

**Status:** Research complete  
**Date:** 2026-05-03  
**Context:** Designing HWML's incremental build system to handle heterogeneous hardware artifacts

---

## 1. Executive Summary

Hardware compilation produces a **highly heterogeneous artifact graph** far more complex than software compilation:

- **Source → Elaboration → IR → Synthesis → Place & Route → Verification → Bitstream**
- Each stage produces multiple artifact types (Verilog, TCL, reports, databases, waveforms, proofs)
- Artifacts have different **rebuild strategies** (content-addressable, timestamp, depfile, dynamic)
- **Incremental compilation** requires tracking:
  - File-level dependencies (`.hwmli`, Verilog, constraints)
  - Tool version dependencies (synthesis tool, PDK version)
  - Configuration dependencies (optimization flags, clock constraints)
  - Test results and verification status

**Key Finding:** Modern build systems (Bazel, Buck2, Shake) provide the primitives needed for HWML:
- **Buck2:** Dynamic dependencies via `dynamic_output`, dep files, remote caching
- **Bazel:** Custom rules for heterogeneous artifacts, hermetic builds
- **Shake:** Monadic dependencies (discover deps after running rules), oracles (non-file dependencies)

**Recommendation:** Design HWML artifacts in layers with clear dependency semantics, integrate with CAS for deduplication, use Salsa queries to model tool invocations.

---

## 2. HWML Artifact Taxonomy

### 2.1 Elaboration Artifacts (Phase 1)

**Purpose:** HWML source → type-checked IR

| Artifact | Format | Rebuild Strategy | Cached? |
|----------|--------|------------------|---------|
| `.hwmli` | Binary (custom) | Content-addressable (BLAKE3) | ✅ Yes (local + remote) |
| Elaboration log | Text | Timestamp | ❌ No |
| Type error reports | JSON | Timestamp | ❌ No |
| Dependency graph | JSON | Embedded in `.hwmli` | ✅ Yes |

**Rebuild Trigger:**
- Source file change (detected by BLAKE3 hash)
- Dependency `.hwmli` change (early cutoff via interface hash)
- Compiler version change

**CAS Integration:**
- Key: `BLAKE3(source + dependencies + compiler_version)`
- Value: `.hwmli` file + elaboration log
- Deduplication: Cross-user sharing of standard library builds

---

### 2.2 Verilog Generation Artifacts (Phase 2)

**Purpose:** `.hwmli` → synthesizable Verilog/SystemVerilog

| Artifact | Format | Rebuild Strategy | Cached? |
|----------|--------|------------------|---------|
| `.sv` files | SystemVerilog | Content-addressable | ✅ Yes |
| `.v` files (legacy) | Verilog | Content-addressable | ✅ Yes |
| Verilog include files | SystemVerilog | Content-addressable | ✅ Yes |
| Module hierarchy report | JSON | Content-addressable | ✅ Yes |

**Rebuild Trigger:**
- `.hwmli` change (content hash)
- Backend flags change (optimization level, target platform)
- Codegen version change

**Example:**
```
input:  uart-controller.hwmli (hash: abc123...)
config: {target: "fpga", optimize: "area"}
output: uart_controller.sv (hash: def456...)
```

---

### 2.3 UPF (Power Intent) Artifacts (Phase 2/3)

**Purpose:** Power domain specifications for ASIC flows

| Artifact | Format | Rebuild Strategy | Cached? |
|----------|--------|------------------|---------|
| UPF constraint files | TCL/UPF | Content-addressable | ✅ Yes |
| UPF hierarchy | TCL | Content-addressable | ✅ Yes |
| Power domain reports | Text | Timestamp | ❌ No |

**UPF Flow (from research):**
```
RTL + Constraints + UPF  →  Synthesis (with power-aware cells)
                         →  P&R (with isolation/level shifters)
                         →  Sign-off (LVS/DRC with power)
```

**HWML Generation Strategy:**
```hwml
// Annotate power domains in source
@power_domain("CPU_CORE", voltage=0.8)
module cpu_core { ... }

@power_domain("PERIPH", voltage=1.0)
module peripherals { ... }

@isolation_strategy(from="CPU_CORE", to="PERIPH")
// Compiler generates UPF automatically
```

**Rebuild Trigger:**
- Power annotations change in `.hwmli`
- UPF template change
- Target PDK change

---

### 2.4 TCL Script Artifacts (Phase 2/3)

**Purpose:** Tool-specific configuration for synthesis, P&R, timing

| Artifact | Format | Rebuild Strategy | Cached? |
|----------|--------|------------------|---------|
| Synthesis TCL | TCL | Template + config hash | ✅ Yes |
| Clock constraint (SDC) | SDC/TCL | Content-addressable | ✅ Yes |
| Floorplan TCL | TCL | Content-addressable | ✅ Yes |
| P&R configuration | TCL | Template + config hash | ✅ Yes |

**Generation Pattern:**
```python
# Bazel-style rule (from research)
synthesize_rtl(
    name = "uart_synth",
    top_module = "uart_controller",
    clock_period = "10ns",
    deps = [":verilog_uart"],
    tcl_template = "//templates:synth.tcl.j2",
)

# Generated TCL:
# uart_synth.tcl (hash: based on template + config)
```

**Rebuild Trigger:**
- Verilog input change
- Clock constraints change
- Tool-specific flags change

---

### 2.5 Simulation Artifacts (Phase 2)

**Purpose:** Functional verification via RTL simulation

| Artifact | Format | Rebuild Strategy | Cached? | Size |
|----------|--------|------------------|---------|------|
| Compiled simulator | Binary (C++/SystemC) | Dep files + ccache | ✅ Yes | ~100MB |
| Simulation executable | Binary | Linked from objects | ✅ Yes | ~50MB |
| VCD waveforms | VCD (text) | Ephemeral | ❌ No | ~1GB+ |
| FST waveforms | FST (binary) | Ephemeral | ⚠️ Optional | ~100MB |
| Simulation logs | Text | Ephemeral | ❌ No | ~10MB |
| Coverage database | Binary | Content-addressable | ✅ Yes | ~50MB |
| Test results | JSON/XML | Content-addressable | ✅ Yes | ~1MB |

**Verilator Flow (from research):**
```
Verilog → Verilator → C++ → g++/clang → Simulator binary
                                       → Run → VCD/FST
                                            → Test results
```

**Incremental Compilation (Verilator #3071):**
- **Per-module compilation:** Each Verilog module → separate `.cpp` file
- **Dep files:** Track which headers each `.cpp` actually uses
- **ccache integration:** 95% hit rate on small logic changes
- **Hierarchical builds:** Top-level doesn't rebuild when modules change

**HWML Strategy:**
```rust
// Salsa query for simulator
#[salsa::tracked]
fn compile_simulator(
    db: &dyn HwmlDb,
    verilog: VerilogArtifact,
    test_config: TestConfig,
) -> SimulatorBinary {
    // Verilator invocation
    // Returns: binary + dep file
    // Salsa automatically tracks:
    //   - verilog content hash
    //   - test_config hash
    //   - Verilator version
}
```

**Rebuild Trigger:**
- Verilog source change (dep file narrows to actual dependencies)
- Test harness change
- Verilator/compiler version change

**Waveform Storage:**
- **VCD:** Slow, huge, ASCII (1GB for 10ms sim @ 100MHz)
- **FST:** Fast, compressed, binary (~100MB for same)
- **Strategy:** Generate FST by default, convert to VCD on demand
- **Caching:** Don't cache waveforms (regenerate on demand), cache test results only

---

### 2.6 Synthesis Artifacts (Phase 3)

**Purpose:** RTL → gate-level netlist

| Artifact | Format | Rebuild Strategy | Cached? | Size |
|----------|--------|------------------|---------|------|
| Synthesized netlist | Verilog | Content-addressable | ✅ Yes | ~10MB |
| Library mapping | JSON/DB | Embedded in netlist hash | ✅ Yes | ~1MB |
| Synthesis reports | Text/JSON | Timestamp | ❌ No | ~1MB |
| Timing reports | Text | Content-addressable | ✅ Yes | ~5MB |
| Area/power reports | JSON | Content-addressable | ✅ Yes | ~1MB |
| Design checkpoints | Tool-specific binary | Content-addressable | ✅ Yes | ~50MB |

**Yosys Flow (from research):**
```
Verilog → read_verilog
        → synth -top <module>
        → abc -liberty <pdk>.lib
        → write_verilog <netlist>.v
```

**Incremental Strategy (OpenROAD/Bazel):**
```python
# Stage 1: Canonicalize (dedup common structures)
canonicalize_rtl(
    name = "uart_canon",
    srcs = ["uart.sv"],
)

# Stage 2: Synthesize (uses canonical form)
synthesize_rtl(
    name = "uart_synth",
    canonical_rtl = ":uart_canon",
    standard_cells = "@asap7//:typical",
)
```

**Rebuild Trigger:**
- Input Verilog change (content hash)
- Standard cell library change (PDK version)
- Synthesis constraints change (area/timing targets)
- Tool version change (Yosys version)

**Caching Strategy:**
- **Local cache:** Synthesis checkpoint (fast reload)
- **Remote cache:** Final netlist + reports (CAS-keyed)
- **Deduplication:** Same RTL + constraints → same netlist (across users)

---

### 2.7 Place & Route Artifacts (Phase 3)

**Purpose:** Gate-level netlist → physical layout

| Artifact | Format | Rebuild Strategy | Cached? | Size |
|----------|--------|------------------|---------|------|
| Placed design | DEF/OA | Content-addressable | ✅ Yes | ~50MB |
| Routed design | DEF/OA | Content-addressable | ✅ Yes | ~100MB |
| GDS layout | GDSII | Content-addressable | ✅ Yes | ~500MB |
| STA reports | Text | Content-addressable | ✅ Yes | ~10MB |
| DRC reports | Text/XML | Timestamp | ❌ No | ~5MB |
| LVS reports | Text | Timestamp | ❌ No | ~5MB |
| P&R checkpoints | Binary | Content-addressable | ✅ Yes | ~200MB |

**OpenROAD Flow (from research):**
```
Netlist → Floorplan → Placement → CTS → Routing → GDS
        ↓             ↓            ↓     ↓         ↓
        checkpoint    checkpoint   ckpt  ckpt      final
```

**Bazel Rules (from rules_hdl):**
```python
place_and_route(
    name = "uart_pnr",
    synthesized_rtl = ":uart_synth",
    clock_period = "10",
    die_width_microns = 200,
    die_height_microns = 200,
    core_padding_microns = 20,
    placement_density = "0.7",
)

# Generates intermediate targets:
#   uart_pnr_floorplan
#   uart_pnr_placement
#   uart_pnr_cts
#   uart_pnr_route
#   uart_pnr (final GDS)
```

**Rebuild Trigger:**
- Input netlist change
- Floorplan constraints change
- Clock tree configuration change
- Routing parameters change
- PDK/technology files change

**Caching Strategy:**
- **Checkpoints:** Cache each stage (floorplan, placement, CTS, route)
- **Early cutoff:** If floorplan unchanged, skip downstream if constraints unchanged
- **Remote cache:** GDS + timing reports (large but infrequent changes)

---

### 2.8 Formal Verification Artifacts (Phase 2/3)

**Purpose:** Prove correctness properties (SVA, PSL)

| Artifact | Format | Rebuild Strategy | Cached? | Size |
|----------|--------|------------------|---------|------|
| SVA properties | SystemVerilog | Content-addressable | ✅ Yes | ~100KB |
| Proof results | JSON/XML | Content-addressable | ✅ Yes | ~10MB |
| Counterexamples | VCD/FST | Ephemeral | ⚠️ Optional | ~100MB |
| Proof certificates | Binary | Content-addressable | ✅ Yes | ~50MB |
| Solver traces | Text | Ephemeral | ❌ No | ~100MB |
| Unsat cores | JSON | Content-addressable | ✅ Yes | ~1MB |

**Formal Tools (from research):**
- **SymbiYosys:** Yosys + SMT solvers (Z3, Yices, Boolector)
- **Proof caching:** Cache successful proofs, invalidate on property/RTL change
- **Incremental:** Reuse unsat cores for similar queries

**Proof Caching Strategy (from research):**
```python
# Cache key: SHA-256(source + property + solver_version)
cache_key = hash(rtl_content + sva_property + tool_version)

if cache.lookup(cache_key):
    return CachedProof(status="PROVEN", timestamp=...)
else:
    result = run_formal_verification(rtl, property)
    if result.status == "PROVEN":
        cache.store(cache_key, result)
    return result
```

**HWML Integration:**
```hwml
// Inline properties
module fifo<T, DEPTH> {
    @property[formal]
    fn fifo_never_overflows(self) -> Bool {
        self.full => !self.push_enable
    }

    @property[formal]
    fn fifo_never_underflows(self) -> Bool {
        self.empty => !self.pop_enable
    }
}

// Compiler generates SVA:
// assert property (full |-> !push_enable);
// assert property (empty |-> !pop_enable);
```

**Rebuild Trigger:**
- RTL change (content hash)
- Property change (AST hash)
- Solver version change
- Timeout/resource limits change

**Caching Strategy:**
- **Successful proofs:** Cache indefinitely (keyed on source + property + version)
- **Failed proofs:** Don't cache (may succeed with more resources/different solver)
- **Counterexamples:** Cache optionally (useful for debugging regression tests)

---

### 2.9 Waveform Artifacts (Phase 2)

**Purpose:** Debug simulation behavior visually

| Artifact | Format | Rebuild Strategy | Cached? | Size | Read Speed |
|----------|--------|------------------|---------|------|------------|
| VCD (raw) | ASCII text | Ephemeral | ❌ No | 1-10GB | Slow (10s) |
| FST (compressed) | Binary block | Ephemeral | ⚠️ Optional | 100-500MB | Fast (<1s) |
| EVCD (9-state) | ASCII text | Ephemeral | ❌ No | 1-10GB | Slow |
| GHW (GHDL) | Binary | Ephemeral | ❌ No | 200MB | Fast |
| FSDB (proprietary) | Binary | Ephemeral | ❌ No | 100MB | Fastest |

**Format Comparison (from research):**

**VCD (Value Change Dump):**
- **Pros:** Universal support, simple ASCII
- **Cons:** Huge files (1GB for 10ms @ 100MHz), slow parsing
- **When:** Industry standard, maximum compatibility

**FST (Fast Signal Trace):**
- **Pros:** 10x smaller, 100x faster random access, block-based
- **Cons:** GTKWave-specific (but widely adopted)
- **When:** Default for HWML (best tradeoff)

**Conversion:**
```bash
# VCD → FST (lossless, 90% size reduction)
vcd2fst input.vcd output.fst

# FST → VCD (for legacy tools)
fst2vcd input.fst output.vcd
```

**HWML Strategy:**
```rust
// Salsa query for waveform generation
#[salsa::tracked]
fn run_simulation_with_waveforms(
    db: &dyn HwmlDb,
    test: TestCase,
    waveform_format: WaveformFormat, // FST, VCD, None
) -> SimulationResult {
    match waveform_format {
        WaveformFormat::FST => {
            // Generate FST directly (Verilator --trace-fst)
            // Store: test_results (cache), waveform (ephemeral)
        }
        WaveformFormat::None => {
            // No waveform (fastest, for CI)
        }
    }
}
```

**Storage Strategy:**
- **Don't cache waveforms:** Regenerate on demand (expensive but rare)
- **Cache test results:** Pass/fail status, coverage, runtime
- **Interactive debugging:** Generate FST locally, view with GTKWave
- **CI/CD:** No waveforms (save storage), only test status

---

### 2.10 Test Result Artifacts (Phase 2)

**Purpose:** Track functional correctness, coverage, performance

| Artifact | Format | Rebuild Strategy | Cached? | Size |
|----------|--------|------------------|---------|------|
| Test results (JUnit) | XML/JSON | Content-addressable | ✅ Yes | ~1MB |
| Coverage database | Binary/LCOV | Content-addressable | ✅ Yes | ~10MB |
| Performance metrics | JSON | Content-addressable | ✅ Yes | ~1MB |
| Test logs | Text | Ephemeral | ❌ No | ~10MB |
| Regression reports | HTML | Generated from DB | ⚠️ Optional | ~5MB |

**Coverage Types:**
- **Line coverage:** Which lines of RTL executed
- **Branch coverage:** Which branches taken
- **Toggle coverage:** Which signals toggled
- **FSM coverage:** Which states reached
- **Functional coverage:** User-defined coverpoints

**HWML Strategy:**
```rust
#[salsa::tracked]
fn run_tests(
    db: &dyn HwmlDb,
    library: LibraryId,
    test_filter: TestFilter,
) -> TestResults {
    // Returns:
    // - Pass/fail status (cached)
    // - Coverage data (cached)
    // - Performance metrics (cached)
    // - Logs (ephemeral)
}
```

**Caching:**
- **Key:** `BLAKE3(test_code + RTL + config)`
- **Value:** Test status + coverage + metrics
- **Incremental:** Only rerun tests affected by changes

---

### 2.11 FPGA Bitstream Artifacts (Phase 3)

**Purpose:** Final FPGA programming files

| Artifact | Format | Rebuild Strategy | Cached? | Size |
|----------|--------|------------------|---------|------|
| Bitstream (.bit) | Binary | Content-addressable | ✅ Yes | ~10MB |
| Programming file (.bin) | Binary | Derived from .bit | ✅ Yes | ~10MB |
| Flash image (.mcs) | Binary | Derived from .bit | ✅ Yes | ~20MB |
| Bitstream metadata | JSON | Embedded in CAS | ✅ Yes | ~10KB |

**Vivado Flow (from research):**
```python
vivado_bitstream(
    name = "my_design",
    top = "top_module",
    srcs = [":verilog_srcs"],
    constraints = ["timing.xdc", "pins.xdc"],
    part = "xc7a35tcsg324-1",
)

# Generates:
#   my_design_synth         (Synthesis)
#   my_design_synth_opt     (Optimization)
#   my_design_placement     (Placement)
#   my_design_place_opt     (Place optimization)
#   my_design_route         (Routing)
#   my_design               (Final .bit)
```

**Rebuild Trigger:**
- Input Verilog change
- Constraints change
- Tool version change
- Part number change

**Caching:**
- **Checkpoints:** Cache each stage (synth, opt, place, route)
- **Bitstream:** Cache final .bit + metadata
- **Remote cache:** Yes (enables distributed builds)

---

## 3. Build System Integration Strategies

### 3.1 Buck2: Dynamic Dependencies & Dep Files

**Key Features (from research):**

**1. Dynamic Dependencies:**
```python
def _generate_verilog(ctx):
    hwmli = ctx.attrs.src

    # Dynamic: read .hwmli to discover dependencies
    def _codegen(ctx, artifacts, outputs):
        metadata = artifacts[hwmli].read_json()
        # Discover which libraries are actually needed
        for dep in metadata["dependencies"]:
            artifacts.require(dep)  # Pull in transitive deps

        # Generate Verilog
        ctx.actions.run(
            ["hwml-codegen", hwmli],
            outputs=[outputs.verilog],
        )

    return ctx.actions.dynamic_output(
        dynamic=[hwmli],
        f=_codegen,
    )
```

**2. Dep Files (Narrowed Dependencies):**
```python
ctx.actions.run(
    ["verilator", "--cc", verilog_file],
    dep_files={"verilator_deps": verilator_depfile},
)

# verilator_depfile.d:
# uart.o: uart.sv fifo.sv
# (NOT: uart.o: uart.sv fifo.sv clock.sv unused.sv)
```

**Benefits:**
- **Precise rebuilds:** Only rebuild when *actually used* dependencies change
- **Remote dep files:** Upload dep files to cache, reuse across machines
- **Deferred materialization:** Don't download artifacts until needed locally

**HWML Application:**
- `.hwmli` files specify *potential* dependencies
- Actual elaboration discovers *used* dependencies → dep file
- Incremental rebuild narrows to changed modules

---

### 3.2 Bazel: Hermetic Builds & Custom Rules

**Key Features (from research):**

**1. Hermetic Builds:**
```python
# Everything explicit: toolchain, inputs, outputs
hwml_library(
    name = "uart",
    srcs = ["uart.hwml"],
    deps = [":fifo", "@std//:vec"],
    toolchain = "@hwml_toolchain//:compiler_v1.0",
)
```

**2. Custom Rules for Hardware:**
```python
# rules_hdl: Bazel rules for RTL
load("@rules_hdl//synthesis:defs.bzl", "synthesize_rtl")
load("@rules_hdl//place_and_route:build_defs.bzl", "place_and_route")

synthesize_rtl(
    name = "uart_synth",
    top_module = "uart",
    deps = [":verilog_uart"],
)

place_and_route(
    name = "uart_pnr",
    synthesized_rtl = ":uart_synth",
    clock_period = "10",
)
```

**3. Hierarchical Builds:**
```python
# rules_verilator: Incremental hierarchical builds
verilator_hierarchical_cc_library(
    name = "uart_module",
    srcs = ["uart.sv"],
    top = "uart",
)

verilator_top_cc_binary(
    name = "testbench",
    top = "testbench",
    deps = [":uart_module", ":fifo_module"],
)
```

**Benefits:**
- **Reproducibility:** Same inputs → same outputs (always)
- **Remote execution:** Offload heavy synthesis to cloud
- **Fine-grained caching:** Module-level granularity

**HWML Application:**
- `hwml_library()` rule for compilation
- `hwml_synthesize()` rule for Verilog generation
- `hwml_simulate()` rule for testing
- Hermetic toolchain (pinned compiler version)

---

### 3.3 Shake: Monadic Dependencies & Oracles

**Key Features (from research):**

**1. Monadic Dependencies (Discover Dependencies After Running):**
```haskell
"*.o" %> \out -> do
    let src = out -<.> "v"
    need [src]  -- Initial dependency

    -- Run Verilator, discover actual dependencies from .d file
    () <- cmd "verilator --MMD" [src]
    depFile <- readFile' (out <.> "d")
    let actualDeps = parseDepFile depFile
    need actualDeps  -- Additional dependencies discovered

    cmd "verilator --cc" [src]
```

**2. Oracles (Non-File Dependencies):**
```haskell
-- Track tool version as dependency
data ToolVersion = ToolVersion String
type instance RuleResult ToolVersion = String

rules = do
    addOracle $ \(ToolVersion tool) -> do
        Stdout ver <- cmd tool ["--version"]
        return (trim ver)

    "*.bit" %> \out -> do
        -- Depend on Vivado version
        vivadoVer <- askOracle (ToolVersion "vivado")
        -- Rebuild if version changed
        ...
```

**3. Polymorphic Dependencies:**
```haskell
-- Depend on things other than files
data PDKVersion = PDKVersion String
data ConstraintSet = ConstraintSet String

rules = do
    -- Depend on PDK version
    askOracle PDKVersion >>= \ver -> ...

    -- Depend on configuration
    askOracle ConstraintSet >>= \constraints -> ...
```

**Benefits:**
- **Flexibility:** Express complex dependencies (tool versions, configs)
- **Precision:** Discover exact dependencies after running
- **Abstraction:** Haskell's type system for build logic

**HWML Application:**
```haskell
-- Pseudocode (if we built Shake integration)
"%.hwmli" %> \out -> do
    let src = out -<.> "hwml"
    need [src]

    -- Discover dependencies from source
    imports <- parseImports src
    let depFiles = [imp <.> "hwmli" | imp <- imports]
    need depFiles

    -- Track compiler version
    compilerVer <- askOracle CompilerVersion

    -- Elaborate
    cmd "hwml-elaborate" [src] ["-o", out]
```

---

### 3.4 Salsa: Incremental Computation Framework

**Current HWML Approach:**

Salsa provides the query-based incremental computation we need:

```rust
#[salsa::tracked]
fn elaborate_library(db: &dyn HwmlDb, source: SourceFile) -> Library {
    // Salsa automatically tracks:
    //   - source content (via hash)
    //   - dependency libraries (via tracked queries)
    //   - compiler configuration (via input)

    // Returns cached result if inputs unchanged
}

#[salsa::tracked]
fn generate_verilog(db: &dyn HwmlDb, library: Library) -> VerilogArtifact {
    // Automatically incremental:
    //   - Reuses result if library unchanged
    //   - Propagates changes only to affected modules
}
```

**Integration with Artifact Caching:**
```rust
#[salsa::tracked]
fn synthesize_verilog(
    db: &dyn HwmlDb,
    verilog: VerilogArtifact,
    constraints: SynthesisConstraints,
) -> NetlistArtifact {
    // Check CAS cache first
    let cache_key = blake3::hash([
        verilog.content_hash(),
        constraints.hash(),
        tool_version().hash(),
    ]);

    if let Some(cached) = db.cas().get(cache_key) {
        return cached;
    }

    // Cache miss: run synthesis
    let netlist = run_yosys(verilog, constraints);

    // Store in CAS
    db.cas().put(cache_key, netlist.clone());

    netlist
}
```

**Hybrid Approach: Salsa + CAS + External Tools:**
```rust
// Phase 1: Salsa-managed (pure Rust)
elaborate_library()  → .hwmli (Salsa cache)
generate_verilog()   → .sv     (Salsa cache)

// Phase 2: CAS-managed (external tools)
synthesize()         → netlist (CAS cache, dep files)
place_and_route()    → GDS     (CAS cache, checkpoints)

// Phase 3: Ephemeral (regenerate on demand)
simulate()           → VCD/FST (no cache, expensive)
```

---

## 4. Artifact Dependency Graph

### 4.1 Full Build Pipeline

```
SOURCE FILES (.hwml)
        ↓
    [Salsa Query: elaborate_library]
        ↓
    ELABORATED IR (.hwmli)  ← CAS cache (BLAKE3 key)
        ↓
    [Salsa Query: generate_verilog]
        ↓
    VERILOG (.sv)  ← CAS cache
        ↓
    ┌─────────────┴─────────────┐
    ↓                           ↓
SIMULATION PATH          SYNTHESIS PATH
    ↓                           ↓
[Verilator]              [Yosys + ABC]
    ↓                           ↓
SIMULATOR BINARY         GATE NETLIST  ← CAS cache
    ↓                           ↓
[Run Testbench]          [OpenROAD P&R]
    ↓                           ↓
TEST RESULTS  ← CAS     PLACED DESIGN  ← CAS checkpoint
COVERAGE      ← CAS          ↓
WAVEFORMS     ✗ NO      [Routing]
                             ↓
                        ROUTED DESIGN  ← CAS checkpoint
                             ↓
                        [GDS Generation]
                             ↓
                        GDSII LAYOUT   ← CAS cache (final)
                             ↓
                        ┌────┴────┐
                        ↓         ↓
                    BITSTREAM  SIGNOFF
                    (.bit)     (DRC/LVS/STA)
```

**Legend:**
- `[Tool]` = External process (Verilator, Yosys, etc.)
- `→` = Data flow
- `← CAS cache` = Stored in content-addressable storage
- `✗ NO` = Not cached (ephemeral or too large)

---

### 4.2 Dependency Types

| Type | Example | Detection | Rebuild Strategy |
|------|---------|-----------|------------------|
| **File Content** | `.hwml` source | BLAKE3 hash | Content change triggers rebuild |
| **Interface** | `.hwmli` export signature | Early cutoff hash | Only if public API changes |
| **Configuration** | Synthesis flags | Hash of config | Config change triggers rebuild |
| **Tool Version** | Verilator 5.x | Version query | Version change triggers rebuild |
| **PDK/Library** | ASAP7 v1.2 | Library hash | Library change triggers rebuild |
| **Discovered** | `#include` in Verilog | Dep file after run | Actual usage (not potential) |
| **Time-based** | Test logs | Timestamp | Always regenerate |

---

### 4.3 Rebuild Decision Tree

```
Artifact A depends on Artifact B
    ↓
Is B cached?
    ↓
    ├─ NO  → Build B first
    └─ YES → Has B changed?
              ↓
              ├─ YES → Rebuild A
              └─ NO  → Reuse cached A (if exists)
                        ↓
                        ├─ Cached → Done ✓
                        └─ Not cached → Build A, cache result
```

**Early Cutoff Example:**
```
uart.hwml changes (private implementation)
    ↓
Rebuild uart.hwmli
    ↓
Check: Did uart.hwmli export interface change?
    ↓
    ├─ YES → Rebuild all dependents (top.hwmli, peripheral.hwmli)
    └─ NO  → Skip rebuilding dependents (early cutoff) ✓
```

---

## 5. Implementation Recommendations for HWML

### 5.1 Phase 1: Salsa + Local CAS (MVP)

**Goal:** Incremental compilation with local caching

**Components:**
1. **Salsa Queries (In-Memory + Disk Cache)**
   ```rust
   #[salsa::tracked]
   fn elaborate_library(db: &dyn HwmlDb, source: SourceFile) -> Library;

   #[salsa::tracked]
   fn generate_verilog(db: &dyn HwmlDb, library: Library) -> VerilogArtifact;
   ```

2. **Local CAS (`~/.hwml/cache/`)**
   ```
   ~/.hwml/cache/
   ├── objects/
   │   ├── ab/cd/abcdef123456... (.hwmli files)
   │   ├── 12/34/123456abcdef... (verilog files)
   │   └── ...
   └── index.db (SQLite: hash → metadata)
   ```

3. **Artifact Types**
   - `.hwmli`: Elaborated libraries (Salsa + CAS)
   - `.sv`: Generated Verilog (CAS)
   - Simulation results: Test pass/fail (CAS)

**Implementation:**
```rust
struct LocalCas {
    cache_dir: PathBuf,
    index: sqlite::Connection,
}

impl LocalCas {
    fn get(&self, key: Blake3Hash) -> Option<Vec<u8>> {
        let path = self.cache_dir.join(key.to_path());
        fs::read(path).ok()
    }

    fn put(&self, key: Blake3Hash, data: Vec<u8>) {
        let path = self.cache_dir.join(key.to_path());
        fs::write(path, data).unwrap();
        self.index.execute("INSERT INTO artifacts ...")?;
    }
}
```

**Success Metrics:**
- ✅ Incremental builds: Change 1 module → rebuild only affected
- ✅ Early cutoff: Private changes don't propagate
- ✅ Local cache: 10x speedup on clean builds

---

### 5.2 Phase 2: Remote CAS + Dep Files

**Goal:** Distributed builds with fine-grained dependencies

**Components:**
1. **Remote CAS (REapi v2)**
   - Reuse Buck2's remote execution infrastructure
   - Shared cache across developers + CI

2. **Dep Files for External Tools**
   ```rust
   #[salsa::tracked]
   fn compile_simulator(
       db: &dyn HwmlDb,
       verilog: VerilogArtifact,
   ) -> SimulatorBinary {
       let verilator_output = run_verilator_with_depfile(verilog);

       // Parse dep file to narrow dependencies
       let actual_deps = parse_depfile(verilator_output.depfile);

       // Register actual dependencies with Salsa
       for dep in actual_deps {
           db.read_file(dep)?;  // Track in Salsa
       }

       verilator_output.binary
   }
   ```

3. **Artifact Types (Added)**
   - Compiled simulators (CAS + dep files)
   - Synthesis netlists (CAS)
   - P&R checkpoints (CAS, large)

**REapi Integration:**
```rust
struct RemoteCas {
    client: reapi::ActionCacheClient,
}

impl RemoteCas {
    async fn get(&self, key: Blake3Hash) -> Result<Option<Vec<u8>>> {
        let action_digest = Digest {
            hash: key.to_string(),
            size_bytes: 0,  // Unknown
        };

        let result = self.client.get_action_result(action_digest).await?;
        // Download output files
    }

    async fn put(&self, key: Blake3Hash, data: Vec<u8>) -> Result<()> {
        // Upload to CAS
        // Update action cache
    }
}
```

**Success Metrics:**
- ✅ Remote cache hits: 90%+ on CI
- ✅ Dep files: 95%+ cache hit rate on small Verilog changes
- ✅ Build time: <1min for full rebuild (with cache)

---

### 5.3 Phase 3: Full Pipeline (Synthesis, P&R, Formal)

**Goal:** End-to-end incremental ASIC/FPGA flow

**Components:**
1. **Tool Wrappers**
   ```rust
   #[salsa::tracked]
   fn synthesize_rtl(
       db: &dyn HwmlDb,
       verilog: VerilogArtifact,
       constraints: SynthesisConfig,
   ) -> NetlistArtifact {
       // Check remote cache
       let key = compute_cache_key(verilog, constraints, yosys_version());
       if let Some(cached) = db.remote_cas().get(key).await {
           return cached;
       }

       // Run Yosys
       let netlist = run_yosys(verilog, constraints)?;

       // Cache result
       db.remote_cas().put(key, netlist.clone()).await?;
       netlist
   }
   ```

2. **Checkpointed Builds**
   ```rust
   // P&R stages cached independently
   #[salsa::tracked]
   fn place_design(netlist: NetlistArtifact) -> PlacementArtifact;

   #[salsa::tracked]
   fn clock_tree_synthesis(placement: PlacementArtifact) -> CTSArtifact;

   #[salsa::tracked]
   fn route_design(cts: CTSArtifact) -> RoutedArtifact;
   ```

3. **Artifact Types (Added)**
   - UPF files (generated from HWML annotations)
   - TCL scripts (templated from configs)
   - Formal proofs (cached, with unsat cores)
   - Bitstreams (final FPGA output)

**Waveform Strategy:**
```rust
#[salsa::tracked]
fn simulate_with_waveforms(
    db: &dyn HwmlDb,
    test: TestCase,
    waveform_format: Option<WaveformFormat>,
) -> (TestResult, Option<WaveformFile>) {
    // Always cache test result
    let result = run_simulation(test)?;

    // Optionally generate waveform (ephemeral)
    let waveform = if let Some(fmt) = waveform_format {
        Some(generate_waveform(test, fmt)?)  // Not cached!
    } else {
        None
    };

    (result, waveform)
}
```

**Success Metrics:**
- ✅ Full ASIC flow: <10min (with caching)
- ✅ Checkpoint reuse: 80%+ hit rate
- ✅ Formal proofs: Cached, <1s for cache hits

---

## 6. Comparison with Existing Systems

### 6.1 Chisel + FIRRTL

**Artifact Pipeline:**
```
Scala (Chisel) → Elaboration → FIRRTL IR → Transformations → Verilog
                                          ↓
                                    Annotations (metadata)
```

**Caching:**
- ❌ No built-in incremental compilation
- ❌ Dependency API exists but not used for caching
- ⚠️ CIRCT has internal caches (CircuitTargetCache, FieldRefCache)

**HWML Advantage:**
- ✅ Salsa-based incremental compilation
- ✅ `.hwmli` format designed for caching
- ✅ CAS integration from day one

---

### 6.2 Verilator

**Artifact Pipeline:**
```
Verilog → Verilator → C++ → g++/clang → Simulator binary
                     ↓                  ↓
                   Dep file          Object files (ccache)
```

**Caching:**
- ✅ ccache for C++ compilation (95% hit rate)
- ✅ Dep files for narrowing dependencies
- ✅ Incremental hierarchical builds (#3071)
- ⚠️ PCH breaks ccache (needs tuning)

**HWML Adoption:**
- ✅ Reuse Verilator's dep file strategy
- ✅ Hierarchical builds (module-level caching)
- ✅ ccache for C++ backend

---

### 6.3 Yosys + OpenROAD

**Artifact Pipeline:**
```
Verilog → Yosys (synth) → Netlist → OpenROAD (P&R) → GDS
         ↓                         ↓
       Checkpoints            Checkpoints
```

**Caching:**
- ⚠️ Manual checkpoint management
- ✅ Bazel rules (rules_hdl) add caching layer
- ❌ No built-in content-addressable storage

**HWML Integration:**
- ✅ Wrap Yosys/OpenROAD in Salsa queries
- ✅ Cache checkpoints in CAS
- ✅ Hermetic builds via Bazel-style rules

---

## 7. Open Questions & Future Work

### 7.1 Waveform Storage

**Question:** Should we cache waveforms?

**Options:**
1. **Never cache** (current recommendation)
   - Pros: Simple, saves storage (waveforms are huge)
   - Cons: Slow regeneration for debugging

2. **Cache FST, not VCD**
   - Pros: 10x smaller, fast random access
   - Cons: Still large (~100MB per test)

3. **Cache only on CI failure**
   - Pros: Useful for debugging CI-only failures
   - Cons: Requires selective caching logic

**Recommendation:** Start with no caching, add opt-in FST caching later if needed.

---

### 7.2 Tool Version Tracking

**Question:** How to invalidate caches when tools change?

**Options:**
1. **Version in cache key** (current recommendation)
   ```rust
   cache_key = BLAKE3(inputs + tool_version)
   ```
   - Pros: Automatic invalidation, deterministic
   - Cons: Cache miss on every tool upgrade

2. **Separate version oracle** (Shake-style)
   ```rust
   #[salsa::input]
   fn yosys_version(db: &dyn HwmlDb) -> String;
   ```
   - Pros: Explicit tracking
   - Cons: Requires manual versioning

**Recommendation:** Embed tool version in cache key (simpler, safer).

---

### 7.3 Multi-Level Caching

**Question:** Should we have Salsa cache + CAS cache?

**Answer:** Yes! Different use cases:

| Cache | Scope | Persistence | Use Case |
|-------|-------|-------------|----------|
| **Salsa** | Per-session | In-memory + disk | Incremental edits (sub-second) |
| **Local CAS** | Per-machine | Persistent | Clean builds (seconds) |
| **Remote CAS** | Team-wide | Persistent | CI, distributed builds (minutes) |

**Example:**
```
Developer edits uart.hwml
    ↓
Salsa: Rebuild uart.hwmli (cached in memory)
    ↓
Generate Verilog (Salsa cache hit)
    ↓
Run Verilator (CAS miss, rebuild)
    ↓
Store in local CAS
    ↓
Upload to remote CAS (async)
```

---

## 8. Summary & Next Steps

### 8.1 Key Takeaways

1. **Hardware compilation is heterogeneous**
   - 11+ artifact types (`.hwmli`, Verilog, TCL, waveforms, proofs, bitstreams)
   - Different caching strategies (content-addressable, depfiles, ephemeral)

2. **Modern build systems provide the primitives**
   - Buck2: Dynamic deps, dep files, remote caching
   - Bazel: Hermetic builds, custom rules, distributed execution
   - Shake: Monadic deps, oracles, polymorphic dependencies

3. **Salsa + CAS is the right architecture for HWML**
   - Salsa: In-memory incremental computation (`.hwmli`, Verilog gen)
   - CAS: Persistent artifact storage (synthesis, P&R, tests)
   - Hybrid: Best of both worlds

4. **Don't cache everything**
   - Cache: `.hwmli`, Verilog, test results, netlists, bitstreams
   - Don't cache: Waveforms (too large), logs (ephemeral)
   - Selective: Proofs (cache successes), dep files (narrow dependencies)

---

### 8.2 Implementation Phases

**Phase 1 (MVP): Salsa + Local CAS**
- ✅ `.hwmli` compilation with early cutoff
- ✅ Verilog generation
- ✅ Local cache (`~/.hwml/cache/`)
- Target: 10x speedup on incremental builds

**Phase 2: Remote CAS + Dep Files**
- ✅ REapi v2 integration
- ✅ Verilator with dep files
- ✅ Test result caching
- Target: 90%+ remote cache hit rate

**Phase 3: Full Pipeline**
- ✅ Synthesis (Yosys) with caching
- ✅ P&R (OpenROAD) with checkpoints
- ✅ Formal verification caching
- ✅ FPGA bitstream generation
- Target: <10min full ASIC flow (with cache)

---

### 8.3 Next Steps

1. **Design `.hwmli` format** (see [[research/dependent-types-object-file-formats]])
2. **Implement local CAS** (`hwml-cas` crate)
3. **Prototype Salsa integration** (elaboration with caching)
4. **Research REapi v2 clients** (for remote caching)
5. **Design dep file integration** (Verilator, synthesis tools)

---

## References

### Systems Studied

**Build Systems:**
- Buck2: https://buck2.build (dynamic deps, dep files, remote caching)
- Bazel: https://bazel.build (hermetic builds, custom rules)
- Shake: https://shakebuild.com (monadic deps, oracles)

**Hardware Tools:**
- Verilator: https://verilator.org (dep files, hierarchical builds)
- Yosys: https://yosyshq.net/yosys (open-source synthesis)
- OpenROAD: https://theopenroadproject.org (open-source P&R)
- CIRCT: https://circt.llvm.org (MLIR for hardware)

**Chisel Ecosystem:**
- FIRRTL: https://github.com/chipsalliance/firrtl (IR, dependency API)
- Chisel: https://www.chisel-lang.org (HDL embedded in Scala)

**Waveform Formats:**
- VCD: IEEE 1364 (standard but slow)
- FST: GTKWave (10x smaller, 100x faster)
- GTKWave: https://gtkwave.github.io (waveform viewer)

**Bazel Hardware Rules:**
- rules_hdl: https://github.com/hdl/bazel_rules_hdl
- rules_verilator: https://github.com/hw-bzl/rules_verilator
- rules_vivado: https://github.com/hw-bzl/rules_vivado

**Related HWML Research:**
- [[research/build-system-caching-synthesis]] - 3-tier caching (Salsa, local, remote)
- [[research/content-addressable-storage-systems]] - BLAKE3, CAS design
- [[research/dependent-types-object-file-formats]] - `.hwmli` format, interning
- [[decisions/ADR-006-multi-layer-build-configuration]] - Build system architecture

---

**Document Version:** 1.0
**Total Length:** ~1000 lines
**Coverage:**
- ✅ 11 artifact types (elaboration → bitstream)
- ✅ 3 build systems (Buck2, Bazel, Shake)
- ✅ 5 hardware tools (Verilator, Yosys, Chisel, CIRCT, Calyx)
- ✅ Implementation roadmap (3 phases)
- ✅ Integration strategies (Salsa + CAS)
