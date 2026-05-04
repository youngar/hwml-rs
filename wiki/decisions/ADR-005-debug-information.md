# ADR-005: Debug Information Strategy

**Status:** Proposed
**Date:** 2026-05-03
**Deciders:** Architecture Team
**Context Tags:** #debug-info #elaboration #hardware-generation #developer-experience

---

## Context

HWML is a two-level dependently-typed hardware description language with:
1. **Meta-level:** Elaboration (type checking, unification, NbE)
2. **Object-level:** Generated hardware (Verilog, CIRCT)

Both levels require different kinds of information for users to understand errors and debug their code.

### Important Distinction: Error Reporting vs Debug Information

This ADR covers TWO distinct concerns that are often conflated:

1. **Error Reporting Infrastructure** - Metadata needed to produce good error messages
   - Examples: constraint origins, metavariable provenance, source locations
   - **Always present** - Required for basic usability
   - NOT optional, NOT controlled by debug flags
   - Used when compilation fails

2. **Debug Information** - Additional data for debugging compiled output
   - Examples: DWARF, source locators in Verilog, waveform dumps
   - **Optionally present** - Controlled by debug flags
   - Used when compilation succeeds but behavior is wrong

**This ADR addresses both**, but it's critical to understand that constraint/metavariable tracking is in category #1, not #2.

### Research Foundation

We conducted comprehensive research covering:
- **DWARF, PDB, and debug formats** [[research/debug-info-systems]]
- **Hardware debug** (VCS, FSDB, waveforms) [[research/hardware-debug-info]]
- **LLVM implementation** (preservation, salvaging) [[research/llvm-debug-info-internals]]
- **Modern academic research** (ASPLOS, PLDI, Onward! 2020-2024) [[research/debug-info-research-modern]]
- **Elaboration error messages** (SHErrLoc, flow-based errors, Rust/Lean/Agda) [[research/elaboration-error-messages]]

### Key Research Findings

#### From Debug Info Research (DWARF, LLVM, Optimization)

1. **Debug info correctness is ill-posed** (Kell & Stinnett, Onward! 2024)
   - No unique "correct" debug info
   - Trade-offs between density, height, and fidelity
   - Multiple valid interpretations exist

2. **Current compilers have significant gaps** (Assaiante et al., ASPLOS 2023)
   - Only 60-70% variable visibility at -O2
   - 80-90% of visible variables have values
   - Hundreds of DWARF bugs in GCC/LLVM

3. **Debug info must not affect optimization** (Wang et al., ASPLOS 2023)
   - CCMD (Compilation Consistency Modulo Debug Information)
   - Enabling `-g` should not change semantics
   - Systematic testing required

4. **Liveness-based metrics are essential** (arXiv 2024)
   - Naive coverage metrics misleading
   - Must account for actual variable lifetime
   - Provides comparable quality measurements

#### From Error Message Research (Type Systems, Elaboration)

5. **Constraint origin tracking is essential** (All modern type systems)
   - Rust, Lean 4, GHC, Agda all extensively track WHY constraints exist
   - Error location depends on constraint provenance, not failure order
   - Users need to understand data flow, not just type mismatches

6. **Metavariable provenance is NOT optional** (Agda Issue #2073, Lean 4 design)
   - Users need to know WHERE and WHY each metavariable was created
   - Without provenance: "Cannot solve ?m" (useless)
   - With provenance: "?m created as implicit arg to 'replicate' at line 10, constrained by: n ~ 8 (line 12), n ~ width(x) (line 15), conflict: 8 ≠ width(x)" (actionable)
   - This is ERROR REPORTING INFRASTRUCTURE, not "debug info"

7. **Global diagnosis beats local failure** (SHErrLoc, Flow-based errors)
   - Don't report first failure point
   - Collect all constraints, analyze constraint graph
   - Find minimal unsatisfiable subset
   - Explain as data flow: "value of type A flows to context expecting B"

### HWML-Specific Challenges

#### Meta-Level Challenges
1. **Dependent types** - Types depend on runtime values
2. **Metavariables** - Unification variables have complex state
3. **NbE (Normalization by Evaluation)** - Terms transformed during evaluation
4. **Elaboration synthesis** - Compiler-generated terms have no source location
5. **Two-level staging** - Meta vs object level distinction

#### Object-Level Challenges
1. **Hardware vs software debugging** - Waveforms, not execution traces
2. **Signal propagation** - Parallel, time-based behavior
3. **Synthesis transformations** - Logic optimization destroys structure
4. **Module hierarchy** - Must preserve for waveform viewers
5. **Tool compatibility** - VCS, Verdi, ModelSim, Verilator

---

## Decision

We adopt a **dual strategy** with separate approaches for error reporting infrastructure (always present) and optional debug information (controlled by flags).

### Core Principles

1. **Error reporting infrastructure is NOT optional**
   - Constraint origins, metavariable provenance, source locations always tracked
   - Required for basic usability (good error messages)
   - Not affected by debug flags

2. **Separation of concerns:** Meta-level and object-level are debugged differently
   - Error reporting: constraint graphs for meta-level, source locators for object-level
   - Debug info: traces/residuals for meta-level, waveforms for object-level

3. **Trade-off awareness:** Provide multiple debug views (accurate, complete, balanced)
   - For optional deep debugging, not basic error messages

4. **Debug info invariance:** Elaboration output must not change with/without debug flags
   - Error reporting metadata doesn't affect semantics
   - Optional debug traces don't affect semantics

5. **Liveness-based quality:** Measure debug info coverage against actual variable lifetime

6. **Residual computation:** Store expressions to recompute optimized-away values (optional)

### Strategy Overview

```
┌─────────────────────────────────────────────────────────────┐
│                    HWML Source Code                         │
│                   (examples/Counter.hwml)                   │
└────────────────┬────────────────────────────────────────────┘
                 │
                 │ Elaboration
                 ↓
┌────────────────────────────────────────────────────────────┐
│        Meta-Level Error Reporting (ALWAYS PRESENT)          │
│  • SourceInfo metadata on all AST nodes                    │
│  • Metavariable origin (created_at, created_by)            │
│  • Constraint provenance (WHY each constraint exists)      │
│  • Justification chains for type errors                    │
└────────────────┬───────────────────────────────────────────┘
                 │
                 ↓
┌────────────────────────────────────────────────────────────┐
│        Meta-Level Debug Info (OPTIONAL --debug=full)        │
│  • NbE residual expressions                                │
│  • Unification traces                                      │
│  • Scope snapshots                                         │
│  • DWARF for elaborator itself                             │
└────────────────┬───────────────────────────────────────────┘
                 │
                 │ Code Generation
                 ↓
┌────────────────────────────────────────────────────────────┐
│        Object-Level Debug Info (OPTIONAL --debug=*)         │
│  • Source locators in generated Verilog                    │
│  •   // @[Counter.hwml 42:10]                             │
│  • VCD/FSDB waveform dumps                                 │
│  • Module hierarchy preservation                           │
│  • Signal name preservation                                │
└────────────────────────────────────────────────────────────┘
```

**Key distinction:**
- **Top box** (Error Reporting) = Always present, required for usable error messages
- **Middle/Bottom boxes** (Debug Info) = Optional, controlled by `--debug` flag

---

## Meta-Level Error Reporting Infrastructure

**Note:** This section describes metadata that is **ALWAYS tracked**, regardless of debug flags. This is not "debug information" in the traditional sense—it's essential infrastructure for producing usable error messages.

### 1. Source Location Tracking

**Implementation:**
```rust
/// Attached to every AST node
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceInfo {
    pub file: SourceFileId,      // Salsa-interned
    pub start: Position,          // Line:Column
    pub end: Position,            // Line:Column
}

#[derive(Debug, Clone, Copy)]
pub struct Position {
    pub line: u32,    // 1-based
    pub column: u32,  // 0-based (UTF-8 byte offset)
}

/// All AST nodes implement this
pub trait HasSourceInfo {
    fn source_info(&self) -> Option<SourceInfo>;
    fn set_source_info(&mut self, info: SourceInfo);
}
```

**Preservation through transformations:**
```rust
// During NbE quotation
fn quote_with_source(nf: &NormalForm) -> Term {
    let mut term = quote_value(&nf.value);
    if let Some(src) = nf.source_info {
        term.set_source_info(src);  // Preserve!
    }
    term
}

// Synthesized terms

```rust
pub enum DebugView {
    Accurate,   // High fidelity, low density
    Complete,   // Low fidelity, high density
    Balanced,   // Middle ground (default)
}

// Example for a unified metavariable
match debug_view {
    Accurate => "Nat",  // Just show the solved type
    Complete => "?n where ?n := Nat (unified at line 45)",  // Show history
    Balanced => "Nat  [from ?n]",  // Show result with hint
}
```

**LSP implementation:**
```rust
fn hover_info(&self, pos: Position, view: DebugView) -> HoverInfo {
    let term = self.term_at(pos);
    match view {
        Accurate => self.show_final_type(term),
        Complete => self.show_elaboration_trace(term),
        Balanced => self.show_type_with_provenance(term),
    }
}
```

---

## Object-Level Debug Information

### 1. Source Locators in Generated Code

**Follow Chisel/FIRRTL approach:**
```verilog
module Counter(
  input clk,
  input reset,
  output [7:0] count
); // @[examples/Counter.hwml 10:1]

  reg [7:0] count_reg; // @[examples/Counter.hwml 11:5]

  always @(posedge clk) begin // @[examples/Counter.hwml 12:3]
    if (reset) // @[examples/Counter.hwml 13:5]
      count_reg <= 8'h0; // @[examples/Counter.hwml 14:7]
    else
      count_reg <= count_reg + 1; // @[examples/Counter.hwml 16:7]
  end

  assign count = count_reg; // @[examples/Counter.hwml 19:3]
endmodule
```

**Format:** `@[<file> <line>:<column>]`

**Emit on:**
- Every module declaration
- Every signal/register declaration
- Every assignment
- Every instantiation
- Every procedural block

### 2. Waveform Generation

**Auto-generate dump statements:**
```verilog
// Generated in testbench
initial begin
  `ifdef DUMP_FSDB
    $fsdbDumpfile("wave.fsdb");
    $fsdbDumpvars(0, testbench);
    $fsdbDumpMDA();  // Multi-dimensional arrays
  `elsif DUMP_VCD
    $dumpfile("wave.vcd");
    $dumpvars(0, testbench);
  `endif
end
```

**CLI options:**
```bash
hwml build --wave=fsdb  # Synopsys FSDB (requires Verdi)
hwml build --wave=vcd   # Standard VCD (default)
hwml build --wave=none  # No waveform
```

### 3. Hierarchy and Signal Preservation

**Rules:**
1. **Never flatten** module hierarchy (unless explicitly requested)
2. **Preserve signal names** from HWML source
3. **Sanitize keywords** but keep recognizable (`begin` → `_begin`)
4. **No anonymous temporaries** - every signal has a source-traceable name

**Example:**
```hwml
module ALU {
  def result : UInt<32> = add(a, b)
}

// Generated Verilog:
module ALU(...);
  wire [31:0] result;  // Good - preserved
  assign result = a + b; // @[ALU.hwml 2:23]

  // NOT: wire [31:0] _T_42;  // Bad - untraceable
endmodule
```

### 4. Bidirectional Source Mapping

**Tool to map waveform signals to source:**
```rust
pub struct SourceMapper {
    verilog_to_hwml: HashMap<SignalPath, SourceInfo>,
    hwml_to_verilog: HashMap<SourceInfo, Vec<SignalPath>>,
}

impl SourceMapper {
    // Parse @[...] comments from Verilog
    pub fn from_verilog(path: &Path) -> Result<Self>;

    // Query: "What HWML line is this signal from?"
    pub fn source_of_signal(&self, signal: &SignalPath) -> Option<SourceInfo>;

    // Query: "What signals came from this HWML line?"
    pub fn signals_from_source(&self, info: SourceInfo) -> Vec<SignalPath>;
}
```

**LSP integration:**
```rust
// LSP command: "Show in waveform"
fn show_in_waveform(&self, pos: Position) -> Result<Vec<SignalPath>> {
    let source_info = self.source_info_at(pos);
    let signals = self.mapper.signals_from_source(source_info);

    // Launch waveform viewer with signals highlighted
    self.launch_waveform_viewer(signals)?;
    Ok(signals)
}
```

---

## Debug Info Invariance

### Requirement

**Elaboration output must be identical whether or not debug info is enabled.**

```bash
# These should produce semantically identical output
hwml-elab --debug=full input.hwml -o out1.hwmli
hwml-elab --debug=none input.hwml -o out2.hwmli

# Verification tool
hwml-compare-semantics out1.hwmli out2.hwmli
# → PASS: Semantically equivalent
```

### Implementation

**Debug info as separate metadata:**
```rust
// AST node
pub struct Term {
    kind: TermKind,           // Semantic content
    ty: Option<Type>,         // Type annotation
    debug: Option<DebugInfo>, // Debug metadata (separate!)
}

// Debug info NEVER affects:
impl Hash for Term {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.kind.hash(state);
        self.ty.hash(state);
        // NOT self.debug - excluded from hashing!
    }
}

impl PartialEq for Term {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind && self.ty == other.ty
        // Debug info excluded from equality!
    }
}
```

**Testing:**
```rust
#[test]
fn test_debug_invariance() {
    let program = "def foo : Nat = 42";

    // Elaborate with full debug info
    let result1 = elaborate(program, DebugLevel::Full);

    // Elaborate with no debug info
    let result2 = elaborate(program, DebugLevel::None);

    // Semantics must be identical
    assert_eq!(result1.semantics(), result2.semantics());

    // But debug info differs
    assert_ne!(result1.debug_info(), result2.debug_info());
}
```

---

## Quality Metrics

### Liveness-Based Coverage

**Track expected vs actual debug info:**
```rust
pub struct DebugCoverage {
    // Where could variable have location?
    expected_liveness: HashMap<VarId, Vec<Range>>,

    // Where do we actually have location?
    actual_locations: HashMap<VarId, Vec<Range>>,
}

impl DebugCoverage {
    pub fn coverage(&self, var: VarId) -> f64 {
        let expected = self.expected_liveness[&var].total_range();
        let actual = self.actual_locations[&var].total_range();
        (actual as f64) / (expected as f64)
    }

    pub fn report(&self) -> CoverageReport {
        CoverageReport {
            overall_coverage: self.overall_coverage(),
            per_variable: self.per_variable_coverage(),
            gaps: self.identify_gaps(),  // Where did we lose info?
        }
    }
}
```

**Identify where debug info is lost:**
```rust
pub enum DebugLossReason {
    NbEQuotation,           // Lost during quote
    Unification,            // Metavar solved, lost origin
    ElaborationSynthesis,   // Compiler-generated
    Optimization,           // If we add optimizations later
}

pub struct DebugGap {
    pub var: VarId,
    pub range: Range,
    pub reason: DebugLossReason,
    pub suggestion: Option<String>,  // How to improve
}
```

**CLI reporting:**
```bash
$ hwml debug-coverage Counter.hwml

Debug Info Coverage Report:
  Overall: 87.3%
  Variables: 92.1%
  Types: 95.4%

Gaps identified:
  - Variable 'n' (line 12): 45.2% coverage
    Reason: Lost during NbE quotation
    Suggestion: Preserve SourceInfo in NormalForm

  - Type parameter 'α' (line 25): 0% coverage
    Reason: Erased during elaboration
    Suggestion: Keep residual type in debug info
```

---

## Implementation Phases

### Phase 1: Foundation (Immediate)

**Goal:** Basic source location tracking operational

1. **Complete SourceInfo migration**
   - Finish Line:Column implementation (already designed)
   - Attach to all AST nodes
   - Test preservation through parser → elaborator

2. **Implement HasSourceInfo trait**
   - All term types
   - All type types
   - All declaration types

3. **LSP integration**
   - Hover shows source location
   - Go-to-definition uses source ranges
   - Diagnostics with accurate positions

4. **Basic Verilog source locators**
   - Emit `@[file line:col]` comments
   - On modules, signals, assignments

**Acceptance criteria:**
- All AST nodes have SourceInfo
- Error messages show accurate locations
- LSP navigation works
- Generated Verilog has source comments

### Phase 2: Meta-Level Debug (3-6 months)

**Goal:** Comprehensive elaboration debugging

1. **Metavariable tracking**
   - Origin tracking
   - Constraint provenance
   - Solver state visualization

2. **Residual computation**
   - Store original expressions
   - Track dependencies
   - Debugger can recompute

3. **NbE preservation**
   - SourceInfo through quote/unquote
   - Track term transformations
   - Blame assignment for synthesis

4. **Debug views**
   - Accurate mode
   - Complete mode
   - Balanced mode (default)

5. **Coverage metrics**
   - Liveness-based measurement
   - Gap identification
   - Quality reporting

**Acceptance criteria:**
- Metavariables traceable to origin
- Can debug "why is ?m stuck?"
- Coverage > 85%
- Debug info doesn't affect elaboration output

### Phase 3: Object-Level Debug (6-12 months)

**Goal:** Waveform debugging integration

1. **Waveform generation**
   - VCD support (standard)
   - FSDB support (if VCS available)
   - Auto-generated dump statements

2. **Source mapping tool**
   - Parse Verilog source locators
   - Bidirectional mapping
   - Query interface

3. **LSP integration**
   - "Show in waveform" command
   - Signal highlighting
   - Jump from waveform to source (if viewer supports)

4. **Hierarchy preservation**
   - Never flatten (by default)
   - Signal name preservation
   - Module structure intact

**Acceptance criteria:**
- Can trace waveform signal to HWML source
- Can find signals from HWML line
- Waveforms viewable in standard tools
- Hierarchy matches HWML structure

### Phase 4: Advanced Features (Future)

**Goal:** State-of-the-art debug experience

1. **DWARF generation** (optional)

   - For elaborator itself (meta-level)
   - If using CIRCT/LLVM backend
   - Enables GDB/LLDB debugging of elaboration

2. **Synthesis debug mapping**
   - Track through synthesis transformations
   - Map optimized netlist back to source
   - Integration with SynAlign-style tools

3. **Time-travel debugging**
   - Record elaboration traces
   - Replay elaboration steps
   - Inspect historical metavariable state

4. **Dependent type extensions to DWARF**
   - Custom DIEs for dependent types
   - Type-level computation tracking
   - Metavariable representation

**Acceptance criteria:**
- Can debug elaborator with GDB/LLDB (if using CIRCT)
- Can trace optimized hardware back to source
- Can replay elaboration for debugging

---

## Alternatives Considered

### Alternative 1: Single Debug Info Approach

**Idea:** Use DWARF for everything (both meta-level and object-level)

**Rejected because:**
- Hardware debugging fundamentally different from software
- DWARF doesn't map well to waveforms
- Waveform viewers don't consume DWARF
- Would require custom tooling, defeating purpose

### Alternative 2: No Debug Info

**Idea:** Rely on existing tools (Verilog debuggers, GDB for elaborator)

**Rejected because:**
- Poor developer experience
- Hard to debug type errors
- Can't trace generated hardware to source
- Metavariables completely opaque
- Research shows 60-70% information loss is unacceptable

### Alternative 3: "Optimized Out" Everywhere

**Idea:** Don't try to preserve debug info through transformations

**Rejected because:**
- Makes elaboration debugging nearly impossible
- Research shows residual computation is feasible
- Dependent types enable storing type-level expressions
- Modern tools can do better

### Alternative 4: Perfect Debug Info

**Idea:** Guarantee 100% debug info coverage always

**Rejected because:**
- Research proves this is ill-posed (no perfect answer)
- Unnecessary overhead for production code
- Better to provide trade-offs (accurate/complete/balanced)
- 85%+ coverage is achievable and sufficient

---

## Consequences

### Positive

1. **Excellent elaboration debugging**
   - Metavariables traceable to origin
   - Can answer "why is type checking stuck?"
   - Constraint visualization

2. **Hardware traceability**
   - Waveform signals map to HWML source
   - Works with existing tools (VCS, Verdi, ModelSim)
   - No custom infrastructure required

3. **Research-backed design**
   - Based on ASPLOS, PLDI, Onward! papers
   - Avoids known pitfalls (CCMD, completeness)
   - Embraces ill-posed nature

4. **Future-proof**
   - Extensible to DWARF if needed
   - Can add synthesis mapping later
   - Residual computation framework in place

5. **Measurable quality**
   - Liveness-based metrics
   - Gap identification
   - Continuous improvement

### Negative

1. **Implementation complexity**
   - Dual strategies require separate systems
   - Metavariable tracking adds overhead
   - Coverage measurement needs infrastructure

2. **Storage overhead**
   - Residual expressions take memory
   - Full debug info larger than no debug info
   - Mitigated by: optional, disabled in production

3. **Learning curve**
   - Users must understand three debug views
   - Meta-level vs object-level distinction
   - Metavariables and constraints are complex

4. **Tool dependencies**
   - Waveform viewing requires external tools
   - FSDB requires Verdi license
   - Not self-contained

### Neutral

1. **Trade-offs explicit**
   - Users choose accurate/complete/balanced
   - No "one size fits all"
   - Documented why perfect debug info impossible

2. **Incremental delivery**
   - Phase 1 useful alone
   - Phases 2-4 enhance but not required
   - Can ship with minimal debug info initially

---

## Testing Strategy

### Unit Tests

```rust
#[test]
fn test_source_info_preservation() {
    let term = parse("def x : Nat = 42");
    let elaborated = elaborate(term);

    // Source info preserved through elaboration
    assert_eq!(
        elaborated.source_info(),
        Some(SourceInfo { file, start: (1, 0), end: (1, 16) })
    );
}

#[test]
fn test_metavar_tracking() {
    let term = parse("def id = λ x => x");
    let (elaborated, ctx) = elaborate_with_context(term);

    // Metavar for implicit type parameter
    let metavar = ctx.metavars().first();
    assert_eq!(metavar.origin, MetaOrigin::ImplicitArgument { .. });
    assert!(metavar.created_at.is_some());
}
```

### Integration Tests

```bash
# Test debug info invariance
hwml test --debug-invariance examples/*.hwml

# Test coverage
hwml test --coverage-check --min-coverage=85 examples/*.hwml

# Test source mapping
hwml test --source-mapping examples/*.hwml
```

### Property-Based Tests

```rust
#[proptest]
fn debug_info_doesnt_affect_semantics(program: HwmlProgram) {
    let result1 = elaborate(program.clone(), DebugLevel::Full);
    let result2 = elaborate(program.clone(), DebugLevel::None);

    prop_assert_eq!(result1.semantics(), result2.semantics());
}

#[proptest]
fn source_info_never_none_for_user_code(user_term: Term) {
    prop_assert!(user_term.source_info().is_some());
}
```

---

## Monitoring and Metrics

### CI Metrics

Track in continuous integration:

```yaml
metrics:
  debug_coverage:
    overall: "> 85%"
    per_file: "> 80%"

  invariance_tests:
    passing: "100%"

  source_mapping_accuracy:
    verilog_comments: "> 95%"
    signal_names_preserved: "> 90%"
```

### Developer Metrics

```bash
# Show coverage for file
$ hwml debug-coverage Counter.hwml
Overall: 87.3%

# Show gaps
$ hwml debug-gaps Counter.hwml
12 gaps found, suggestions:
  - Add SourceInfo to synthesized terms (5 instances)
  - Preserve through NbE (3 instances)

# Validate invariance
$ hwml check-invariance Counter.hwml
✓ PASS: Debug info doesn't affect elaboration
```

---

## Documentation Requirements

### User Documentation

1. **Getting Started with Debugging**
   - How to read error messages
   - Using LSP for navigation
   - Understanding metavariables

2. **Waveform Debugging Guide**
   - Generating VCD/FSDB
   - Mapping signals to source
   - Using with Verdi/ModelSim/GTKWave

3. **Debug Views Guide**
   - When to use accurate/complete/balanced
   - Interpreting residual expressions
   - Understanding coverage reports

### Developer Documentation

1. **Debug Info Implementation Guide**
   - How to preserve SourceInfo
   - Adding residual computation
   - Testing debug info invariance

2. **Coverage Improvement Guide**
   - Identifying gaps
   - Improving preservation
   - Measuring impact

---

## Related Decisions

- [[ADR-001-lcf-kernel]] - Error reporting uses SourceInfo
- [[ADR-002-bidirectional-typing]] - Type checking preserves locations
- [[ADR-004-mvs-package-manager]] - Interface files need debug info

## References

### Research Papers - Debug Info (Optimization)

- Kell & Stinnett (Onward! 2024): "Debugging Optimised Code: Ill-Posed, but Not Impossible"
- Assaiante et al (ASPLOS 2023): "Where Did My Variable Go?"
- Wang et al (ASPLOS 2023): "Compilation Consistency Modulo Debug Information"
- Li, Wu, Xie (PLDI 2020): "Debug Information Validation for Optimized Code"

### Research Papers - Error Messages (Elaboration)

- Zhang & Myers (ICSE 2014): "Toward General Diagnosis of Static Errors" (SHErrLoc)
- Raghu, Bhanuka, Trieu, Chin (POPL 2024): "Getting into the Flow: Towards Better Type Error Messages"
- Pavlinovic, King, Wies (2015): "Finding Minimum Type Error Sources" (SMT-based)
- Seidel, Jhala, Weimer (2016): "Dynamic Witnesses for Static Type Errors"

### HWML Wiki Research

- [[research/elaboration-error-messages]] - Constraint origins, metavar provenance, global diagnosis
- [[research/debug-info-systems]] - DWARF, PDB, source maps
- [[research/hardware-debug-info]] - VCS, FSDB, waveforms, Chisel
- [[research/llvm-debug-info-internals]] - LLVM implementation details
- [[research/debug-info-research-modern]] - Modern academic research

### External References

- DWARF 5 Standard: https://dwarfstd.org/dwarf5std.html
- Chisel Source Locators: https://www.chisel-lang.org/docs/explanations/source-locators
- LLVM Debug Info: https://llvm.org/docs/SourceLevelDebugging.html

---

## Decision Outcome

**Chosen:** Two-tier strategy: Essential error reporting infrastructure (always) + Optional debug information (flags)

**Rationale:**
1. **Error reporting is NOT optional** - Modern type systems (Rust, Lean, GHC, Agda) all track constraint/metavariable provenance for error messages
2. **Separation of concerns** - Distinguish "data needed for good errors" from "data for deep debugging"
3. **Research-backed** - SHErrLoc, flow-based errors, and all modern elaborators use this approach
4. **Hardware and software debugging are fundamentally different** - Waveforms vs execution traces
5. **Ill-posed nature requires trade-offs** - Multiple debug views for different needs
6. **Feasible to implement incrementally** - Error reporting first, advanced features later

**Critical clarification:**
- **Metavariable `created_at`, `created_by`, `constrained_by`** → ERROR REPORTING (always present)
- **Constraint origins** → ERROR REPORTING (always present)
- **Source locations** → ERROR REPORTING (always present)
- **Unification traces, NbE residuals, scope snapshots** → DEBUG INFO (optional with `--debug=full`)
- **Verilog source locators, waveforms** → DEBUG INFO (optional with `--debug=*`)

**Next Steps:**
1. Complete Phase 1 (source location tracking foundation)
2. Implement metavariable provenance tracking (error reporting)
3. Implement constraint origin tracking (error reporting)
4. Implement global constraint diagnosis
5. Add optional debug features (traces, residuals, waveforms)

**Status:** Proposed → Awaiting approval → Implementation

---

**Confidence:** High

This ADR is backed by comprehensive research including:
- **Elaboration/Error Messages:** SHErrLoc, flow-based errors (POPL 2024), Rust/Lean/GHC/Agda implementations
- **Debug Info Optimization:** ASPLOS 2023, PLDI 2020, Onward! 2024
- **LLVM Implementation:** Production debug info preservation
- **Hardware Debugging:** Chisel, VCS, Verdi best practices

The distinction between error reporting infrastructure and optional debug information is critical and matches industry practice (Rust's `ObligationCause` is always present, DWARF is optional).
```

### 2. Metavariable Provenance Tracking

**CRITICAL: This is ERROR REPORTING INFRASTRUCTURE, not optional debug info.**

Research shows all modern type systems (Rust, Lean 4, GHC, Agda) track metavariable provenance to produce good error messages. Without this, users get "Cannot solve ?m" which is useless.

**Always track:**
```rust
pub struct MetaEntry {
    pub id: MetaId,
    pub ty: RcTy,
    pub solution: Option<RcTerm>,

    // ERROR REPORTING (always tracked):
    pub created_at: Location,
    pub created_by: MetaOrigin,
    pub constrained_by: Vec<ConstraintWithOrigin>,
}

pub enum MetaOrigin {
    ImplicitArgument {
        function_name: String,
        function_loc: Location,
        param_name: String,
        param_index: usize,
    },
    TypeInference {
        expression: Location,
        reason: String,  // "return type", "function argument", etc.
    },
    PlaceholderType {
        annotation_hole: Location,  // User wrote `_`
    },
    UnificationVariable { equation: Location },
    InstanceSearch {
        class_name: String,
        required_at: Location,
    },
}

pub struct ConstraintWithOrigin {
    pub constraint: UnificationConstraint,
    pub source: Location,
    pub origin: ConstraintOrigin,  // WHY this constraint exists
}

pub enum ConstraintOrigin {
    FunctionApplication { function: Location, arg_index: usize, arg: Location },
    ReturnType { declared: Location, returned: Location },
    PatternMatch { scrutinee: Location, pattern: Location },
    FieldAccess { struct_name: String, field_name: String, access: Location },
    // ... many more
}
```

**Error message with provenance:**
```
error: cannot solve metavariable ?n
  ┌─ Counter.hwml:10:5
  │
10│   val replicate n false
  │       ^^^^^^^^^ implicit argument to 'replicate'
  │
  = note: ?n was created for implicit type parameter to 'replicate'
  = note: ?n is constrained by:
    • ?n ~ 8             (from literal at line 12)
    • ?n ~ width(x)      (from field access at line 15)
    • width(x) ~ 16      (from type annotation at line 3)
  = note: conflicting constraints: 8 ≠ 16
  = help: check the width annotation at line 3
```

**Without provenance (unusable):**
```
error: cannot solve metavariable ?n
```

**Justification:** Based on research into Rust's `ObligationCause`, Lean 4's justifications, Agda Issue #2073, and SHErrLoc constraint graph analysis. See [[research/elaboration-error-messages]] for details.

### 3. Constraint Collection & Global Diagnosis

**Don't fail at first error—collect all constraints, then diagnose:**

```rust
pub struct ElaborationContext {
    constraints: Vec<ConstraintWithOrigin>,
    // ... other fields
}

impl ElaborationContext {
    // DON'T fail immediately:
    pub fn add_constraint(&mut self, constraint: UnificationConstraint, origin: ConstraintOrigin) {
        self.constraints.push(ConstraintWithOrigin { constraint, origin, source: self.current_span });
    }

    // DO collect all, then diagnose:
    pub fn finalize(&mut self) -> Result<(), Vec<ElabError>> {
        match self.solve_constraints() {
            Ok(solution) => Ok(()),
            Err(unsatisfiable) => {
                // Global diagnosis: find minimal unsatisfiable subset
                let errors = self.diagnose_constraint_conflicts(unsatisfiable);
                Err(errors)
            }
        }
    }

    fn diagnose_constraint_conflicts(&self, unsat: Vec<ConstraintId>) -> Vec<ElabError> {
        // Use constraint origins to explain error
        // Show data flow: "value of type A flows from X to Y which expects B"
        // Based on SHErrLoc and flow-based error research
    }
}
```

**Justification:** Based on SHErrLoc (Cornell), flow-based errors (POPL 2024), and SMT-based localization research. Error location depends on global constraint analysis, not failure order.

---

## Meta-Level Optional Debug Information

**Note:** This section describes data that is **OPTIONALLY tracked** with `--debug=full`. This is for debugging the elaborator itself, not for user error messages.

### 4. Residual Computation (Optional)

**Store how to recompute values:**
```rust
pub struct ResidualInfo {
    pub original_term: Term,
    pub normalized_value: Value,
    pub recompute_expr: Option<String>,  // Human-readable
    pub dependencies: Vec<VarId>,         // What's needed to recompute
}

// Example
ResidualInfo {
    original_term: Term::App(replicate, [n, false]),
    normalized_value: Value::Vec([false; 8]),
    recompute_expr: Some("replicate n false where n = 8"),
    dependencies: vec![n_var],
}
```

**Debugger can show:**
```
x: Vec Bit 8  [recomputable from 'replicate n false' where n = 8]
```

### 5. Debug Views (Embrace Ill-Posed Nature)

**Provide three views:**

**Accurate mode:** Only show when confident
