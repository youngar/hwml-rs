# Debug Information Implementation Plan

**Date:** 2026-05-03
**Related ADR:** [[wiki/decisions/ADR-005-debug-information]]
**Status:** Planning - Based on Codebase Exploration

---

## Executive Summary

HWML has **foundational infrastructure** (~30% complete) but needs significant work to match ADR-005 requirements. The main gap is migrating from byte-offset-based locations to native Line:Column representation throughout the compiler pipeline.

**Timeline:** ~18 weeks (4.5 months) across 3 phases
**Current State:** Source tracking exists but uses wrong representation; metavariable tracking missing; Verilog locators not implemented

---

## Gap Analysis Summary

| Component | Exists | Missing | Severity |
|-----------|--------|---------|----------|
| **Source Location** | Byte offsets, `LineInfo` util | Line:Column native, Core IR locations | HIGH |
| **Metavariable Tracking** | Basic `MetaEntry` | Origin, constraint provenance | MEDIUM |
| **Error Reporting** | Locations in errors | Context snippets, meta history | MEDIUM |
| **Verilog Locators** | CIRCT backend exists | Source comments, waveforms | MEDIUM |
| **Debug Invariance** | Nothing | Separation, flags, tests | MEDIUM |
| **Coverage Metrics** | Nothing | Liveness tracking | LOW |

---

## Phase 1: Source Location Foundation (3-4 weeks)

**Goal:** All AST nodes have native Line:Column locations

### Current State

✅ **Existing:**
- `SourceFileId<'db>` - Salsa-interned file IDs
- `SourceInfo<'db>` enum (File/Synthetic)
- `LineInfo` utility (byte ↔ line:col conversion)
- Surface syntax nodes have `loc: Range<usize>`
- Parser tracks byte positions

❌ **Problems:**
- `SourceRange<'db>` uses `Range<usize>` (byte offsets)
- Core IR `Syntax<'db>` has NO location fields
- Parser emits byte offsets, conversion is lazy
- Elaboration loses source information

### Required Changes

**1. New Location Type** (3 days)

Create `crates/hwml-core/src/source_range.rs`:

```rust
#[salsa::interned]
pub struct Location<'db> {
    pub data: LocationData<'db>,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum LocationData<'db> {
    FileLineColRange {
        file: SourceFileId<'db>,
        start_line: u32,    // 1-based
        start_column: u32,  // 0-based byte offset in line
        end_line: u32,
        end_column: u32,
    },
    Synthetic {
        label: Word<'db>,
    },
}

// Compatibility during migration
pub type SourceRange<'db> = Location<'db>;
```

**2. Update Parser** (3 days)

Modify `crates/hwml-core/src/syn/parse.rs`:

```rust
pub fn parse<'db>(
    db: &'db dyn Database,
    file: SourceFileId<'db>,
    text: &str,
) -> Result<Vec<Statement<'db>>, ParseError> {
    let line_info = LineInfo::new(text);

    // Convert during parse, not lazily
    let to_location = |range: Range<usize>| -> Location<'db> {
        let (start_line, start_col) = line_info.loc(range.start);
        let (end_line, end_col) = line_info.loc(range.end);

        Location::new(db, LocationData::FileLineColRange {
            file,
            start_line: start_line as u32,
            start_column: start_col as u32,
            end_line: end_line as u32,
            end_column: end_col as u32,
        })
    };

    // Use in all parser actions
}
```

**3. Add Locations to Core IR** (5 days)

Update `crates/hwml-core/src/syn/syntax.rs`:

```rust
pub enum Syntax<'db> {
    Lit(Literal, Location<'db>),
    Var(Var<'db>, Location<'db>),
    App {
        fun: RcSyntax<'db>,
        args: Vec<RcSyntax<'db>>,
        location: Location<'db>,  // NEW
    },
    // ... all variants get location
}

impl<'db> Syntax<'db> {
    pub fn location(&self) -> Location<'db> {
        match self {
            Syntax::Lit(_, loc) => *loc,
            Syntax::Var(_, loc) => *loc,
            Syntax::App { location, .. } => *location,
            // ...
        }
    }
}
```

**4. Preserve Through Elaboration** (5 days)

Update `crates/hwml-elab/src/elab.rs` to thread locations:

```rust
fn elaborate_expr(
    &mut self,
    surface: &SurfaceExpr,
    location: Location<'db>,
) -> Result<RcSyntax<'db>, ElabError<'db>> {
    let core = match surface {
        SurfaceExpr::Lit(lit) => {
            Syntax::Lit(lit.clone(), location)

Find all `fresh_meta()` calls and provide origin information.

**4. Enhanced Error Display** (5 days)

```rust
// crates/hwml-elab/src/error.rs

impl<'db> ElabError<'db> {
    pub fn display_with_context(
        &self,
        db: &'db dyn Database,
    ) -> String {
        match self {
            ElabError::UnsolvedMeta { meta, span } => {
                let entry = /* get from state */;
                format!(
                    "error: unsolved metavariable ?{}\n  \
                     created at: {}\n  \
                     reason: {}\n  \
                     constrained by:\n{}",
                    meta.0,
                    format_location(db, entry.created_at),
                    format_origin(&entry.created_by),
                    format_constraints(db, &entry.constrained_by),
                )
            },
            // ... other variants
        }
    }
}
```

**5. Verilog Source Locators** (7 days)

Thread locations through CIRCT translation:

```rust
// crates/hwml-circt/src/translate.rs

fn translate_constant<'db>(
    ctx: &CirctContext,
    db: &'db dyn Database,
    constant: &ConstantDecl<'db>,
) -> Result<...> {
    // Get location from Syntax
    let loc = constant.body.location();

    // Convert to MLIR location
    let mlir_loc = convert_to_mlir_location(db, ctx, loc);

    // Use in operations
    let module_op = OperationBuilder::new("hw.module", mlir_loc)
        .build()?;
}
```

Post-process Verilog to add comments:

```rust
// Insert: // @[file.hwml 42:10]
fn annotate_verilog_with_sources(
    verilog: &str,
    source_map: &HashMap<String, Location<'db>>,
) -> String {
    // Pattern match and insert comments
}
```

**6. Waveform Generation** (3 days)

```rust
// crates/hwml-circt/src/testbench.rs (NEW)

pub enum WaveFormat { VCD, FSDB, None }

pub fn generate_testbench_with_waves(
    module_name: &str,
    format: WaveFormat,
) -> String {
    match format {
        WaveFormat::VCD => {
            format!(r#"
  initial begin
    $dumpfile("wave.vcd");
    $dumpvars(0, tb);
  end
"#)
        },
        // ... FSDB variant
    }
}
```

**7. Debug Views** (5 days)

Implement accurate/complete/balanced modes for LSP hover.

### Acceptance Criteria

- [ ] Metavariables show "created at X for reason Y"
- [ ] Errors display constraint provenance
- [ ] Generated Verilog has `@[file line:col]` comments
- [ ] Can generate VCD waveforms
- [ ] LSP hover shows debug views

**Estimated:** 33 days (~7 weeks with buffer)

---

## Phase 3: Debug Invariance & Tooling (6-8 weeks)

**Goal:** Ensure debug info doesn't affect semantics

### Required Changes

**1. Debug Level Flag** (1 day)

```rust
// crates/hwml/src/main.rs

#[derive(Parser)]
struct Args {
    #[arg(long, default_value = "balanced")]
    debug_level: DebugLevel,
}

pub enum DebugLevel {
    None,      // No debug info
    Balanced,  // Default trade-off
    Full,      // Maximum info
}
```

**2. Separate Debug Metadata** (5 days)

Option: Wrapper that excludes debug from Hash/PartialEq

```rust
pub struct DebuggedSyntax<'db> {
    pub semantic: RcSyntax<'db>,
    pub debug: Option<SyntaxDebugInfo<'db>>,
}

impl Hash for DebuggedSyntax<'db> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.semantic.hash(state);
        // NOT self.debug!
    }
}
```

**3. Invariance Tests** (3 days)

```rust
#[test]
fn test_debug_info_invariance() {
    let program = "def foo : Nat = 42";

    let result_full = elaborate(program, DebugLevel::Full);
    let result_none = elaborate(program, DebugLevel::None);

    assert_eq!(
        result_full.semantics(),
        result_none.semantics(),
        "Debug info changed elaboration output!"
    );
}
```

**4. Source Mapping Tool** (7 days)

Bidirectional mapping between Verilog signals and HWML source:

```rust
// crates/hwml-circt/src/source_map.rs (NEW)

pub struct SourceMapper<'db> {
    verilog_to_hwml: HashMap<SignalPath, Location<'db>>,
    hwml_to_verilog: HashMap<Location<'db>, Vec<SignalPath>>,
}

impl SourceMapper {
    pub fn from_verilog(verilog: &str) -> Result<Self> {
        // Parse @[...] comments
    }

    pub fn source_of_signal(&self, signal: &SignalPath) -> Option<Location<'db>> {
        self.verilog_to_hwml.get(signal).copied()
    }
}
```

**5. LSP Integration** (5 days)

Add "Show in Waveform" command:

```rust
// crates/hwml-lsp-server/src/main.rs

fn show_in_waveform(&self, pos: Position) -> Result<Vec<SignalPath>> {
    let source_info = self.source_info_at(pos);
    let signals = self.mapper.signals_from_source(source_info);

    // Launch waveform viewer
    self.launch_waveform_viewer(signals)?;
    Ok(signals)
}
```

**6. Coverage Metrics** (7 days)

```rust
// crates/hwml-elab/src/coverage.rs (NEW)

pub struct DebugCoverage {
    expected_liveness: HashMap<VarId, Vec<Range>>,
    actual_locations: HashMap<VarId, Vec<Range>>,
}

impl DebugCoverage {
    pub fn coverage(&self, var: VarId) -> f64 {
        let expected = self.expected_liveness[&var].total_range();
        let actual = self.actual_locations[&var].total_range();
        (actual as f64) / (expected as f64)
    }
}
```

**7. CLI Reporting** (3 days)

```bash
$ hwml debug-coverage Counter.hwml

Debug Info Coverage Report:
  Overall: 87.3%
  Variables: 92.1%

Gaps:
  - Variable 'n' (line 12): 45% coverage
    Reason: Lost during NbE quotation
```

### Acceptance Criteria

- [ ] Debug level flag controls info generation
- [ ] Debug info excluded from Hash/PartialEq
- [ ] Invariance tests pass (100%)
- [ ] Can map waveform signals ↔ HWML source
- [ ] Coverage measurement works (target: >85%)

**Estimated:** 33 days (~7 weeks with buffer)

---

## Risk Mitigation

| Risk | Mitigation |
|------|------------|
| Location migration breaks code | Incremental migration with compatibility layer (`SourceRange = Location`) |
| CIRCT lacks location support | Fall back to post-processing Verilog for source comments |
| Performance overhead | Make debug info optional via flags, lazy computation where possible |
| Invariance test failures | Implement early in Phase 1, fix issues before Phase 2 |

---

## Resource Estimates

**Total Development Time:** ~18 weeks (4.5 months)
- Phase 1: 4 weeks
- Phase 2: 7 weeks
- Phase 3: 7 weeks

**Skills Required:**
- Rust (advanced - Salsa, lifetimes, type system)
- Compiler internals (elaboration, type checking, NbE)
- MLIR/CIRCT (for location threading)
- Verilog/HDL tooling

**Testing:**
- Property-based testing (proptest)
- Integration tests for full pipeline
- LSP protocol testing

---

## Success Metrics

**Phase 1:**
- ✓ 100% of AST nodes have `Location<'db>`
- ✓ 0 test regressions
- ✓ LSP shows line:column accurately

**Phase 2:**
- ✓ >80% metavariables have origin
- ✓ Errors show constraint provenance
- ✓ 95% of generated Verilog has source locators

**Phase 3:**
- ✓ Debug invariance: 100% tests pass
- ✓ Coverage: >85% overall
- ✓ Signal preservation: >90%

---

## Files to Modify

### Phase 1 (Foundation)
- `crates/hwml-core/src/source_range.rs` - New Location type
- `crates/hwml-core/src/syn/syntax.rs` - Add location fields
- `crates/hwml-core/src/syn/parse.rs` - Compute line:col during parse
- `crates/hwml-surface/src/syntax.rs` - Update to use Location
- `crates/hwml-elab/src/elab.rs` - Preserve through elaboration
- `crates/hwml-lsp-server/src/main.rs` - Use native locations

### Phase 2 (Meta-Level)
- `crates/hwml-elab/src/meta.rs` - Extend MetaEntry
- `crates/hwml-elab/src/state.rs` - Update fresh_meta
- `crates/hwml-elab/src/error.rs` - Enhanced error display
- `crates/hwml-circt/src/translate.rs` - Thread locations
- `crates/hwml-circt/src/export.rs` - Annotate Verilog
- `crates/hwml-circt/src/testbench.rs` - NEW (waveforms)

### Phase 3 (Invariance)
- `crates/hwml/src/main.rs` - Debug level flag
- `crates/hwml-core/src/syn/syntax.rs` - Separate debug metadata
- `crates/hwml-elab/src/tests.rs` - Invariance tests
- `crates/hwml-circt/src/source_map.rs` - NEW (mapping tool)
- `crates/hwml-lsp-server/src/main.rs` - "Show in waveform" command
- `crates/hwml-elab/src/coverage.rs` - NEW (metrics)

---

## Next Actions

1. ✅ Review this implementation plan
2. ⬜ Approve Phase 1 start
3. ⬜ Create tracking issues for each phase
4. ⬜ Begin Location<'db> implementation
5. ⬜ Set up CI metrics for debug coverage

---

**Related Documents:**
- [[wiki/decisions/ADR-005-debug-information]] - The architectural decision
- Sub-agent exploration report (2026-05-03) - Detailed current state analysis
}
```

**5. Update LSP Integration** (2 days)

Modify `crates/hwml-lsp-server/src/main.rs` to use native line:col.

**6. Testing** (2 days)

Add tests verifying location preservation.

### Acceptance Criteria

- [ ] All `Syntax<'db>` nodes have `Location<'db>`
- [ ] Parser emits line:column during parse (not lazy)
- [ ] Elaboration preserves locations
- [ ] LSP diagnostics show accurate positions
- [ ] All existing tests pass

**Estimated:** 22 days (~4 weeks with buffer)

---

## Phase 2: Meta-Level Debug (6-8 weeks)

**Goal:** Metavariable origin tracking + Verilog source locators

### Current State

✅ **Existing:**
- `MetaId`, `MetaEntry<'db>`, `SolverState<'db>`
- Basic metavariable allocation
- CIRCT backend with translation

❌ **Problems:**
- No origin tracking (where/why meta created)
- No constraint provenance
- Verilog has no source comments
- No waveform dumps

### Required Changes

**1. Extend MetaEntry** (3 days)

```rust
// crates/hwml-elab/src/meta.rs

pub struct MetaEntry<'db> {
    pub id: MetaId,
    pub ty: RcTy<'db>,
    pub arity: usize,
    pub solution: Option<MetaSolution<'db>>,
    pub kind: MetaKind,

    // NEW:
    pub created_at: Location<'db>,
    pub created_by: MetaOrigin<'db>,
    pub constrained_by: Vec<Constraint<'db>>,
}

pub enum MetaOrigin<'db> {
    ImplicitArgument { function: Location<'db>, param_index: usize },
    TypeInference { expression: Location<'db> },
    UnificationVariable { equation: Location<'db> },
    Elaboration { reason: String, location: Location<'db> },
}

pub struct Constraint<'db> {
    pub id: ConstraintId,
    pub kind: ConstraintKind,
    pub source: Location<'db>,
}
```

**2. Update fresh_meta** (2 days)

Change signature to require origin:

```rust
pub fn fresh_meta(
    &mut self,
    ty: RcTy<'db>,
    arity: usize,
    kind: MetaKind,
    created_at: Location<'db>,     // NEW
    created_by: MetaOrigin<'db>,   // NEW
) -> MetaId
```

**3. Update Call Sites** (5 days)

