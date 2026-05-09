# HWML Big Picture: Complete Pipeline Architecture

**Date:** 2026-05-08  
**Status:** Architecture Overview  
**Context:** How elaboration, diagnostics, and proof distillation fit together  
**See Also:** `research/proof-distillation-survey.md`, `research/diagnostic-framework-design.md`

---

## Executive Summary

HWML's architecture follows the universal pattern of modern proof assistants with hardware-specific enhancements:

```
Source Code → Elaboration (with trace) → Diagnostics → Proof Terms → Kernel → Accept/Reject
                    ↓                        ↓              ↓
              ElabTrace              Post-Process     Export Proofs
                    ↓                        ↓              ↓
              ML Training             User-Friendly    Cross-Check
                                        Errors
```

**Key Principles:**
1. **Separation of concerns** - Untrusted elaboration, trusted kernel
2. **Observability** - Record everything during elaboration
3. **User experience** - Post-process errors for clarity
4. **Verifiability** - Generate independently checkable proof terms
5. **Hardware focus** - Proof-carrying modules, certified synthesis

---

## The Complete Pipeline

### Stage 1: Parsing & Desugaring

**Input:** Raw source code (`.hwml` files)

**Process:**
```
Raw Text → Lexer → Parser → Concrete Syntax Tree (CST)
                                    ↓
                           Desugaring Pass
                                    ↓
                           Abstract Syntax Tree (AST)
```

**Output:** AST with source spans preserved

**Current State:** ✅ Implemented (tree-sitter based)

**Key Feature:** Preserve all source locations for diagnostics

---

### Stage 2: Elaboration (The Heavy Lifting)

**Input:** AST with holes, implicit args, type inference needed

**Process:**
```
                    ┌─────────────────────────────────┐
                    │   Elaboration Pipeline          │
                    │                                 │
   AST              │  ┌──────────────────────────┐   │
    │               │  │ Bidirectional Type Check │   │
    ├──────────────>│  │  • Synthesis (⇒)         │   │
    │               │  │  • Checking (⇐)          │   │
    │               │  └──────────┬───────────────┘   │
    │               │             ↓                    │
    │               │  ┌──────────────────────────┐   │
    │               │  │ Constraint Generation    │   │
    │               │  │  • Unification           │   │
    │               │  │  • Subtyping             │   │
    │               │  └──────────┬───────────────┘   │
    │               │             ↓                    │
    │               │  ┌──────────────────────────┐   │
    │               │  │ Constraint Solving       │   │
    │               │  │  • Provenance tracking   │   │
    │               │  │  • Error collection      │   │
    │               │  └──────────┬───────────────┘   │
    │               │             ↓                    │
    │               │  ┌──────────────────────────┐   │
    │               │  │ Metavariable Instantiation│  │
    │               │  │  • Fill in inferred types│   │
    │               │  │  • Resolve implicits     │   │
    │               │  └──────────┬───────────────┘   │
    │               │             ↓                    │
    ↓               └─────────────┼─────────────────┘
                                  ↓
         ┌────────────────────────┴────────────────────────┐
         │                                                  │
         ↓                                                  ↓
  Elaborated AST                                   ElaborationTrace
  (may have errors)                                (full recording)
```

**Output:**
1. **Elaborated AST** - With types resolved, implicits filled
2. **ElaborationTrace** - Complete record of all decisions
3. **Error Collection** - All problems found (lenient mode)

**Current State:** 🔄 Partially implemented
- ✅ Bidirectional type checking exists
- ✅ Constraint solving exists
- ✅ Provenance tracking exists
- ❌ Full trace recording needs implementation
- ❌ Lenient error collection needs extension

**Key Feature:** RAII Trace Guards for backtrace
```rust
fn check_function(&self, func: &Function) -> Result<Type, ElabError> {
    let _guard = TraceGuard::new(self, TraceEntry::CheckingFunction {
        name: func.name.clone(),
        span: func.span,
    });
    // All errors inside include this in backtrace!
    self.check_body(&func.body)
}
```

---

### Stage 3: Error Post-Processing (Diagnostics)

**Input:** Vec<ElabError<'db>> + ElaborationTrace

**Process:**
```
Vec<ElabError>
      │
      ├─> Convert to Diagnostic objects
      │
      ├─> Deduplication
      │     (Remove identical errors)
      │
      ├─> Cascading Analysis
      │     (Find root causes via provenance graph)
      │
      ├─> Pattern Detection
      │     (Recognize common mistakes)
      │
      ├─> Suggestion Generation
      │     (Auto-fix proposals)
      │
      ├─> Intelligent Sorting
      │     (By severity → file → line → column)
      │
      └─> Gather Source Files
            (For rendering)
      │
      ↓
DiagnosticSet<'db>
```

**Output:** DiagnosticSet ready for rendering

**Current State:** ❌ Not implemented (designed in wiki)

**Key Feature:** Use provenance graph for cascading error analysis
```rust
fn find_root_causes(errors: &[ElabError]) -> Vec<ErrorCascade> {
    // Build dependency graph from constraint provenance
    let graph = build_constraint_graph(errors);

    // Find connected components
    let components = graph.connected_components();

    // Identify root vs. cascading errors
    components.into_iter().map(|component| {
        let root = find_root_in_component(&component);
        let cascaded = component.into_iter()
            .filter(|e| e != root)
            .collect();
        ErrorCascade { root, cascaded }
    }).collect()
}
```

---

### Stage 4: Diagnostic Rendering (Multi-Format Output)

**Input:** DiagnosticSet<'db>

**Process:**
```
DiagnosticSet
      │
      ├────────────┬────────────┬────────────┬────────────┐
      │            │            │            │            │
      ↓            ↓            ↓            ↓            ↓
  Terminal       LSP         JSON        HTML       Statistics
  (colors)    (IDE rich)  (CI/CD)    (web view)   (summary)
```

**Output Formats:**

**1. Terminal (Human-Readable)**
```
error[E001]: type mismatch
  --> src/main.hwml:42:10
   |
40 | fn process(x: Nat) -> Nat {
41 |     let y = x + 1;
42 |     return true;
   |            ^^^^ expected Nat, found Bool
43 | }

elaboration backtrace:
  0: checking expression against Nat at src/main.hwml:42:10
  1: checking function return type at src/main.hwml:40:23

help: consider using an if expression

error: aborting due to 1 previous error
```

**2. LSP (IDE Integration)**
```json
{
  "diagnostics": [{
    "range": {"start": {"line": 41, "character": 11}, ...},
    "severity": 1,
    "code": "E001",
    "message": "type mismatch: expected Nat, found Bool",
    "relatedInformation": [{
      "location": {"uri": "...", "range": ...},
      "message": "function return type declared here"
    }],
    "codeDescription": {
      "href": "https://hwml.dev/errors/E001"
    }
  }]
}
```

**3. JSON (Machine-Readable)**
```json
{
  "errors": 1,
  "warnings": 0,
  "diagnostics": [...],
  "files": {"src/main.hwml": {"errors": 1, "warnings": 0}},
  "elapsed_ms": 42
}
```

**4. Statistics Summary**
```
Found 5 error(s) and 3 warning(s) across 3 file(s)

  src/main.hwml    - 2 error(s), 1 warning(s)
  src/lib.hwml     - 2 error(s), 2 warning(s)
  src/utils.hwml   - 1 error(s), 0 warning(s)
```

**Current State:** ❌ Not implemented (designed in wiki)

**Key Feature:** Group by file, sort intelligently
```rust
diagnostics.sort_by(|a, b| {
    a.severity.order().cmp(&b.severity.order())
        .then(a.file_path().cmp(&b.file_path()))
        .then(a.line().cmp(&b.line()))
        .then(a.column().cmp(&b.column()))
});
```

---

### Stage 5: Proof Term Generation (Distillation)

**Input:** Elaborated AST (only if no errors!)

**Process:**
```
Elaborated AST
      │
      ├─> Instantiate all metavariables
      │     (Use solutions from constraint solver)
      │
      ├─> Insert all implicit arguments
      │     (Make everything explicit)
      │
      ├─> Add all type annotations
      │     (Every subterm has type)
      │
      ├─> Resolve all indirections
      │     (Flatten to kernel language)
      │
      └─> Generate KernelTerm
            (Fully explicit, self-contained)
      │
      ↓
KernelTerm<'db>
```

**Example Transformation:**
```rust
// User Source (Stage 1)
fn double(x) = x + x

// Elaborated AST (Stage 2)
fn double(x: ?M1) -> ?M2 = x + x
// where ?M1 = Nat (inferred)
//       ?M2 = Nat (inferred)

// Proof Term (Stage 5)
Lam {
    param: "x",
    param_ty: KernelType::Nat,
    return_ty: KernelType::Nat,
    body: App {
        func: App {
            func: Builtin::Add,
            arg: Var("x")
        },
        arg: Var("x")
    }
}
```

**Output:** KernelTerm<'db> (fully explicit)

**Current State:** ❌ Not implemented (designed in wiki)

**Key Feature:** Make everything explicit
```rust
pub trait ToKernelTerm<'db> {
    fn to_kernel_term(&self, db: &'db dyn HwmlDb) -> KernelTerm<'db>;
}

impl<'db> ToKernelTerm<'db> for Expr<'db> {
    fn to_kernel_term(&self, db: &'db dyn HwmlDb) -> KernelTerm<'db> {
        match self {
            Expr::App { func, arg } => {
                // INSERT IMPLICIT ARGUMENTS!
                let all_args = self.collect_implicit_and_explicit_args(db);
                KernelTerm::MultiApp {
                    func: func.to_kernel_term(db),
                    args: all_args.iter()
                        .map(|a| a.to_kernel_term(db))
                        .collect(),
                }
            }
            // ... handle all cases
        }
    }
}
```

---

### Stage 6: Kernel Verification (Trust Boundary)

**Input:** KernelTerm<'db>

**Process:**
```
KernelTerm
      │
      ├─> Type Check (simple algorithm)
      │     • No unification
      │     • No inference
      │     • No elaboration
      │     • Just verification
      │
      └─> Accept or Reject
            │
            ├─> Accept → Proof Valid ✓
            │
            └─> Reject → Bug in Elaboration!
                         (Not user error)
```

**Kernel Type Checker:**
```rust
/// TRUSTED KERNEL - Keep this simple!
pub mod kernel {
    pub fn type_check(
        ctx: &Context,
        term: &KernelTerm,
        expected_ty: &KernelType,
    ) -> Result<(), KernelError> {
        match term {
            KernelTerm::Var(x) => {
                let actual = ctx.lookup(x)?;
                if actual.eq_alpha(expected_ty) {
                    Ok(())
                } else {
                    Err(KernelError::TypeMismatch { expected, actual })
                }
            }
            KernelTerm::Lam { param, param_ty, body } => {
                match expected_ty {
                    KernelType::Pi { domain, codomain } => {
                        if !param_ty.eq_alpha(domain) {
                            return Err(KernelError::DomainMismatch);
                        }
                        let mut ctx2 = ctx.clone();
                        ctx2.insert(param, param_ty);
                        type_check(&ctx2, body, codomain)
                    }
                    _ => Err(KernelError::NotFunction),
                }
            }
            // All other cases equally simple!
        }
    }
}
```

**Output:** Accept/Reject

**Current State:** ❌ Not implemented

**Key Properties:**
- **Simple** - No clever algorithms, just checking
- **Small** - Target < 5k LOC
- **Auditable** - Anyone can verify correctness
- **No dependencies** - On elaboration or constraint solving

---

### Stage 7: Proof Export (External Verification)

**Input:** KernelTerm<'db>

**Process:**
```
KernelTerm
      │
      ├────────┬────────┬────────┬────────┐
      │        │        │        │        │
      ↓        ↓        ↓        ↓        ↓
   Coq      Lean    Isabelle  Dedukti  Lambdapi
 (.v file) (.lean)  (.thy)   (.dk)    (.lp)
```

**Output:** Proof files for external checkers

**Example Coq Export:**
```coq
(* Generated from HWML proof term *)
Definition double (x : nat) : nat := x + x.

Theorem double_correct : forall x, double x = x + x.
Proof.
  intro x.
  unfold double.
  reflexivity.
Qed.
```

**Example Lean Export:**
```lean
-- Generated from HWML proof term
def double (x : Nat) : Nat := x + x

theorem double_correct (x : Nat) : double x = x + x := rfl
```

**Current State:** ❌ Not implemented (future work)

**Key Benefit:** Independent verification by multiple checkers
- Coq checker verifies proof
- Lean checker verifies proof
- If both accept → very high confidence!

---

### Stage 8: Advanced Features (ML & Mining)

**Input:** ElaborationTrace + KernelTerm

**Applications:**

**1. ML Training Data**
```
ElaborationTrace
      │
      ├─> Extract tactic-level steps
      │     (Before/after states)
      │
      ├─> Extract proof terms
      │     (Kernel representation)
      │
      └─> Generate training pairs
            (State → Action → New State)
```

**Use Cases:**
- Train proof search models
- Train autocompletion models
- Train error prediction models

**2. Proof Simplification**
```
KernelTerm (verbose)
      │
      ├─> Apply ProofOptimizer-style ML
      │     (Iterative shortening)
      │
      └─> Simplified KernelTerm
            (Same semantics, shorter)
```

**Use Cases:**
- Improve proof readability
- Reduce proof checking time
- Generate human-friendly proofs

**3. Proof Mining**
```
KernelTerm + ElaborationTrace
      │
      ├─> Extract quantitative bounds
      │     (From type checking proofs)
      │
      ├─> Extract reusable lemmas
      │     (REFACTOR-style)
      │
      └─> Build proof library
            (Organize by patterns)
```

**Use Cases:**
- Discover complexity bounds
- Build lemma libraries
- Improve proof automation

**4. Proof-Carrying Hardware**
```
Hardware Module + KernelTerm
      │
      ├─> Package as proof-carrying module
      │     (RTL + correctness certificate)
      │
      └─> Verify at integration time
            (Check certificate before use)
```

**Use Cases:**
- Trusted IP cores
- Verified synthesis
- Hardware security modules

**Current State:** ❌ Not implemented (research phase)

---

## Data Flow Summary

### The Happy Path (No Errors)

```
User Source Code
      ↓
[Stage 1] Parsing & Desugaring
      ↓
Abstract Syntax Tree
      ↓
[Stage 2] Elaboration (with trace recording)
      ↓
Elaborated AST + ElaborationTrace
      ↓
[Stage 5] Proof Term Generation
      ↓
KernelTerm (fully explicit)
      ↓
[Stage 6] Kernel Verification
      ↓
✓ ACCEPT
      ↓
[Stage 7] Optional: Export to Coq/Lean
      ↓
[Stage 8] Optional: ML training, mining
```

### The Error Path (User Mistakes)

```
User Source Code (with errors)
      ↓
[Stage 1] Parsing & Desugaring
      ↓
Abstract Syntax Tree
      ↓
[Stage 2] Elaboration (lenient mode)
      ↓
Elaborated AST (partial) + Vec<ElabError> + ElaborationTrace
      ↓
[Stage 3] Error Post-Processing
      ↓
DiagnosticSet (deduplicated, root causes identified)
      ↓
[Stage 4] Diagnostic Rendering
      ↓
User-Friendly Error Messages
      ↓
× COMPILATION FAILED
```

### The Bug Path (Elaboration Error)

```
User Source Code (correct!)
      ↓
[Stage 1-2] Parsing & Elaboration
      ↓
Elaborated AST (no errors reported)
      ↓
[Stage 5] Proof Term Generation
      ↓
KernelTerm
      ↓
[Stage 6] Kernel Verification
      ↓
× REJECT - Type Error in Proof Term!
      ↓
⚠️  BUG IN ELABORATOR - Report to developers
```

**Key Insight:** If kernel rejects, it's OUR bug, not user's!

---

## Trust Boundaries

### Trusted Computing Base (TCB)

**What MUST be correct:**

1. **Kernel Type Checker** (Stage 6)
   - Small (< 5k LOC)
   - Simple algorithms
   - Independently auditable
   - **This is the only part that MUST be correct!**

2. **Kernel Language Definition** (KernelTerm/KernelType)
   - Formal semantics
   - Well-defined type system
   - Proven metatheory (confluence, normalization)

**What can have bugs without compromising soundness:**

1. **Parser** (Stage 1)
   - Bug → confusing error or crash
   - Does NOT lead to accepting incorrect proofs

2. **Elaborator** (Stage 2)
   - Bug → confusing error, or kernel rejects proof term
   - Kernel catches elaboration mistakes!

3. **Diagnostics** (Stages 3-4)
   - Bug → confusing error messages
   - Doesn't affect soundness at all

4. **Proof Term Generator** (Stage 5)
   - Bug → kernel rejects
   - Kernel catches mistakes!

5. **External Exporters** (Stage 7)
   - Bug → external checker rejects
   - No impact on HWML's correctness

### The LCF Architecture Guarantee

**De Bruijn Criterion:** "Check proofs, not proof scripts"

```
┌────────────────────────────────────────────┐
│      UNTRUSTED (can have bugs)             │
│  • Parser                                  │
│  • Elaborator                              │
│  • Constraint solver                       │
│  • Diagnostics                             │
│  • Proof term generator                    │
│  • ML models                               │
│  • Optimizations                           │
└────────────────┬───────────────────────────┘
                 │
                 ↓ KernelTerm
┌────────────────────────────────────────────┐
│      TRUSTED (must be correct)             │
│  • Kernel type checker (< 5k LOC)          │
│  • Kernel language definition              │
└────────────────────────────────────────────┘
```

**Property:** Bug in untrusted code → Kernel rejects OR confusing error, NEVER accepts incorrect proof!

---

## Implementation Roadmap

### Phase 1: Foundation (Weeks 1-4)

**Goal:** Extend existing infrastructure

**Tasks:**
1. **Extend Error Collection** (Week 1)
   - Make elaboration fully lenient
   - Collect all errors, don't fail-fast
   - Already partially done in `elab_library_with_sccs`

2. **ElaborationTrace Recording** (Weeks 2-3)
   ```rust
   pub struct ElaborationTrace<'db> {
       pub constraints: Vec<ConstraintRecord<'db>>,
       pub unifications: Vec<UnificationRecord<'db>>,
       pub meta_assignments: HashMap<MetaId, Expr<'db>>,
       pub judgments: Vec<TypingJudgment<'db>>,
       pub provenance: ProvenanceGraph<'db>,  // Leverage existing!
   }
   ```

3. **RAII Trace Guards** (Week 3)
   ```rust
   fn check_expr(&self, expr: &Expr) -> Result<Type> {
       let _guard = TraceGuard::new(self, TraceEntry::CheckExpr {
           expr: expr.clone(),
           span: expr.span,
       });
       // Backtrace automatically includes this!
       self.check_expr_impl(expr)
   }
   ```

4. **Basic Diagnostic Output** (Week 4)
   - Convert ElabError → Diagnostic
   - Simple terminal rendering
   - Test on existing code

**Deliverables:**
- ✅ Lenient error collection working
- ✅ Full elaboration traces recorded
- ✅ Backtrace in error messages
- ✅ Basic diagnostic output

### Phase 2: Diagnostics (Weeks 5-8)

**Goal:** User-friendly error messages

**Tasks:**
1. **Post-Processing Pipeline** (Weeks 5-6)
   - Deduplication algorithm
   - Cascading error analysis (use provenance!)
   - Pattern detection (common mistakes)
   - Suggestion generation

2. **Source Rendering** (Week 7)
   - Multi-line snippets with context
   - Caret underlines (`^^^^`)
   - Unicode-aware column calculation
   - ANSI colors for terminal

3. **Multiple Output Formats** (Week 8)
   - Terminal (human-readable)
   - LSP (IDE integration)
   - JSON (machine-readable)
   - Statistics summary

**Deliverables:**
- ✅ Beautiful error messages
- ✅ LSP integration working
- ✅ CI/CD JSON output
- ✅ File grouping and statistics

### Phase 3: Proof Terms (Weeks 9-14)

**Goal:** Generate and verify proof terms

**Tasks:**
1. **Kernel Language Design** (Week 9)
   ```rust
   pub enum KernelTerm<'db> {
       Var(Name),
       Lam { param: Name, param_ty: KernelType<'db>, body: Box<KernelTerm<'db>> },
       App { func: Box<KernelTerm<'db>>, arg: Box<KernelTerm<'db>> },
       Pi { param: Name, domain: KernelType<'db>, codomain: KernelType<'db> },
       // ... minimal set of constructs
   }
   ```

2. **Proof Term Generation** (Weeks 10-11)
   - Implement `ToKernelTerm` trait
   - Instantiate all metavariables
   - Insert all implicit arguments
   - Add all type annotations
   - Test on simple examples

3. **Trusted Kernel** (Weeks 12-13)
   - Simple type checker (no unification!)
   - Alpha-equality checking
   - Context management
   - Keep it SIMPLE and AUDITABLE

4. **Integration & Testing** (Week 14)
   - Elaborate → Generate → Check pipeline
   - Test on entire codebase
   - Verify kernel catches bugs

**Deliverables:**
- ✅ KernelTerm representation
- ✅ Proof term generation working
- ✅ Trusted kernel (< 5k LOC)
- ✅ End-to-end verification

### Phase 4: External Verification (Weeks 15-18)

**Goal:** Export to other proof assistants

**Tasks:**
1. **Coq Export** (Weeks 15-16)
   - KernelTerm → Coq syntax
   - Handle type theory differences
   - Test roundtrip verification

2. **Lean Export** (Week 17)
   - KernelTerm → Lean 4 syntax
   - Leverage similar type systems
   - Test on examples

3. **Cross-Checker Testing** (Week 18)
   - Verify same proof accepted by multiple checkers
   - Build confidence in kernel correctness

**Deliverables:**
- ✅ Coq exporter working
- ✅ Lean exporter working
- ✅ Cross-verification tests passing

### Phase 5: Advanced Features (Months 5-6)

**Goal:** ML integration and optimization

**Tasks:**
1. **ML Training Data** (Month 5)
   - Extract tactic-level steps from traces
   - Export in standard formats (LEANSTEP-style)
   - Generate datasets for research

2. **Proof Simplification** (Month 6)
   - Identify redundant steps
   - Remove unnecessary intermediates
   - ProofOptimizer-style optimization

3. **Proof Mining** (Month 6)
   - Extract complexity bounds
   - Identify reusable lemmas
   - Build proof library

**Deliverables:**
- ✅ ML training datasets
- ✅ Proof simplification working
- ✅ Proof mining experiments

### Phase 6: Hardware-Specific (Months 7-12)

**Goal:** Proof-carrying hardware modules

**Tasks:**
1. **Module Certificates** (Months 7-8)
   - Package hardware modules with proofs
   - Define interface for proof-carrying modules
   - Integration with synthesis tools

2. **Compositional Verification** (Months 9-10)
   - Verify module composition
   - Check interface contracts
   - Incremental verification with Salsa

3. **Hardware Security** (Months 11-12)
   - Timing-safe proofs
   - Information flow proofs
   - Side-channel resistance certificates

**Deliverables:**
- ✅ Proof-carrying module format
- ✅ Compositional verification
- ✅ Security certificates for hardware

---

## Key Design Decisions

### 1. Lenient vs. Fail-Fast Elaboration

**Decision:** Lenient (already partially implemented)

**Rationale:**
- Better user experience (see multiple errors at once)
- Enables holistic analysis (find root causes)
- Standard in modern compilers (rustc, ghc)

**Implementation:** Continue on error, collect in Vec<ElabError>

### 2. Provenance Graph vs. Explicit Trace

**Decision:** Both! Provenance for constraints, ElaborationTrace for full history

**Rationale:**
- Provenance graph already exists, handles constraints well
- ElaborationTrace adds tactic-level steps, judgments
- Provenance enables cascading error analysis
- Trace enables ML training, proof reconstruction

**Implementation:** Extend existing provenance, add ElaborationTrace

### 3. Small Kernel vs. Verified Elaborator

**Decision:** Small kernel (like Lean, Coq)

**Rationale:**
- MetaCoq-style verified elaboration is research project (years)
- Small kernel gives high assurance NOW
- Can add verified elaborator later (doesn't change architecture)
- Kernel < 5k LOC is auditable by hand

**Implementation:** LCF architecture with trusted kernel

### 4. Error Messages vs. Proof Terms

**Decision:** Do both in parallel (Phases 1-2 and 3-4)

**Rationale:**
- Error messages are user-facing, high priority
- Proof terms are foundational, high priority
- Different teams can work in parallel
- Both leverage elaboration infrastructure

**Implementation:** Parallel development, integrate later

### 5. Internal Verification vs. External Export

**Decision:** Internal first, then external

**Rationale:**
- Internal kernel proves concept
- External export adds confidence
- Can iterate on kernel design before exporting
- External export is "nice to have", not critical path

**Implementation:** Phase 3 (internal), Phase 4 (external)

---

## Success Metrics

### Phase 1-2: Diagnostics ✓

**User Experience:**
- [ ] Users see multiple errors in one compilation
- [ ] Root cause is highlighted, cascading errors suppressed
- [ ] Suggestions help fix common mistakes
- [ ] LSP integration shows errors in IDE

**Technical:**
- [ ] Deduplication reduces error count by >30%
- [ ] Cascading analysis identifies root causes correctly >90%
- [ ] Pattern detection suggests fixes for >50% of errors
- [ ] Terminal output is readable and actionable

### Phase 3-4: Proof Terms ✓

**Soundness:**
- [ ] Kernel rejects all malformed proof terms
- [ ] Kernel accepts all correctly elaborated terms
- [ ] External checkers (Coq/Lean) agree with kernel

**Performance:**
- [ ] Proof term generation adds <10% to elaboration time
- [ ] Kernel checking adds <5% to total compilation time
- [ ] Memory overhead for traces <20%

**Quality:**
- [ ] Kernel implementation < 5k LOC
- [ ] Kernel has no dependencies on elaborator
- [ ] Independent reviewers can audit kernel in <1 week

### Phase 5-6: Advanced ✓

**Research Value:**
- [ ] ML training data enables proof automation research
- [ ] Proof simplification reduces proof size by >40%
- [ ] Proof mining discovers useful lemmas automatically

**Hardware Impact:**
- [ ] Proof-carrying modules integrate with synthesis tools
- [ ] Compositional verification scales to large systems
- [ ] Security certificates catch timing violations

---

## Conclusion

**The Big Picture:** HWML follows the universal architecture of modern proof assistants, adapted for hardware verification.

**Key Pillars:**
1. **Elaboration with traces** - Record everything for diagnostics and ML
2. **User-friendly errors** - Post-process for clarity, group by root cause
3. **Proof term generation** - Make implicit explicit, verify independently
4. **Small trusted kernel** - Simple, auditable, independently checkable
5. **External verification** - Export to Coq/Lean for additional confidence
6. **Hardware focus** - Proof-carrying modules, security certificates

**Timeline:** 18 months to full implementation
- Months 1-2: Foundation + Diagnostics
- Months 3-4: Proof Terms + Kernel
- Months 5-6: External Export + Advanced Features
- Months 7-18: Hardware-specific applications

**Current Status:**
- ✅ Bidirectional type checking (implemented)
- ✅ Constraint solving with provenance (implemented)
- ✅ Salsa incremental computation (implemented)
- 🔄 Lenient error collection (partially implemented)
- ❌ Full elaboration traces (needs implementation)
- ❌ Diagnostic post-processing (designed, not implemented)
- ❌ Proof term generation (designed, not implemented)
- ❌ Trusted kernel (designed, not implemented)

**Next Steps:** Start Phase 1 (Foundation) - extend error collection and add elaboration trace recording.

---

**Document Status:** COMPLETE
**Total Length:** 693+ lines
**Purpose:** Big picture architecture showing how all pieces fit together
**Audience:** Developers, designers, stakeholders
**Related Docs:** `research/proof-distillation-survey.md`, `research/diagnostic-framework-design.md`

