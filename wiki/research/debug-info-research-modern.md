# Modern Debug Information Research

**Type:** Research
**Last Updated:** 2026-05-03
**Purpose:** Survey of recent academic research (2020-2024) on debug information formats, correctness, and optimization

---

## Overview

Recent academic research has identified fundamental problems with debug information in optimized code and proposed new approaches to measuring, validating, and improving debug info quality. This document covers the state-of-the-art research from top-tier conferences (PLDI, ASPLOS, Onward!).

**Key insight:** Debug information correctness is an **ill-posed problem** - there's no perfect answer, only trade-offs.

---

## Major Research Themes

### 1. Correctness and Validation
- How do we know debug info is correct?
- Testing frameworks for debug info
- Compiler bugs related to debug info

### 2. Completeness and Coverage
- Measuring how much debug info is present
- Gaps in variable locations
- Quantifying "optimized out" variables

### 3. Debug Info Invariance
- Should compilation output differ with/without debug info?
- Testing for consistency
- Compiler bugs that violate invariance

### 4. Optimized Code Debugging
- Fundamental tension between optimization and debuggability
- State mapping and residual computation
- Temporal imprecision

---

## Recent Papers (2020-2024)

### ASPLOS 2023: "Compilation Consistency Modulo Debug Information"

**Authors:** Wang, Tian, Dong, Xu, Sun
**Problem:** CCMD (Compilation Consistency Modulo Debug Information)

**Key finding:** Compilers should generate **identical machine code** whether debug info is enabled or not.

**Violations found:**
- GCC, LLVM have bugs where `-g` changes optimization
- Debug info presence affects inlining decisions
- Loop optimizations behave differently with debug info

**Dfusor testing technique:**
```c
// Original program P
int foo(int x) { return x + 1; }

// Dfusor generates variant P' with more debug opportunities
int foo(int x) {
  int y = x;      // More variables
  int z = y + 1;  // More assignments
  return z;
}

// Compile P and P' with/without -g
// Machine code should be identical for P
// But more debug info for P'
```

**Methodology:**
1. Take compilable program
2. Generate variants with more debug info opportunities
3. Compile with/without `-g`
4. Compare machine code (should be identical)
5. Found 14 bugs in GCC, 6 in LLVM

**Impact:** First systematic study of debug info affecting optimization

---

### ASPLOS 2023: "Where Did My Variable Go? Poking Holes in Incomplete Debug Information"

**Authors:** Assaiante, D'Elia, Di Luna, Querzoni
**Problem:** **Completeness** of debug information in optimized code

**Key contribution:** Three conjectures about variable availability:

#### Conjecture 1: Variable Visibility
"A variable should be visible at any source line where it is in lexical scope"

**Reality:** Variables often missing due to optimization

**Measurement:**
```python
visibility_ratio = visible_variables / total_in_scope_variables
```

**Finding:** Only 60-70% visibility at -O2 in GCC/LLVM

#### Conjecture 2: Variable Availability
"A visible variable should have a displayable value"

**Reality:** Variables shown but value is `<optimized out>`

**Measurement:**
```python
availability_ratio = available_variables / visible_variables
```

**Finding:** 80-90% of visible variables have values

#### Conjecture 3: Value Accuracy
"Available variable values should match -O0 behavior"

**Reality:** Some values are stale or incorrect

**Approach: Where-Provenance Analysis**
- Track which optimizations affected each variable
- Identify root causes of missing variables
- Common culprits: SROA, loop optimizations, inlining

**Tools provided:**
- DVLiveness - compute expected variable lifetime
- metrics for comparing debug info quality across compilers/versions

---

### Onward! 2024: "Source-Level Debugging of Compiler-Optimised Code: Ill-Posed, but Not Impossible"

**Authors:** Stephen Kell, J. Ryan Stinnett
**Groundbreaking insight:** **Debug info correctness is ill-posed**

**What does "ill-posed" mean?**
- No unique correct answer
- Multiple valid interpretations
- Cannot be fully specified algorithmically

**Example:**
```c
int x = a + b;
int y = x * 2;
// Compiler optimizes to: y = (a + b) * 2
// What is "x" when stopped at line 2?
//   Option A: x doesn't exist (optimized out)
//   Option B: x = a + b (recompute)
//   Option C: x = y / 2 (reverse engineer)
// All are "correct" in some sense!
```


1. **Unreachable breakpoints** - optimizations eliminate code
2. **Undefined behavior** - inspecting uninitialized variables
3. **No ground truth** - what's the "correct" value?

**Solution: Actionable Program Transformation**

**Key idea:** Transform program to make debug info testable

**Definition: Actionable Program**
```
P⟨s,v⟩ - Program with specific line s and variable v
         guaranteed to be actionable (testable)
```

**Transformations to ensure actionability:**

1. **Make breakpoint reachable:**
```c
// Original (might be optimized away)
if (false) {
  x = 5;  // Unreachable
}

// Actionable version
if (input()) {  // External input, can't optimize
  x = 5;
}
```

2. **Make variable initialized:**
```c
// Original (undefined behavior to inspect)
int x;
foo(x);

// Actionable version
int x = 0;  // Initialized
foo(x);
```

3. **Force variable to exist:**
```c
// Original (might be optimized away)
int x = a + b;

// Actionable version
int x = a + b;
consume(x);  // Use x, prevent elimination
```

**Testing framework:**
```
For each ⟨statement s, variable v⟩:
  1. Transform program → P⟨s,v⟩
  2. Compile with optimization
  3. Run in debugger
  4. Check:
     - Can set breakpoint at s?
     - Is v visible?
     - Does v have expected value?
```

**Results:**
- Found 45 bugs in GCC DWARF generation
- Found 23 bugs in LLVM DWARF generation
- Most bugs: incorrect location lists, wrong scopes

---

### 2024: "Accurate Coverage Metrics for Compiler-Generated Debugging Information"

**Authors:** (arXiv 2402.04811)
**Problem:** How to measure debug info quality?

**Current metrics are flawed:**
```python
# Naive metric (wrong!)
coverage = variables_with_location / total_variables

# Problem: Assumes variable could be available everywhere in scope
# Reality: Variable might only be live for small region
```

**Proposed: Liveness-based metrics**

**Step 1: Compute expected liveness**
- Use compiler's liveness analysis
- Determine where variable *could* have location
- Account for optimization effects

**Step 2: Measure actual coverage**
```python
expected_liveness = liveness_analysis(variable)
actual_coverage = dwarf_location_ranges(variable)
coverage = len(actual_coverage) / len(expected_liveness)
```

**Example:**
```c
int foo() {
  int x = 0;        // x born
  for (int i = 0; i < 10; i++) {
    x += i;         // x live
  }
  return x;         // x last use, then dead
}

// Expected liveness: lines 2-5
// DWARF location: lines 2-3 (missing 4-5)
// Coverage: 50%

// Old metric would assume x should cover whole function
// New metric: more accurate, accounts for actual liveness
```

**Key contributions:**
1. First robust liveness-based metric
2. Comparable across compilations
3. Tools to compute metrics automatically
4. Benchmark suite for debug info quality

---

## Practical Implications

### For Compiler Developers

**1. Measure completeness systematically**
```bash
# Use liveness-based coverage tool
./measure-debug-coverage -O2 myprogram.c
# Output: 73.5% variable coverage
#         92.1% line coverage
#         Gaps at: loop optimizations, inlining
```

**2. Test debug info invariance**
```bash
# Dfusor-style testing
gcc -O2 program.c -o a.out
gcc -O2 -g program.c -o b.out
diff <(objdump -d a.out) <(objdump -d b.out)
# Should be identical!
```

**3. Validate DWARF correctness**
```bash
# Actionable program testing
./generate-actionable-variants program.c
for variant in variants/*.c; do
  test-debug-info $variant
done
# Reports: 45 DWARF bugs found
```

### For Language Designers

**1. Design for debuggability**
- Simple semantics → easier to map to machine state
- Explicit state → less residual computation needed
- Predictable optimization → less temporal imprecision

**2. Residual computation friendly**
```
# Good: Easy to reconstruct
x = a + b

# Bad: Hard to reconstruct
x = complexFunction(a, b, c, d)
# Would need to re-execute complexFunction
```

**3. Metadata extensibility**
- Allow custom debug info
- Support for domain-specific semantics
- Turing-powerful expressions if needed

### For Tool Developers (Debuggers)

**1. Embrace ill-posed nature**
- Provide multiple views of "current state"
- Let user choose trade-off (density vs fidelity)
- Show confidence levels

**Example debugger UI:**
```
Variable x:
  [High confidence] 42 (from register RAX)
  [Medium confidence] 43 (recomputed from y - 1)
  [Low confidence] <optimized out>

Choose view: [Accurate] [Complete] [Balanced]
```

**2. Use residual computation**
```
// Instead of just "optimized out"
x: <optimized out>

// Show how to recompute
x: <can recompute from 'a + b'>
   (a = 10, b = 5)
   [Compute now?]
```

**3. Handle temporal imprecision**
```
Current execution point:
  Logically: line 42
  Physically: lines 38-42 (hoisted/reordered)

Show variables from:
  ○ Logical line (42 only)
  ● All affected lines (38-42)
```

---

## Trends and Future Directions

### 1. Machine Learning for Debug Info

**Idea:** Learn to predict variable locations from optimization patterns

**Potential:**
- "This loop optimization usually eliminates x"
- "Suggest keeping y for better debuggability"
- Auto-generate salvaging strategies

**Challenges:**
- Training data (need labeled correct/incorrect debug info)
- Correctness guarantees (can't be approximate)

### 2. Reversible Debugging

**Idea:** Record execution, reconstruct state retroactively

**Approaches:**
- rr (Mozilla) - records execution traces
- Undo (from paper authors) - reverse execution
- Time-travel debugging

**Connection to debug info:**
- Less reliance on metadata
- Can recompute historical state
- Trade-off: storage vs metadata accuracy

### 3. Hybrid Approaches

**Combine:**
- Traditional debug info (DWARF)
- Residual computation (expressions)
- Reversible debugging (time travel)
- JIT deoptimization (dynamic)

**Example:**
```
Debugger strategy:
  1. Try DWARF location list (fast)
  2. If unavailable, try residual computation
  3. If still unavailable, replay from checkpoint
  4. If still unavailable, deoptimize and recompute
```

### 4. Formal Verification of Debug Info

**Goal:** Prove debug info is correct

**Challenges:**
- What does "correct" even mean? (Ill-posed!)
- Optimization transformations are complex
- Thousands of optimization passes

**Partial solutions:**
- Translation validation (check specific transformation)
- Bounded verification (prove for limited cases)
- Fuzzing + oracles (find bugs, not prove correctness)

---

## Key Insights for HWML

### 1. Embrace Ill-Posed Nature

**Don't aim for "perfect" debug info** - it doesn't exist!

**Instead, provide:**
- **Accurate mode:** Only show when confident
- **Complete mode:** Show everything, even if imprecise
- **Balanced mode:** Reasonable middle ground

**HWML example:**
```hwml
-- After unification and NbE
def foo : Vec Bit 8 = ...

-- Debugger views:
-- [Accurate] Vec Bit 8  (from type checker)
-- [Complete] Vec Bit ?n where ?n = 8  (show metavar history)
-- [Residual] Vec Bit (evalType (?n := Nat.lit 8))  (recomputable)
```

### 2. Measure Completeness

**Implement liveness-based metrics:**
```rust
struct DebugCoverage {
    expected_liveness: HashMap<VarId, Vec<Range>>,
    actual_locations: HashMap<VarId, Vec<Range>>,
}

impl DebugCoverage {
    fn coverage(&self, var: VarId) -> f64 {
        let expected = self.expected_liveness[var].total_range();
        let actual = self.actual_locations[var].total_range();
        actual / expected
    }
}
```

**Track where debug info is lost:**
- NbE quotation
- Unification
- Elaboration synthesis
- Optimization (if any)

### 3. Test Debug Info Invariance

**HWML should ensure:**
```bash
# Elaborate with full debug info
hwml-elab --debug=full input.hwml -o out1.hwmli

# Elaborate with no debug info
hwml-elab --debug=none input.hwml -o out2.hwmli

# Should produce identical semantics
hwml-compare-semantics out1.hwmli out2.hwmli
# → PASS: Semantically equivalent

# But different debug metadata
hwml-compare-debug out1.hwmli out2.hwmli
# → DIFF: out1 has 245 location annotations, out2 has 0
```

### 4. Residual Computation for Dependent Types

**HWML's advantage:** Type-level computation is explicit

**Example:**
```hwml
def replicate {n : Nat} (x : Bit) : Vec Bit n = ...

-- After elaboration, n is computed
-- Debug info can record:
residual_info {
  n = "evaluated from type argument"
  value = Nat.lit 8
  expression = "8"  -- original source
}

-- Debugger can show:
-- n: 8  [computed from type parameter]
```

### 5. Two-Level Debug Strategy

**Meta-level (elaboration):**
- Traditional DWARF or similar
- Metavariable tracking
- Constraint visualization
- **Accuracy matters** - this is compilation

**Object-level (hardware):**
- Source locators (Chisel-style)
- Waveform correlation
- **Completeness matters** - need to trace signals

**Key:** These are separate concerns with different requirements!

---

## Summary: State of Research

### What We Know

1. **Debug info correctness is ill-posed**
   - No unique right answer
   - Trade-offs between density, height, fidelity
   - Partial correctness criteria possible

2. **Current compilers have significant gaps**
   - 60-70% visibility at -O2
   - 80-90% of visible vars have values
   - Hundreds of DWARF bugs in GCC/LLVM

3. **Debug info can affect optimization**
   - CCMD violations found
   - Compiler bugs where `-g` changes output
   - Need systematic testing

4. **Liveness-based metrics are more accurate**
   - Better than naive "coverage in scope"
   - Account for optimization effects
   - Comparable across compilations

### What We Don't Know

1. **Optimal trade-off between optimization and debuggability**
   - How much performance for how much debug info?
   - User studies needed

2. **Residual computation limits**
   - How complex can DIExpressions be?
   - When to fall back to "optimized out"?

3. **Temporal imprecision handling**
   - UI/UX for showing imprecise locations
   - User expectations and mental models

### Open Research Questions

1. Can we formally verify debug info transformations?
2. Can ML predict good salvaging strategies?
3. What's the right UI for ill-posed debug info?
4. How to handle dependent types in DWARF?
5. Integration with reversible debugging?

---

## References

### Key Papers

**ASPLOS 2023:**
- "Compilation Consistency Modulo Debug Information" (Wang et al.)
- "Where Did My Variable Go?" (Assaiante et al.)

**Onward! 2024:**
- "Source-Level Debugging of Compiler-Optimised Code" (Kell, Stinnett)

**PLDI 2020:**
- "Debug Information Validation for Optimized Code" (Li, Wu, Xie)

**arXiv 2024:**
- "Accurate Coverage Metrics for Compiler-Generated Debugging Information"

### Classic Papers (Historical Context)

**PLDI 1993:**
- "Source-Level Debugging of Scalar Optimized Code" (Copperman)
  - Introduced currency determination
  - "Debugging without being misled"

### Tools and Frameworks

- **Dfusor** - CCMD testing (ASPLOS 2023)
- **DVLiveness** - Liveness-based metrics (arXiv 2024)
- **Actionable testing** - DWARF validation (PLDI 2020)

### Related HWML Docs

- `wiki/research/debug-info-systems.md` - DWARF, PDB overview
- `wiki/research/hardware-debug-info.md` - Hardware simulation debug
- `wiki/research/llvm-debug-info-internals.md` - LLVM implementation details

---

## See Also

- [[research/debug-info-systems]] - Debug info formats (DWARF, PDB)
- [[research/llvm-debug-info-internals]] - LLVM debug info implementation
- [[research/hardware-debug-info]] - Hardware debug (VCS, waveforms)

---

**Status:** Research complete. Provides academic foundation for HWML debug info design decisions.

**Key takeaway:** Modern research shows debug info is fundamentally about **trade-offs**, not perfection. HWML should embrace this, provide multiple views, measure completeness, and ensure invariance.
- Source state → Machine state mapping
- Not 1-to-1, but many-to-many
- Mapping has three properties:

**1. Density:** How many source states have mappings?
```
density = (source states with any mapping) / (total source states)
```

**2. Height:** How many machine states per source state?
```
height = average(machine states per source state)
```

**3. Fidelity:** How accurate are the mappings?
```
fidelity = how closely machine state matches source semantics
```

**Trade-offs:**
- High density → show "optimized out" less
- High fidelity → only show when truly accurate
- Can't maximize both!

#### Residual Computation
**Idea:** Keep just enough information to reconstruct state

**Example:**
```c
int x = a + b;
// x is eliminated, but keep:
//   - x = a + b (residual expression)
//   - Locations of a and b
// Debugger can recompute x on demand
```

**Turing-powerful metadata?**
- Could embed arbitrary computation in debug info
- DIExpression already has simple VM
- Could extend to full reconstruction

#### Temporal Imprecision
**Problem:** Code motion makes "current line" ambiguous

**Example:**
```c
1: int x = foo();
2: int y = bar();
3: print(x + y);

// Optimized to:
// (hoisted before loop)
// x_val = foo();
// y_val = bar();
// (inside loop)
// print(x_val + y_val);

// If stopped in loop, what line are we on?
// - Line 3 (the print)?
// - Lines 1-2 (the hoisted calls)?
// - All of them simultaneously?
```

**Partial correctness criterion:**
"Variable location is correct if using it produces observably correct behavior"

**Not verifiable, but provides design guidance**

---

### PLDI 2020: "Debug Information Validation for Optimized Code"

**Authors:** Li, Wu, Xie
**Problem:** How to test debug info for correctness?

**Challenge:** Existing testing focuses on unoptimized code

**Novel challenges:
