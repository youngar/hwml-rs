# LLVM Debug Information Internals

**Type:** Research
**Last Updated:** 2026-05-03
**Purpose:** Deep dive into how LLVM preserves, transforms, and consumes debug information through compilation

---

## Overview

LLVM's debug information system bridges source code and machine code across three major stages:
1. **Frontend → IR:** Source info encoded as metadata + intrinsics
2. **IR → IR:** Optimizations preserve/update debug info
3. **IR → Machine Code:** Backend generates DWARF/CodeView

This document covers the **internal mechanisms** that make debug info survive optimization and code generation.

---

## The Three Representations

### 1. IR Level: Metadata + Debug Records

**Two formats (transitioning):**

#### Old Format: Debug Intrinsics (deprecated)
```llvm
declare void @llvm.dbg.declare(metadata, metadata, metadata)
declare void @llvm.dbg.value(metadata, metadata, metadata)
declare void @llvm.dbg.assign(metadata, metadata, metadata, metadata, metadata, metadata)
declare void @llvm.dbg.label(metadata, metadata)
```

**Example:**
```llvm
define i32 @foo(i32 %x) !dbg !10 {
entry:
  %x.addr = alloca i32
  store i32 %x, i32* %x.addr
  call void @llvm.dbg.declare(metadata i32* %x.addr,
                               metadata !15,    ; DILocalVariable "x"
                               metadata !DIExpression())
  %y = add i32 %x, 1
  call void @llvm.dbg.value(metadata i32 %y,
                            metadata !16,      ; DILocalVariable "y"
                            metadata !DIExpression())
  ret i32 %y
}
```

#### New Format: Debug Records (current, since LLVM 18+)
- **Not instructions** - attached to instructions, don't appear in instruction list
- Faster to process
- Can't be accidentally moved/deleted by naive transforms

**Accessing debug records:**
```cpp
// Old way (iterates all instructions, including debug intrinsics)
for (Instruction &I : BB) { ... }

// New way (debug records attached to instructions)
for (Instruction &I : BB) {
  // Process instruction
  for (DbgRecord &DR : I.getDbgRecordRange()) {
    // Process debug records attached to I
  }
}
```

**Migration tools:**
- `Module::convertFromNewDbgValues()` - Convert to old format
- `Module::convertToNewDbgValues()` - Convert to new format
- Default: New format since LLVM 18

### 2. SelectionDAG Level: SDDbgValue

**During instruction selection:**
- Debug info converted from IR-level to `SDDbgValue` objects
- Attached to SelectionDAG nodes
- **Problem:** If SelectionDAG node is deleted, debug info can be lost

**Key classes:**
- `SDDbgValue` - Debug info during ISel
- `SelectionDAGBuilder::handleDebugValue()` - Process dbg intrinsics
- `SelectionDAGBuilder::resolveDanglingDebugInfo()` - Salvage when nodes disappear

**Salvaging:**
```cpp
// If referenced value V hasn't been materialized yet, record it
addDanglingDebugInfo(V, Var, Expr);

// Later, when V is materialized:
resolveDanglingDebugInfo(V, SDValue);
```

**Frame indices:**
- Variables on stack → FrameIndex nodes
- ISel can salvage by converting to FI references
- Prevents "optimized out" for stack-allocated vars

### 3. MachineInstr Level: DBG_VALUE / DBG_INSTR_REF

**After instruction selection:**
- `DBG_VALUE` - Specifies variable location at specific program point
- `DBG_INSTR_REF` - References value produced by another instruction (newer)
- `DBG_LABEL` - Debug label markers

**DBG_VALUE format:**
```
DBG_VALUE $rax, $noreg, !15, !DIExpression()
  ; Variable !15 is in register RAX

DBG_VALUE 42, $noreg, !15, !DIExpression()
  ; Variable !15 is the constant 42

DBG_VALUE $rsp, 0, !15, !DIExpression(DW_OP_plus_uconst, 8)
  ; Variable !15 is at [RSP + 8]

DBG_VALUE $noreg, $noreg, !15, !DIExpression()
  ; Variable !15 is undefined/optimized out
```

**DBG_INSTR_REF (instruction referencing):**
```
%0:gr64 = MOV64rm ...
DBG_INSTR_REF 0, 0, !15, !DIExpression()
  ; Variable !15 = instruction #0, operand #0 (the result of %0)
```

**Advantages:**
- Survives register allocation better
- Tracks value through transformations
- Can reconstruct location from instruction number

---

## How Debug Info is Preserved

### Rule 1: Location Preservation

**From "How to Update Debug Info" guide:**

**Preserve location when:**
- Instruction stays in same basic block
- Basic block folded into unconditional predecessor
- Moved to block that already has same debug location

**Example (preserve):**
```cpp
// Transform: a + b → b + a (commutative)
NewInst->setDebugLoc(OldInst->getDebugLoc());
```

**Merge locations when:**
- Combining instructions from different source locations
- Create composite location or use most specific

**Example (merge):**
```cpp
// Merging two instructions with different locations
DebugLoc DL = DILocation::getMergedLocation(Loc1, Loc2);
NewInst->setDebugLoc(DL);
```

**Drop location when:**
- No clear source correspondence
- Speculative/hoisted instruction

**Example (drop):**
```cpp
// Instruction has no source equivalent
SpeculativeInst->dropLocation();
```

---

## Optimization Pass Instrumentation

### Assignment Tracking

**Modern approach** for handling alloca-based variables through SROA/mem2reg.

**Key idea:**
- Attach `DIAssignID` to stores and `llvm.dbg.assign`
- Track which stores correspond to which variable assignments
- Allows SROA to split/transform stores while preserving debug info

**Example:**
```llvm
%s = alloca %struct.Foo
store i32 %x, i32* %s.field1, !DIAssignID !20
call void @llvm.dbg.assign(metadata i32 %x,
                           metadata !var,        ; Variable
                           !DIExpression(DW_OP_LLVM_fragment, 0, 32),
                           metadata !20,         ; DIAssignID (matches store)
                           metadata i32* %s.field1,
                           !DIExpression())
```

**When SROA splits struct:**
- Creates new stores with new `DIAssignID`s
- Creates new `llvm.dbg.assign` for each fragment
- Debugger can reconstruct full variable from fragments

**Handles:**
- Struct splitting
- Partial stores
- Store merging/splitting
- Promotion to registers

### Debug Info Invariance

**Goal:** Compilation output should be the same whether or not debug info is present.

**Problem:** Debug info used to affect optimizations
- Debug intrinsics count as "uses"
- Control flow with only debug info in block
- Metadata influencing decisions

**Testing: `-debugify-each`**
```bash
# Adds/removes synthetic debug info before/after each pass
opt -debugify-each -passes='...' input.ll

# Compare output with/without debug info
# Should be identical (modulo debug metadata)
```

**Common bugs caught:**
1. **SimplifyCFG:** Only removes empty blocks if no debug info
2. **InstCombine:** Different behavior with/without debug intrinsics
3. **Loop passes:** Debug locations in loop metadata affect optimization

**Fix:** Ignore debug info when making optimization decisions
```cpp
// Bad: counts debug intrinsics
if (BB.size() == 1) { /* empty block */ }

// Good: ignores debug records
if (BB.getFirstNonDebugInstruction() == BB.getTerminator()) { /* empty */ }
```

---

## Backend: Machine Code Generation

### LiveDebugValues Pass

**Purpose:** Extend variable location ranges through machine code.

**Input:** `DBG_VALUE` instructions at specific points
**Output:** Additional `DBG_VALUE` instructions to cover all valid ranges

**Example:**
```
Before LiveDebugValues:
  BB0:
    DBG_VALUE $rax, !var  ; var = RAX
    MOV $rbx, $rax        ; RAX copied to RBX
    ; (no debug info here)
  BB1:
    USE $rbx              ; var should still be RBX here!

After LiveDebugValues:
  BB0:
    DBG_VALUE $rax, !var
    MOV $rbx, $rax
    DBG_VALUE $rbx, !var  ; Inserted! var now in RBX
  BB1:
    DBG_VALUE $rbx, !var  ; Inserted! Propagated from BB0
    USE $rbx
```

**Two implementations:**

#### 1. VarLocBasedImpl (older)
- Tracks explicit locations
- **Dataflow:** Compute available variable locations
- Forward propagation through CFG
- **Limitations:** Can lose info through complex transformations

#### 2. InstrRefBasedImpl (newer, default)
- Tracks instruction-produced values
- Uses `DBG_INSTR_REF` instead of `DBG_VALUE`
- **Advantages:**
  - Survives register allocation better
  - Can recover locations after coalescing
  - More robust to transformations

**How InstrRef works:**
```
; Before RA:
%0:gr64 = ADD64rr %1, %2
DBG_INSTR_REF 0, 0, !var  ; var = instruction #0, operand #0

; After RA (register allocation):
$rax = ADD64rr $rcx, $rdx
DBG_INSTR_REF 0, 0, !var  ; Still refers to instruction #0
; LiveDebugValues resolves: var = $rax
```

**When value is clobbered:**
```
$rax = ADD64rr $rcx, $rdx  ; Instruction #0
DBG_INSTR_REF 0, 0, !var   ; var = $rax
; ...
$rax = MOV64rm ...         ; RAX clobbered
DBG_VALUE $noreg, !var     ; LiveDebugValues inserts: var now undefined
```

### SelectionDAG: Instruction Selection

**Challenge:** Lowering IR to machine instructions can lose debug info.

**Process:**
1. **Build SelectionDAG** from IR
2. **Attach SDDbgValue** to nodes
3. **Optimize DAG** (pattern matching, combining)
4. **Instruction selection** (convert to MachineInstrs)
5. **Transfer debug info** to MachineInstrs

**Problem scenarios:**

#### Dangling debug info
- `dbg.value` refers to value V
- V hasn't been materialized yet in DAG
- Record it as "dangling"
- Resolve when V is materialized

```cpp
handleDebugValue(V, Var, Expr) {
  if (!hasSDValue(V)) {
    // V not yet in DAG
    addDanglingDebugInfo(V, Var, Expr);
    return;
  }
  // V exists, emit SDDbgValue
  DAG.AddDbgValue(new SDDbgValue(V, Var, Expr));
}
```

#### Node elimination
- DAG optimization deletes node
- Attached debug info lost
- **Salvaging:** Try to express value using remaining nodes

**Example:**
```
Before:
  %add = add i32 %a, %b
  SDDbgValue(%add, !var)

DAG combines (add X, 0) → X:
  %add deleted
  SDDbgValue(%a, !var, DIExpression(DW_OP_plus_uconst, 0))
  ; Salvaged! Still correct, no "optimized out"
```

#### Entry values (call site parameters)
- Function parameter in register on entry
- Register gets clobbered immediately
- **Entry value:** "Value of parameter as it was on entry"

**DWARF:** `DW_OP_entry_value` / `DW_OP_GNU_entry_value`
```
DBG_VALUE $noreg, !param,
          !DIExpression(DW_OP_entry_value, DW_OP_reg5)
; "param's value was in register 5 on function entry"
```

**Allows:**
- Debugging optimized code
- Seeing original parameter values
- Even when register is reused

### AsmPrinter: DWARF Generation

**Final stage:** Convert machine debug info to DWARF.

**Class:** `DwarfDebug`

**Process:**
1. **beginModule:** Create compilation unit
2. **beginFunction:** Gather function metadata
3. **Process each MachineInstr:**
   - Track line number changes
   - Build `.debug_line` program
4. **Process DBG_VALUE instructions:**
   - Build location lists
   - Create variable DIEs
5. **endFunction:** Emit function debug info
6. **endModule:** Write DWARF sections

**Location lists:**
```
DBG_VALUE $rax, !var  @ 0x1000
; ...
DBG_VALUE $rbx, !var  @ 0x1050
; ...
DBG_VALUE undef, !var @ 0x1080

Becomes DWARF:
DW_TAG_variable
  DW_AT_name: "var"
  DW_AT_location: location list #0

.debug_loc:
  [0x1000, 0x1050): DW_OP_reg0 (RAX)
  [0x1050, 0x1080): DW_OP_reg3 (RBX)
  ; [0x1080, ...): no location
```

**Optimizations:**
- Merge adjacent same-location ranges
- Omit empty ranges
- Use base address specifiers for compression
- Split DWARF (.dwo files) for faster linking

---

## Common Pitfalls & Solutions

### 1. Variables Showing "Optimized Out"

**Causes:**
- Value truly not needed anymore (dead)
- Salvaging failed
- Critical edge eliminated block
- Register allocator couldn't preserve

**Solutions:**
- Use `llvm.dbg.assign` (better tracking)
- Mark values as "used" if debugging is critical
- Use `-O0` or `-Og` for better debug experience
- Implement custom salvaging in pass

### 2. Incorrect Variable Values

**Causes:**
- Debug info not updated after transformation
- Location list has gap
- Wrong DIExpression after transformation

**Solutions:**
- Always update `DIAssignID` when splitting stores
- Use `MachineInstr::dropDebugNumber()` if unsure
- Test with `-debugify-each`

### 3. Missing Source Locations

**Causes:**
- `dropLocation()` called too aggressively
- Merged location lost information
- Inlined function attribution wrong

**Solutions:**
- Use `setDebugLoc()` when replacing instructions
- Merge locations for combined instructions
- Preserve inlined-at information

### 4. Debug Info Affecting Optimization

**Causes:**
- Pass checks block size including debug intrinsics
- Loop metadata includes debug locations
- Value use-count includes debug uses

**Solutions:**
- Use `getFirstNonDebugInstruction()`
- Ignore debug-only metadata
- Use `users()` instead of `uses()` if appropriate
- Test with/without debug info

---

## Best Practices for LLVM Pass Writers

### 1. Preserve Locations
```cpp
// When replacing instruction
NewInst->setDebugLoc(OldInst->getDebugLoc());

// When combining from multiple sources
auto DL = DILocation::getMergedLocation(DL1, DL2);
NewInst->setDebugLoc(DL);
```

### 2. Update Variable Locations
```cpp
// When replacing a value
OldValue->replaceAllUsesWith(NewValue);
// Debug intrinsics are updated automatically!

// For assignment tracking
if (auto *Store = dyn_cast<StoreInst>(I)) {
  if (auto *OldID = Store->getMetadata(LLVMContext::MD_DIAssignID)) {
    NewStore->setMetadata(LLVMContext::MD_DIAssignID,
                          DIAssignID::getDistinct(Context));
    // Also update llvm.dbg.assign!
  }
}
```

### 3. Handle Debug Records
```cpp
// New debug format (preferred)
for (Instruction &I : BB) {
  // Process instruction

  // Also handle attached debug records
  for (DbgRecord &DR : I.getDbgRecordRange()) {
    if (auto *DVR = dyn_cast<DbgVariableRecord>(&DR)) {
      // Update variable record
    }
  }
}
```

### 4. Use Helper Functions
```cpp
// Move instruction preserving debug info
Inst->moveBeforePreserving(InsertPt);

// Not just moveBefore() - that loses debug records!
```

### 5. Salvage When Possible
```cpp
// If deleting instruction that debug info refers to
if (I->isUsedByMetadata()) {
  salvageDebugInfo(*I);  // Try to preserve with DIExpression
}
I->eraseFromParent();
```

### 6. Test Debug Info Preservation
```bash
# Add to your test
# RUN: opt < %s -passes=yourpass -S | FileCheck %s
# CHECK: call void @llvm.dbg.value(metadata {{.*}}, metadata ![[VAR:[0-9]+]]
# CHECK: ![[VAR]] = !DILocalVariable(name: "x"
```

---

## Debugging LLVM Debug Info

### View IR Debug Info
```bash
# Human-readable IR
llc -print-after-all input.ll 2>&1 | less

# Just debug intrinsics
opt -print-module input.ll 2>&1 | grep llvm.dbg
```

### View Machine Debug Info
```bash
# Machine IR with DBG_VALUE
llc -print-after=livedebugvalues input.ll

# Stop before register allocation
llc -stop-before=regallocfast input.ll -o - | less
```

### View DWARF
```bash
# Dump DWARF sections
llvm-dwarfdump output.o

# Just variable locations
llvm-dwarfdump --debug-info --debug-loc output.o | grep -A5 DW_TAG_variable

# Verify DWARF
llvm-dwarfdump --verify output.o
```

### Test Debug Info Preservation
```bash
# Synthetic debug info testing
opt -debugify -passes=yourpass -check-debugify input.ll

# Should report 100% preservation if correct
```

---

## Implications for HWML

### 1. Learn from LLVM's Approach

**Key lessons:**

**Use metadata, not magic:**
- Attach SourceInfo as metadata to IR nodes
- Don't encode locations in instruction opcodes
- Keep debug info separate from optimization decisions

**Three-tier strategy:**
- **IR level:** SourceInfo metadata + debug records
- **Mid-level (after elaboration):** Location tracking through transformations
- **Backend (code gen):** Emit source locators in Verilog

**Assignment tracking analog:**
- HWML has `let` bindings and variable assignments
- Track which AST nodes correspond to which assignments
- Preserve through NbE, unification, elaboration

### 2. Salvaging for Dependent Types

**LLVM salvages:** `x + 5` when `x` is deleted → express as `DW_OP_plus_uconst 5`

**HWML could salvage:**
- Type variable `α` unified to `Nat` → show substitution
- Metavariable `?m` solved to `replicate 8 true` → show solution
- Inlined function → show original source

**Example:**
```hwml
def foo (n : Nat) : Vec Bit n = replicate n false

-- After inlining and constant folding:
-- "replicate 8 false" in generated code
-- Debug info: "from foo(8) at source line 42"
```

### 3. Debug Info Invariance for HWML

**HWML should ensure:**
- Elaboration produces same result with/without debug info
- Type checking doesn't look at source locations
- Optimization passes ignore SourceInfo

**Testing:**
```bash
# Elaborate with full debug info
hwml-elab --debug=full input.hwml -o output1.hwmli

# Elaborate with no debug info
hwml-elab --debug=none input.hwml -o output2.hwmli

# Compare (should be identical modulo debug metadata)
diff <(hwml-strip-debug output1.hwmli) <(hwml-strip-debug output2.hwmli)
```

### 4. Location Tracking Through NbE

**Challenge:** Normalization by Evaluation transforms terms.

**LLVM analog:** SelectionDAG transforms IR nodes
**Solution:** Salvaging + SDDbgValue tracking

**HWML approach:**
```rust
// During NbE, track original term
struct NormalForm {
    value: Value,
    source_info: Option<SourceInfo>,  // From original term
}

// When quoting back:
fn quote(nf: &NormalForm) -> Term {
    let term = quote_value(&nf.value);
    term.set_source_info(nf.source_info);  // Preserve!
    term
}
```

**When elaboration synthesizes:**
```rust
// Generated term has no direct source
let synthesized_term = elaborate_implicit();
synthesized_term.set_source_info(
    SourceInfo::synthetic("elaborator generated")
);
```

### 5. Metavariable Debug Info

**LLVM** tracks instruction-produced values → `DBG_INSTR_REF`

**HWML** could track metavariable origins:
```rust
struct MetaVar {
    id: MetaId,
    created_at: SourceInfo,  // Where was ?m introduced?
    constrained_by: Vec<(ConstraintId, SourceInfo)>,  // What blocks it?
}
```

**Debugger output:**
```
Metavariable ?m (created at input.hwml:42:10)
  Constrained by:
    - Unification with Vec Bit ?n (line 45)
    - Occurs check with ?n (line 47)
  Status: Blocked, waiting for ?n
```

### 6. Hardware vs Elaboration Debug


**Two separate debug experiences:**

**Elaboration debugging (software):**
- Use DWARF (from LLVM or manual generation)
- Debug the meta-level computation
- Step through elaboration
- Inspect metavariables, constraints
- **LLVM parallel:** Debug the compiler itself

**Generated hardware debugging (waveforms):**
- Use source locators in Verilog
- Debug the object-level hardware
- View waveforms, signals
- Trace back to source
- **LLVM parallel:** Debug the compiled program

**Connection between them:**
- Elaboration step references source location
- Generated hardware preserves source location
- Bidirectional mapping

---

## Summary: Key Takeaways

### How LLVM Preserves Debug Info

1. **Frontend generates:**
   - `!DICompileUnit`, `!DIFile`, `!DISubprogram` metadata
   - `llvm.dbg.value`/`llvm.dbg.assign` for variables
   - `DebugLoc` on every instruction

2. **Optimizations update:**
   - `setDebugLoc()` when replacing instructions
   - `replaceAllUsesWith()` auto-updates debug intrinsics
   - `salvageDebugInfo()` when deleting referenced values
   - Assignment tracking for robust alloca handling

3. **Backend extends:**
   - `LiveDebugValues` propagates locations through CFG
   - Register allocation preserves via `DBG_INSTR_REF`
   - `DwarfDebug` emits location lists

### What Happens When Optimized Away

**Best case:** Value expressed with `DIExpression`
```llvm
; x = y + 5, but x is eliminated
llvm.dbg.value(y, !x, !DIExpression(DW_OP_plus_uconst, 5))
; Debugger shows x = y + 5
```

**Worst case:** `undef`
```llvm
llvm.dbg.value(undef, !x, !DIExpression())
; Debugger shows "optimized out"
```

**Middle ground:** Partial information
```
; Variable available in some location ranges, not others
DW_AT_location: [0x1000-0x1050): DW_OP_reg0
                ; [0x1050-...): <no location>
```

### Debug Info Consumption (Backend)

1. **SelectionDAG:**
   - Converts `llvm.dbg.*` → `SDDbgValue`
   - Attaches to DAG nodes
   - Salvages when nodes deleted

2. **Instruction Selection:**
   - Converts `SDDbgValue` → `DBG_VALUE` MachineInstr
   - May lose info if value not materialized

3. **Register Allocation:**
   - `DBG_INSTR_REF` survives better than `DBG_VALUE`
   - Tracks values through register moves

4. **LiveDebugValues:**
   - Extends location ranges
   - Inserts `DBG_VALUE` at block boundaries
   - Creates complete picture

5. **AsmPrinter:**
   - Collects all `DBG_VALUE` instructions
   - Builds location lists
   - Emits DWARF `.debug_info`, `.debug_loc`, `.debug_line`

---

## References

### LLVM Documentation
- **Source Level Debugging** - https://llvm.org/docs/SourceLevelDebugging.html
- **How to Update Debug Info** - https://llvm.org/docs/HowToUpdateDebugInfo.html
- **Assignment Tracking** - https://llvm.org/docs/AssignmentTracking.html
- **Instruction Referencing** - https://llvm.org/docs/InstrRefDebugInfo.html
- **RemoveDIs Migration** - https://llvm.org/docs/RemoveDIsDebugInfo.html

### Key Classes
- `llvm::DIBuilder` - Create debug metadata
- `llvm::DbgVariableRecord` - New debug record format
- `llvm::DwarfDebug` - DWARF emission
- `llvm::LiveDebugValues` - Location propagation
- `llvm::SDDbgValue` - SelectionDAG debug info

### GitHub Issues
- **#37076** - Meta: Make passes debug info invariant
- **#54796** - SROA affects DWARF ranges
- **#54757** - InstCombine causes undef dbg value
- **#55115** - SimplifyCFG critical edge problem

### Related HWML Docs
- `wiki/research/debug-info-systems.md` - Software debug formats (DWARF overview)
- `wiki/research/hardware-debug-info.md` - Hardware debug (waveforms, VCS)
- `design/to-ingest/debug-info-research.md` - Original DWARF research
- `design/to-ingest/location-information-design.md` - HWML location architecture

---

## See Also

- [[research/debug-info-systems]] - DWARF, PDB, source maps overview
- [[research/hardware-debug-info]] - Hardware simulation debug (VCD, FSDB)
- [[decisions/ADR-001-lcf-kernel]] - Kernel architecture (error reporting)
- [[entities/nbe]] - Normalization by Evaluation (preserving source info through NbE)

---

**Status:** Research complete. Ready for implementation planning and ADR creation.

**Key insight:** LLVM's debug info system is a sophisticated balance of:
- **Metadata representation** (separate from IR)
- **Transformation tracking** (update, merge, salvage)
- **Best-effort preservation** (undef when impossible)
- **Backend reconstruction** (LiveDebugValues fills gaps)

HWML can adopt similar strategies for both elaboration (software-style DWARF) and generated hardware (source locators + waveforms).
```cpp
// Merging two instructions with different locations
DebugLoc DL = DILocation::getMergedLocation(Loc1, Loc2);
NewInst->setDebugLoc(DL);
```

**Drop location when:**
- No clear source correspondence
- Speculative/hoisted instruction

**Example (drop):**
```cpp
// Instruction has no source equivalent
SpeculativeInst->dropLocation();
```

### Rule 2: Variable Location Updates

**Three intrinsics/records for different scenarios:**

#### `llvm.dbg.declare` - Address of variable
- "Variable X lives at alloca %ptr"
- Used when variable has fixed memory location
- **Discouraged** - being phased out
- SROA/mem2reg can invalidate

**Problem:**
```llvm
%x.addr = alloca i32
call void @llvm.dbg.declare(metadata i32* %x.addr, ...)
; Later, mem2reg promotes alloca away
; Debug info becomes stale!
```

#### `llvm.dbg.value` - Value of variable
- "Variable X has value %val"
- Used for SSA values
- **Preferred** for most variables
- Updated by optimizations

**Example:**
```llvm
%y = add i32 %x, 1
call void @llvm.dbg.value(metadata i32 %y, metadata !16, ...)
; If %y gets CSE'd to %z:
call void @llvm.dbg.value(metadata i32 %z, metadata !16, ...)
```

#### `llvm.dbg.assign` - Assignment tracking (newest)
- Tracks both value AND memory location
- Defers decision about register vs memory
- Survives SROA, mem2reg, etc.
- **Recommended** for new frontends

**Key insight:**
- Track assignment, not just location
- Let LLVM decide register/memory after optimizations
- Provides most accurate debug info

### Rule 3: What Happens When Optimized Away

**Scenario 1: Dead code elimination**
```llvm
%x = add i32 1, 2
call void @llvm.dbg.value(metadata i32 %x, metadata !10, ...)
; InstCombine constant-folds to:
call void @llvm.dbg.value(metadata i32 3, metadata !10, ...)
; Variable still available, now constant!
```

**Scenario 2: Value truly eliminated**
```llvm
%x = add i32 %a, %b
call void @llvm.dbg.value(metadata i32 %x, metadata !10, ...)
; Later, if %x is dead and eliminated:
call void @llvm.dbg.value(metadata i32 undef, metadata !10, ...)
; Variable shows as "optimized out" in debugger
```

**Scenario 3: Salvaging (best effort)**
- If value can be recomputed, emit expression
```llvm
%x = add i32 %y, 5
; If %x is eliminated but %y remains:
call void @llvm.dbg.value(metadata i32 %y, metadata !10,
                          !DIExpression(DW_OP_plus_uconst, 5))
; Debugger can compute: x = y + 5
```

**Scenario 4: Control flow changes**
- SimplifyCFG can eliminate basic blocks
- Creates critical edges with no place for debug info
- **Current limitation:** Variable unavailable on some paths

**GitHub Issue #55115 example:**
```
Before SimplifyCFG:           After SimplifyCFG:
  Block 1                       Block 1
    ↓                             ↓
  Block 4 (assignment)         (critical edge, no block!)
    ↓                             ↓
  Block 5                       Block 5
```
- Assignment in Block 4 has nowhere to go
- Can't put in Block 1 (affects other paths)
- Can't put in Block 5 (wrong semantics)
- Result: Variable unavailable

---

## Optimization Pass Instrumentation

### Assignment Tracking

**Modern approach** for handling alloca-based variables through SROA/mem2reg.
