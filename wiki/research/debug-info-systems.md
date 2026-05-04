# Debug Information Representation Across Systems

**Type:** Research
**Last Updated:** 2026-05-02
**Purpose:** Survey of how different compiler systems represent debug information beyond simple source locations

---

## Overview

Debug information serves to bridge the gap between **compiled code** and **source code**, enabling debuggers to:
- Map instruction addresses to source lines
- Inspect variable values
- Understand type layouts
- Navigate call stacks
- Set breakpoints
- Single-step through code

This goes **beyond simple location tracking** to include type information, variable lifetimes, optimization effects, and runtime state.

---

## Categories of Debug Information

### 1. **Location Information** (Basic)
Maps compiled code back to source:
- **File:Line:Column** - Where in source code
- **Instruction address → source location** - For breakpoints, stack traces
- **Inlined function tracking** - Which function is actually running

### 2. **Type Information** (Structural)
Describes data layout and semantics:
- **Type names and sizes** - `struct Foo { ... }` with byte layout
- **Field offsets** - Where each field is in memory
- **Inheritance/composition** - OOP hierarchies, trait objects
- **Generic instantiations** - `Vec<i32>` vs `Vec<String>` are different types
- **Enums/sum types** - Discriminant layout and variant fields

### 3. **Variable Information** (Scope & Lifetime)
Tracks where variables exist:
- **Location lists** - Variable moves between registers/stack during execution
- **Scope ranges** - When variable is valid (lexical scope + optimizations)
- **Parameter passing** - How arguments are passed (register, stack, split)
- **Captured variables** - Closures and their environments

### 4. **Function/Procedure Information**
Describes executable units:
- **Entry points** - Where functions start
- **Prologue/epilogue** - Stack frame setup/teardown
- **Frame base** - How to find local variables
- **Return address** - For unwinding
- **Calling convention** - How arguments are passed

### 5. **Optimization Information** (Advanced)
Tracks compiler transformations:
- **Inlining** - Which calls were inlined where
- **Dead code elimination** - Variables that were optimized away
- **Constant folding** - Values known at compile time
- **Register allocation** - Variable lives in different places over time

---

## Major Debug Information Formats

### DWARF (Dominant Format)

**Used by:** GCC, Clang, Rust, GHC, LLVM-based compilers
**Platforms:** Linux, macOS, BSD, most POSIX systems
**Current Version:** DWARF 5 (2017), DWARF 6 in draft (2024)

**Structure:**
```
.debug_info      - Debug Information Entries (DIEs) - tree structure
.debug_abbrev    - Abbreviation codes (compression)
.debug_line      - Line number program (compact mapping)
.debug_str       - String table (deduplicated)
.debug_loc       - Location lists (variable tracking)
.debug_ranges    - Address ranges
.debug_frame     - Call frame information (unwinding)
.debug_aranges   - Accelerator for address lookups
.debug_pubnames  - Accelerator for global names
.debug_types     - Type information (merged into .debug_info in DWARF 5)
```

**Key Concepts:**

**Debug Information Entries (DIEs):**
- Tree structure describing program
- Each DIE has a tag (DW_TAG_variable, DW_TAG_subprogram, etc.)
- Attributes carry information (DW_AT_name, DW_AT_type, DW_AT_location)

**Location Expressions:**
- Stack-based VM for computing variable locations
- `DW_OP_reg5` - variable in register 5
- `DW_OP_fbreg -16` - variable at frame base offset -16
- `DW_OP_plus_uconst` - add constant offset

**Location Lists:**
- Variable location changes over instruction ranges
- `[0x1000-0x1020]: DW_OP_reg3` (in register)
- `[0x1020-0x1050]: DW_OP_fbreg -8` (spilled to stack)

**Split DWARF (DWO files):**
- Separate `.dwo` files for debug info
- Faster linking (debug info not in main link)
- Used by Rust, recommended for large projects

**DWARF 5 Improvements:**
- Merged `.debug_types` into `.debug_info`
- New `.debug_names` index (faster lookup)
- More compact location/range lists
- Better support for LLVM and modern compilers

---

### PDB (Microsoft Format)

**Used by:** MSVC, Windows debuggers
**Platform:** Windows exclusively

**Structure:**
- Proprietary binary format (not fully documented)
- Multiple streams containing different information
- Type information in Type Server (separate file)
- Similar concepts to DWARF but different encoding

**Key Features:**
- Supports incremental linking
- Edit & Continue debugging
- Source indexing for source control integration

---

### Source Maps (Web)

**Used by:** JavaScript, TypeScript, compiled-to-JS languages
**Platform:** Web browsers, Node.js

**Format:** JSON mapping from generated to original source
```json
{
  "version": 3,
  "sources": ["original.ts"],
  "names": ["variable", "function"],
  "mappings": "AAAA,CAAC,CAAC;IACE,CAAC"
}
```

**Limited to:**
- Source location mapping
- Variable name mapping
- No type information or variable lifetimes

---

## Implementation Approaches

### LLVM's Debug Info System

**How it works:**
1. **Frontend** (rustc, clang) generates LLVM IR with debug metadata
2. **LLVM** translates metadata to target debug format (DWARF/PDB)
3. **Debugger** reads debug info to interpret running program

**LLVM Metadata Nodes:**
```llvm
!DICompileUnit - represents a compilation unit
!DIFile - source file
!DISubprogram - function
!DILocalVariable - local variable
!DILocation - source location
!DICompositeType - struct/class/union
!DIBasicType - primitive type
```

**DIBuilder API:**
- `createCompileUnit()` - top-level compilation unit
- `createFunction()` - function with signature
- `createAutoVariable()` - local variable
- `createBasicType()` - int, float, etc.
- `createStructType()` - struct layout

**Example (Rust → LLVM → DWARF):**
```rust
fn foo(x: i32) -> i32 {
    let y = x + 1;
    y
}
```

Generates LLVM metadata:
```llvm
!DISubprogram(name: "foo",
              type: !1,  // (i32) -> i32
              file: !2,  // source file
              line: 1,
              scopeLine: 1,
              variables: !3)  // [x, y]

!DILocalVariable(name: "x",
                 arg: 1,
                 scope: !0,  // foo
                 type: !4,   // i32
                 file: !2,
                 line: 1)

!DILocalVariable(name: "y",
                 scope: !0,
                 type: !4,
                 file: !2,
                 line: 2)
```

Which becomes DWARF:
```
DW_TAG_subprogram
  DW_AT_name: "foo"
  DW_AT_type: <reference to i32 -> i32 signature>
  DW_AT_decl_file: 1
  DW_AT_decl_line: 1

  DW_TAG_formal_parameter
    DW_AT_name: "x"
    DW_AT_type: <reference to i32>
    DW_AT_location: <location expression>

  DW_TAG_variable
    DW_AT_name: "y"
    DW_AT_type: <reference to i32>
    DW_AT_location: <location expression>
```

---

### Rust's Approach

**Compilation Pipeline:**
1. **MIR** (Mid-level IR) → rustc inspects
2. **LLVM IR** → rustc generates with debug metadata via DIBuilder
3. **Object file** → LLVM CodeGen produces DWARF
4. **Debugger** → gdb/lldb reads DWARF

**Rust-specific challenges:**
- **Enums with data** - Complex discriminant + payload layout
- **Trait objects** - Fat pointers (data + vtable)
- **Closures** - Synthetic types, captured environment
- **Async** - State machines, generator layout

**Solutions:**
- Output debug info similar to C++ (works with existing debuggers)
- Additional Rust-specific metadata for better experience
- GDB/LLDB have Rust pretty-printers for better value display

**Debug levels:**
- `debuginfo=0` (none) - No debug info
- `debuginfo=line-tables-only` - Just line tables (backtraces)
- `debuginfo=1` (limited) - No type/variable info
- `debuginfo=2` (full) - Complete debug info

**Split debug info:**
- `-C split-debuginfo=unpacked` - Separate `.dwo` files per compilation unit
- `-C split-debuginfo=packed` - Single `.dwp` package file
- Dramatically faster linking for large projects

---

### GHC (Haskell) Approach

**Challenges for functional languages:**
- **Lazy evaluation** - Values computed on demand, not linearly
- **Thunks** - Unevaluated computations
- **Garbage collection** - Heap layout changes
- **Higher-order functions** - Functions as values

**GHC's strategy:**
- Generate DWARF with `-g` flag
- Basic blocks as DIEs
- Function entry points
- Limited variable tracking (due to GC and evaluation order)
- **Primarily useful for:**
  - Profiling (ghc-prof, eventlog)
  - Backtraces with `haskellerr`
  - Performance analysis with `perf`

**Limitations:**
- Can't easily inspect thunks
- Lazy evaluation makes stepping unintuitive
- GC moves data, location lists are approximate



---

## HWML's Current State & Design

### Existing Infrastructure

From `design/to-ingest/debug-info-research.md` and codebase exploration:

**Location Tracking (Partially Implemented):**
- `SourceFileId` - Salsa-interned file identifiers (library + path)
- `SourceInfo` - File vs Synthetic sources
- `SourceRange` - Currently byte offsets, **should be Line:Column**
- `LineInfo` - Utility for offset → (line, col) conversion

**Error Reporting (Working):**
- `ElabError` variants carry `Option<SourceRange>`
- LSP diagnostics with location information
- Salsa database for caching and invalidation

**Design Documents (Comprehensive):**
- Complete DWARF 5 research and recommendations
- Location architecture with Line:Column design
- LSP metadata for `.hwmli` files
- Split debug info strategy

### Planned Implementation (from design docs)

**Phase 1: Basic Debug Info**
- Line tables (`.debug_line`)
- Function names and entry points
- Minimal info for GDB breakpoints
- Stack traces with function names

**Phase 2: Variable Inspection**
- Location lists for variables
- Type information (DWARF DIEs)
- Parameter tracking
- Local variable scope

**Phase 3: Advanced Features**
- Split debug info (`.hwml.debug` files)
- Optimization tracking (inlining, DCE)
- Source-level stepping through meta-level code
- Type parameter instantiation tracking

**Recommendations:**
- Use **DWARF 5** (modern, well-supported)
- Use **LLVM DIBuilder** for generation (if using CIRCT backend)
- Use **DW_LANG_C** initially (DWARF lacks dependent type codes)
- Consider **custom DWARF extensions** for dependent types

---

## Special Considerations for HWML

### 1. Two-Level Type Theory (Staging)

**Challenge:** Code has meta-level (compile-time) and object-level (hardware) components.

**Possible approaches:**

**Option A: Debug meta-level only**
- Show elaboration as it happens
- Limited for hardware debugging

**Option B: Debug object-level only**
- Show final generated hardware
- Lose connection to meta-level source

**Option C: Dual debug info (both levels)** ← Recommended
- Meta-level: For elaboration debugging
- Object-level: For hardware debugging
- Most complete solution

### 2. Dependent Types

**DWARF limitations:** No native support for types depending on values.

**Workarounds:**
1. Represent as C++ templates (immediate)
2. Custom DWARF extension (long-term)
3. Type erasure with metadata
4. **Pretty-printer scripts** (GDB/LLDB) ← Start here

### 3. Hardware vs Execution

**Two debug scenarios:**
- **Elaboration debugging:** Standard DWARF for elaborator
- **Hardware debugging:** Waveform viewers (VCD), not software debugging
- **Source mapping:** Link generated Verilog back to HWML source

---

## Recommendations for HWML

### Short Term
1. Complete location tracking (Line:Column)
2. Basic DWARF line tables (if using CIRCT)
3. Elaborator debugging infrastructure

### Medium Term
4. Full type debug info
5. Variable location tracking
6. Split debug info

### Long Term
7. Hardware source mapping
8. Custom DWARF extensions
9. Interactive elaboration debugging

---

## References

**Standards:**
- DWARF 5: https://dwarfstd.org/dwarf5std.html
- LLVM Debug Info: https://llvm.org/docs/SourceLevelDebugging.html

**Implementation:**
- Rust: https://rustc-dev-guide.rust-lang.org/debuginfo/intro.html
- GHC: https://ghc.gitlab.haskell.org/ghc/doc/users_guide/debug-info.html

**HWML Design:**
- `design/to-ingest/debug-info-research.md`
- `design/to-ingest/location-information-design.md`
- `design/to-ingest/lsp-object-file-research.md`

---

**Status:** Research complete, ready for implementation planning.