# Debug Information Research for HWML

## Overview

Research into how programming languages generate, store, and consume debug
information to enable source-level debugging of compiled code.

**Key Question**: How should HWML generate debug information to support:
- Source-level debugging (GDB, LLDB)
- Stack traces with source locations
- Variable inspection at runtime
- Debugging optimized code

---

## Debug Information Formats

### 1. DWARF (Debugging With Attributed Record Formats)

**Standard format for Unix/Linux** (ELF binaries)

**Current version**: DWARF 5 (2017), DWARF 6 in draft

**Structure**:
```
.debug_info      - Type, variable, function information (DIEs - Debug Info Entries)
.debug_line      - Maps machine addresses to source line numbers
.debug_frame     - Call frame unwinding information (stack traces)
.debug_abbrev    - Abbreviation codes for DIEs (compression)
.debug_str       - String table (shared strings across debug info)
.debug_loc       - Variable location lists (tracks variables through registers/memory)
.debug_ranges    - Address range lists
.debug_macinfo   - Macro definitions
.debug_types     - Type information (merged into .debug_info in DWARF 5)
```

**Debug Information Entries (DIEs)**:
- Tree structure representing program structure
- Tags: `DW_TAG_compile_unit`, `DW_TAG_subprogram`, `DW_TAG_variable`,
  `DW_TAG_base_type`, `DW_TAG_inlined_subroutine`, etc.
- Attributes: `DW_AT_name`, `DW_AT_type`, `DW_AT_location`, `DW_AT_low_pc`,
  `DW_AT_high_pc`, etc.

**Example DIE hierarchy**:
```
DW_TAG_compile_unit
  DW_AT_name: "myfile.hwml"
  DW_AT_language: DW_LANG_C  (or DW_LANG_lo_user + offset for custom lang)
  DW_AT_producer: "hwml compiler 0.1.0"
  DW_AT_stmt_list: <offset into .debug_line>
  
  DW_TAG_subprogram
    DW_AT_name: "foo"
    DW_AT_type: <ref to return type>
    DW_AT_low_pc: 0x401000
    DW_AT_high_pc: 0x401050
    
    DW_TAG_formal_parameter
      DW_AT_name: "x"
      DW_AT_type: <ref to Int type>
      DW_AT_location: <location list>
```

**Location expressions** (`DW_AT_location`):
- Describe where a variable lives at different points in execution
- Can be in register, on stack, or optimized out
- Examples:
  - `DW_OP_fbreg -24` - on stack, 24 bytes below frame pointer
  - `DW_OP_reg0` - in register 0
  - `DW_OP_addr 0x12345` - at fixed address
  - Location lists: different locations at different PC ranges

---

### 2. PDB (Program Database) - Microsoft Windows

**Proprietary format** for Windows binaries

**Structure**:
- Container format (MSF - Multi-Stream File)
- Stream 0: PDB header
- Stream 1: PDB information (GUID, age, signature)
- Stream 2: TPI (Type Info) - all type definitions
- Stream 3: DBI (Debug Info) - module list, section contributions
- Stream 4: IPI (ID Info) - UDT definitions
- Streams 5+: per-module debug info (symbols, line numbers)

**CodeView format**: Inside PDB, symbol/type info uses CodeView format
- Originally separate `.dbg` files, now embedded in PDB
- Compiler emits CodeView records to object files (`.obj`)
- Linker merges into PDB, deduplicates types, builds indices

**Key differences from DWARF**:
- Separate file (`.pdb`), not embedded in executable
- Executable contains GUID+age to match correct PDB
- More centralized (one PDB per binary vs sections in ELF)
- Incremental linking: PDB can be updated without full relink

---

### 3. Source Maps (JavaScript/TypeScript/WebAssembly)

**JSON-based format** for mapping compiled code to source

**Structure**:
```json
{
  "version": 3,
  "file": "out.js",
  "sourceRoot": "",
  "sources": ["foo.ts", "bar.ts"],
  "sourcesContent": ["<source of foo.ts>", ...],  // optional
  "names": ["originalName1", "originalName2", ...],
  "mappings": "AAAA,CAAC,CAAE,CAAC,SAAS,CAAC,CAAC,CAAC"  // VLQ base64 encoded
}
```

**Mappings encoding** (VLQ base64):
- Maps each segment of generated code to original source
- Tuple: (gen_col, source_idx, orig_line, orig_col, name_idx)
- Semicolons separate lines, commas separate segments
- Relative encoding (deltas) for compactness

**Inline source maps**:
```javascript
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJz...
```

**Key insight**: Extremely compact format designed for download overhead
- No type information (not needed for JavaScript debugging)
- Focuses on line/column mapping only
- Can inline original source to avoid separate file fetches

---

## Split Debug Information

**Problem**: Debug info can be 2-10x larger than code itself
- Slows linking (linker must process/merge/relocate debug info)
- Increases binary size (deployment, memory usage)

**Solution**: Separate debug info from executable

### Split DWARF (`.dwo` files)

**Introduced in DWARF 4** ("Debug Fission")

**Mechanism**:
1. Compiler emits `.o` (object file) with lightweight "skeleton" debug info
2. Compiler emits `.dwo` (DWARF object file) with full debug info
3. Linker processes only `.o` files (fast!)
4. Debugger reads `.dwo` files on demand (via references from `.o`)

**Skeleton info in `.o`**:
- Bare minimum for linking
- References to `.dwo` file
- Address ranges (for mapping PC → compilation unit)

**Full debug info in `.dwo`**:
- All types, variables, line info
- Not processed by linker, no relocations
- Shared across incremental builds (unchanged `.dwo` reused)

**Packed Split DWARF** (`.dwp` files):
- Package all `.dwo` files into single `.dwp` (DWARF package)
- Indexed for fast lookup
- Easier distribution than hundreds of `.dwo` files

**Example usage**:
```bash
# Compile with split DWARF
gcc -g -gsplit-dwarf foo.c  # Produces foo.o + foo.dwo

# Link (fast, doesn't touch .dwo)
gcc foo.o bar.o -o myapp

# Package for distribution
dwp -e myapp -o myapp.dwp  # Collects all .dwo into .dwp

# Debug
gdb myapp  # GDB automatically finds myapp.dwp or individual .dwo files
```

**Rust support**:
```bash
# Unpacked (separate .dwo per .o)
rustc -C split-debuginfo=unpacked

# Packed (single .dwp file)
rustc -C split-debuginfo=packed
```

**Benefits**:
- 40-70% reduction in linker memory usage
- 25-50% faster link times
- Smaller binaries (easier deployment)
- Incremental builds: unchanged `.dwo` not regenerated

---

## Generating Debug Info: LLVM Approach

Rust (via LLVM) uses **LLVM IR debug metadata** + **DIBuilder API**

### DIBuilder Workflow

**1. Create compile unit**:
```rust
let di_builder = DIBuilder::new(module);

let di_file = di_builder.create_file("myfile.hwml", "/path/to");

let di_cu = di_builder.create_compile_unit(
    DW_LANG_C,  // or custom language code
    di_file,
    "hwml compiler 0.1.0",
    is_optimized: false,
    flags: "",
    runtime_version: 0
);
```

**2. Create type definitions**:
```rust
// Basic type (Int)
let di_int_type = di_builder.create_basic_type(
    "Int",
    64,  // size in bits
    DW_ATE_signed  // encoding
);

// Function type
let di_fn_type = di_builder.create_subroutine_type(
    di_file,
    &[di_int_type, di_int_type],  // param types
    di_int_type  // return type
);
```

**3. Create function debug info**:
```rust
let di_subprogram = di_builder.create_function(
    di_cu,
    "foo",
    "foo",  // linkage name (mangled name if applicable)
    di_file,
    line_num: 10,
    di_fn_type,
    is_local: false,
    is_definition: true,
    scope_line: 10
);

// Attach to LLVM function
llvm_function.set_subprogram(di_subprogram);
```

**4. Set source locations on instructions**:
```rust
let di_loc = di_builder.create_debug_location(
    line: 12,
    column: 5,
    scope: di_subprogram,
    inlined_at: None
);

// Attach to every LLVM instruction
builder.set_current_debug_location(di_loc);
// ... emit LLVM IR ...
```

**5. Declare variables**:
```rust
// Local variable
let di_local_var = di_builder.create_auto_variable(
    di_subprogram,  // scope
    "x",
    di_file,
    line_num: 11,
    di_int_type
);

// Insert dbg.declare intrinsic
di_builder.insert_declare_at_end(
    alloca_inst,  // storage (stack slot)
    di_local_var,
    di_builder.create_expression(&[]),  // no DWARF expression
    di_loc,
    block
);
```

**6. Finalize**:
```rust
di_builder.finalize();  // Must call before emitting module
```

**Generated LLVM IR** (simplified):
```llvm
!0 = distinct !DICompileUnit(language: DW_LANG_C, file: !1, producer: "hwml compiler 0.1.0")
!1 = !DIFile(filename: "myfile.hwml", directory: "/path/to")
!2 = !DISubroutineType(types: !3)
!3 = !{!4, !4}  ; Int -> Int
!4 = !DIBasicType(name: "Int", size: 64, encoding: DW_ATE_signed)
!5 = distinct !DISubprogram(name: "foo", type: !2, file: !1, line: 10, unit: !0)
!6 = !DILocalVariable(name: "x", scope: !5, file: !1, line: 11, type: !4)

define i64 @foo(i64 %0) !dbg !5 {
entry:
  %x = alloca i64, !dbg !7
  call void @llvm.dbg.declare(metadata i64* %x, metadata !6, metadata !DIExpression()), !dbg !7
  ; ... rest of function ...
}

!7 = !DILocation(line: 11, column: 5, scope: !5)
```

**LLVM backend** translates this to DWARF sections in object file.

---

## Debugging Optimized Code

**Challenge**: Optimizations transform code, invalidating debug info

**Common problems**:
- Variables eliminated (dead code elimination)
- Variables promoted to SSA registers (no fixed memory location)
- Functions inlined (call stack doesn't match source)
- Loops unrolled/vectorized (line numbers repeat/scatter)

### Variable Location Tracking

**Approach 1: `dbg.declare`** (simple, imprecise):
- Attach debug info to stack `alloca` instruction
- Works only if variable stays in memory
- Mem2reg optimization promotes to register → location lost

**Approach 2: `dbg.value`** (precise, complex):
- Track variable value through SSA transformations
- Emit `llvm.dbg.value` intrinsic at each assignment
- Location can change: register, stack, constant, or "optimized out"

**Example**:
```llvm
; Before optimization
%x = alloca i64
store i64 %arg, i64* %x
call void @llvm.dbg.declare(metadata i64* %x, metadata !var_x, ...)
%val = load i64, i64* %x
%result = add i64 %val, 1

; After mem2reg (x promoted to register)
call void @llvm.dbg.value(metadata i64 %arg, metadata !var_x, ...)  ; x = arg
%result = add i64 %arg, 1
; x is in register (parameter), not memory
```

**DWARF location lists**:
- Different locations at different PC ranges
- Example: "x is in %rdi from 0x1000-0x1010, then on stack at [%rbp-8]
  from 0x1010-0x1050"

**LLVM `LiveDebugValues` pass**:
- Tracks variable values through code transformations
- Propagates `dbg.value` intrinsics across basic blocks
- Handles register spills/restores, inlining, etc.

**Assignment tracking** (newer approach):
- Track assignments explicitly (not just values)
- Defer decision "register vs memory" until after optimizations
- Better accuracy for complex transformations

**When variable can't be tracked**:
```llvm
call void @llvm.dbg.value(metadata undef, metadata !var_x, ...)
; Debugger shows "optimized out" or "<unavailable>"
```

### Inlining Debug Info

**Problem**: Function `bar()` inlined into `foo()`, but stack trace should show
both.

**DWARF solution**: `DW_TAG_inlined_subroutine`

**Example**:
```c
// Source
void bar() { crash(); }    // line 5
void foo() { bar(); }      // line 10

// After inlining
void foo() {
  crash();  // Physically in foo, logically from bar
}
```

**DWARF**:
```
DW_TAG_subprogram (foo)
  DW_AT_low_pc: 0x1000
  DW_AT_high_pc: 0x1020

  DW_TAG_inlined_subroutine (bar)
    DW_AT_abstract_origin: <ref to bar's abstract definition>
    DW_AT_low_pc: 0x1005
    DW_AT_high_pc: 0x1010
    DW_AT_call_file: 1
    DW_AT_call_line: 10
```

**Stack unwinding with inlining**:
1. Debugger sees PC = 0x1007 (inside inlined code)
2. Looks up compilation unit, finds `DW_TAG_subprogram` foo
3. Finds nested `DW_TAG_inlined_subroutine` bar at that PC
4. Reports stack trace as:
   ```
   #0 crash() at crash.c:1
   #1 bar() at bar.c:5 (inlined into foo)
   #2 foo() at foo.c:10
   ```

**Go's approach**:
- Generates inline tree in `pclntab` (PC-to-line table)
- Runtime `Callers()` expands inline frames dynamically
- No DWARF needed for stack traces (but DWARF also emitted for debuggers)

**Rust challenge**:
- MIR inlining happens before codegen
- Must preserve inlining info across MIR → LLVM IR boundary
- Rustc passes `InlineInfo` to LLVM backend, which creates
  `DW_TAG_inlined_subroutine` DIEs

---

## Storage Strategies

### 1. Embedded in Binary (Default)

**DWARF**: Debug sections in ELF binary
**PDB**: Separate `.pdb` file, but referenced by GUID in `.exe`

**Pros**:
- Simple: one file
- Always available (binary = debuggable)

**Cons**:
- Large binaries (5-10x code size)
- Slow linking (must process debug info)
- Deployment bloat

**When to use**: Development builds, small programs

### 2. Separate File

**DWARF**: `objcopy --only-keep-debug` extracts debug sections
**PDB**: Native format (always separate)

**Pros**:
- Smaller production binaries
- Debug info optional (download separately, "debuginfo" packages)

**Cons**:
- Must distribute/manage two files
- Debugger must locate separate file

**GNU debug link** (DWARF):
```bash
# Extract debug info
objcopy --only-keep-debug myapp myapp.debug

# Strip from binary
strip --strip-debug myapp

# Add reference
objcopy --add-gnu-debuglink=myapp.debug myapp
```

Binary now contains CRC32 checksum + filename. Debugger searches:
1. Same directory: `myapp.debug`
2. `.debug` subdirectory: `.debug/myapp.debug`
3. Global debug directory: `/usr/lib/debug/path/to/myapp.debug`

**When to use**: Production builds, Linux distro packages

### 3. Split DWARF

**Described above**: `.dwo` or `.dwp` files

**Pros**:
- Fastest linking (debug info not processed by linker)
- Efficient incremental builds (`.dwo` reused if source unchanged)
- Moderate deployment size (skeleton info in binary)

**Cons**:
- More complex build system (manage `.dwo` files)
- Debugger must support split DWARF

**When to use**: Large C++ projects, frequent incremental builds

### 4. Compressed Debug Sections

**DWARF v5**: `.zdebug_*` sections (zlib or zstd compressed)

**Example**:
```bash
gcc -gz=zstd myfile.c  # Compress debug sections with zstd
objcopy --compress-debug-sections=zlib myapp
```

**Benefit**: 30-50% size reduction, transparent to debugger

**Trade-off**: Slightly slower debugger startup (decompress on load)

### 5. Debug Info Servers

**Concept**: Central server hosts debug info, debugger fetches on demand

**Examples**:
- **Microsoft Symbol Server**: URL in PDB, debugger downloads
- **debuginfod** (Linux): HTTP server for debug info + source files
  - `export DEBUGINFOD_URLS="https://debuginfod.fedoraproject.org/"`
  - GDB/LLDB auto-fetch debug info by build-id

**Pros**:
- Zero deployment overhead (binaries contain no debug info)
- Centralized storage (no duplication)
- On-demand loading (fast debugger startup, download only used modules)

**Cons**:
- Requires infrastructure
- Network dependency
- Privacy concerns (leak build-id, stack trace info)

**When to use**: Large organizations, cloud deployments, open-source distros

---

## Recommendations for HWML

Based on research, here's what HWML should do:

### Phase 1: Basic DWARF via LLVM

**During codegen (HWML → LLVM IR)**:
1. Create `DICompileUnit` for each source file
2. Create `DISubprogram` for each elaborated function
3. Create `DIBasicType` for primitive types (Int, Bool, etc.)
4. Use `DW_LANG_C` initially (DWARF doesn't have dependent types lang code)
5. Set `!dbg` metadata on every LLVM instruction from `SourceRange`

**Minimal working debugger**:
- GDB can set breakpoints by line number
- Stack traces show function names + source locations
- No variable inspection yet (MIR doesn't have variable locations)

**Implementation**: In `hwml_codegen_llvm`, add `DebugInfoBuilder`:
```rust
struct DebugInfoBuilder<'ll> {
    di_builder: &'ll DIBuilder,
    di_compile_unit: &'ll DICompileUnit,
    di_files: HashMap<PathBuf, &'ll DIFile>,
    di_types: HashMap<TypeId, &'ll DIType>,
}

impl<'ll> DebugInfoBuilder<'ll> {
    fn create_compile_unit(&mut self, source_file: &Path) {
        let di_file = self.di_builder.create_file(
            source_file.file_name().unwrap().to_str().unwrap(),
            source_file.parent().unwrap().to_str().unwrap()
        );

        self.di_compile_unit = self.di_builder.create_compile_unit(
            DW_LANG_C,  // TODO: register custom language with DWARF committee
            di_file,
            format!("hwml compiler {}", env!("CARGO_PKG_VERSION")),
            is_optimized: false,  // TODO: check opt level
            "",  // flags
            0    // runtime version
        );
    }

    fn create_function_debug_info(
        &mut self,
        name: &str,
        llvm_fn: &'ll Function,
        source_range: SourceRange
    ) {
        let di_file = self.get_or_create_file(source_range.source.file_path());
        let di_fn_type = self.get_or_create_function_type(fn_type);

        let di_subprogram = self.di_builder.create_function(
            self.di_compile_unit,
            name,
            name,  // linkage name
            di_file,
            source_range.start_line(),
            di_fn_type,
            false,  // is_local
            true,   // is_definition
            source_range.start_line()
        );

        llvm_fn.set_subprogram(di_subprogram);
    }

    fn set_debug_location(
        &mut self,
        builder: &Builder<'ll>,
        source_range: SourceRange,
        scope: &'ll DIScope
    ) {
        let di_loc = self.di_builder.create_debug_location(
            source_range.start_line() as u32,
            source_range.start_column() as u32,
            scope,
            None  // inlined_at
        );

        builder.set_current_debug_location(di_loc);
    }
}
```

**Integration point**: In MIR → LLVM lowering, call `set_debug_location`
before emitting each LLVM instruction. Use `SourceRange` from MIR.

### Phase 2: Variable Location Tracking

**Challenge**: MIR is SSA (variables = values, not memory locations)

**Options**:

**Option A: `dbg.value` everywhere** (precise but complex):
- Emit `llvm.dbg.value` intrinsic every time a variable's value changes
- LLVM `LiveDebugValues` pass propagates through code
- Result: Accurate variable locations in optimized code

**Option B: `alloca` + `dbg.declare`** (simple but loses info in optimized code):
- For each MIR local variable, create stack `alloca`
- Store/load from alloca instead of using SSA values directly
- Mem2reg pass promotes to SSA later (debug info lost)
- Result: Variables visible in `-O0`, "optimized out" in `-O2`

**Recommendation**: Start with Option B (simple), migrate to Option A later.

**Implementation**:
```rust
// In function prologue
for (local_id, local) in mir_body.locals.iter_enumerated() {
    let alloca = builder.build_alloca(local.ty, &local.name);

    let di_local_var = debug_info.di_builder.create_auto_variable(
        di_subprogram,
        &local.name,
        di_file,
        local.source_range.start_line(),
        di_type_of(local.ty)
    );

    debug_info.di_builder.insert_declare(
        alloca,
        di_local_var,
        di_expression_empty(),
        current_debug_location,
        current_block
    );

    local_allocas.insert(local_id, alloca);
}
```

### Phase 3: Split Debug Info

**Default strategy**: Separate file (`.hwml.debug`)

**Rationale**:
- HWML binaries should be small (deploy to FPGA, embedded systems)
- Debug info can be 5-10x larger than code
- Most deployments don't need debug info

**Generation**:
```bash
# Build with debug info
hwml build --debug myapp.hwml

# Produces:
# - myapp (executable, stripped)
# - myapp.debug (DWARF sections)
# - myapp links to myapp.debug via build-id
```

**Linux packaging**:
```
/usr/bin/myapp                          # Stripped binary
/usr/lib/debug/.build-id/ab/cdef123...  # Debug info (by build-id)
```

**Debugger usage**:
```bash
gdb myapp
# GDB auto-finds myapp.debug via build-id in .note.gnu.build-id section
```

**Optional**: Support `-Csplit-debuginfo=packed` for `.dwp` files (large
projects).

### Phase 4: Dependent Types in Debug Info

**Problem**: DWARF has no native representation for dependent types

**Example**:
```hwml
def Vec (n : Nat) (a : Type) : Type = ...
def foo : Vec 10 Int = ...
```

How to represent `Vec 10 Int` in DWARF?

**Option 1: Mangle into name**:
- DIE name: `Vec<10, Int>`
- Type: `DW_TAG_structure_type`
- Works in GDB, but no semantic understanding

**Option 2: Custom DWARF extension** (via `DW_TAG_*` vendor range):
- Define `DW_TAG_lo_user + 1` = dependent type application
- Attributes: base type, arguments (mix of types and values)
- Requires patching GDB/LLDB to understand (unlikely)

**Option 3: Type erasure** (practical):
- Represent `Vec 10 Int` as `Vec` (erase index)
- Or `Vec_10` (monomorphize)
- Debugger shows less precise type, but functional

**Recommendation**: Start with Option 1 (names), investigate Option 3 for common
cases.

**Pretty-printing**: Write GDB Python script to parse type names and display
nicely:
```python
# ~/.gdbinit or .gdbinit in project root
import gdb

class VecPrinter:
    def __init__(self, val):
        self.val = val

    def to_string(self):
        # Parse type name "Vec<10, Int>" and format
        return f"Vec({self.val['length']}) = {self.val['data']}"

gdb.pretty_printers.append(VecPrinter)
```

### Phase 5: Custom Language Registration

**DWARF language codes**: `DW_LANG_*` enum (C, C++, Fortran, etc.)

**Custom languages**: `DW_LANG_lo_user` (0x8000) through `DW_LANG_hi_user`
(0xffff)

**Registration** (optional, for tooling ecosystem):
- Request assignment from DWARF committee: https://dwarfstd.org/
- Example: Julia = `DW_LANG_Julia` (0x001a), added in DWARF 5

**For HWML**:
```rust
const DW_LANG_HWML: u32 = DW_LANG_lo_user + 1;  // Or wait for official assignment

di_builder.create_compile_unit(
    DW_LANG_HWML,
    // ...
);
```

**Benefit**: Debuggers can customize behavior (e.g., expression evaluator, name
mangling) based on language.

**Current**: Use `DW_LANG_C` (universal fallback).

---

## Performance Considerations

### Debug Info Size

**Typical sizes** (C++ example):
- Code: 10 MB
- Debug info (DWARF): 50-100 MB
- Compressed debug info: 30-60 MB
- Split DWARF skeleton: 5 MB + `.dwo` files 40-80 MB

**HWML prediction**: Larger due to dependent types
- Each monomorphic instantiation needs separate debug info
- `Vec 10 Int`, `Vec 20 Int`, `Vec 10 Bool` = 3 separate types in DWARF
- Mitigation: Type deduplication (share `Vec` structure)

### Compilation Time

**DWARF generation overhead**: 5-15% of total compile time

**Optimized builds**: 30-50% longer with debug info (more for split DWARF)

**Recommendation**:
- `-O0 --debug`: Default for development (fast compile, debuggable)
- `-O2`: Default for release (no debug info)
- `-O2 --debug`: Opt-in for release debugging (slower compile, larger binary)

### Debugger Performance

**Startup time**: Loading debug info can take seconds for large binaries

**Split DWARF advantage**: Only load `.dwo` for modules actually debugged

**Compressed debug sections**: Slight slowdown (decompress on load) but smaller
downloads

**Index files** (`.gdb_index`, `.debug_names`):
- Accelerate debugger symbol lookup
- Generated by `gdb-add-index` or `objcopy --add-gnu-debuglink`
- 2-10x faster debugger startup

---

## Testing Strategy

### 1. Unit Tests: Debug Info Generation

**Test DIBuilder calls**:
```rust
#[test]
fn test_debug_info_compile_unit() {
    let context = Context::create();
    let module = context.create_module("test");
    let di_builder = DIBuilder::new(&module);

    let di_cu = create_compile_unit_for_test(&di_builder);

    assert_eq!(di_cu.get_language(), DW_LANG_C);
    assert_eq!(di_cu.get_producer(), "hwml compiler 0.1.0");
}
```

### 2. Integration Tests: DWARF Validation

**Parse generated DWARF**:
```rust
#[test]
fn test_dwarf_output() {
    let binary = compile("tests/debug/simple.hwml", "--debug");

    let dwarf = gimli::Dwarf::load(&binary).unwrap();

    // Check compile unit exists
    let mut units = dwarf.units();
    let unit = units.next().unwrap().unwrap();

    // Check function DIE exists
    let mut entries = unit.entries();
    let (_, die) = entries.next().unwrap().unwrap();
    assert_eq!(die.tag(), gimli::DW_TAG_subprogram);

    // Check has line info
    let line_program = dwarf.line_program(&unit).unwrap();
    assert!(line_program.header().file_names().len() > 0);
}
```

**Libraries**: Use `gimli` (Rust DWARF parser) for validation.

### 3. End-to-End Tests: Debugger Integration

**GDB scripting**:
```bash
#!/bin/bash
# tests/debug/test_gdb.sh

hwml build --debug tests/debug/breakpoint.hwml -o /tmp/test_debug

gdb -batch -ex 'file /tmp/test_debug' \
    -ex 'break breakpoint.hwml:10' \
    -ex 'run' \
    -ex 'backtrace' \
    -ex 'quit'
```

**Expected output**:
```
Breakpoint 1, foo () at breakpoint.hwml:10
10      let x = 42
#0  foo () at breakpoint.hwml:10
#1  main () at breakpoint.hwml:15
```

**CI Integration**: Run debugger tests on each PR (requires GDB/LLDB installed).

---

## Summary Table

| Feature | Phase | Complexity | Benefit |
|---------|-------|------------|---------|
| Basic line info (breakpoints) | 1 | Low | Essential |
| Function names in stack traces | 1 | Low | Essential |
| Variable inspection (`print x`) | 2 | Medium | High |
| Optimized code debugging | 2 | High | Medium |
| Separate debug files | 3 | Low | High (deployment) |
| Split DWARF (`.dwo`) | 3 | Medium | Medium (large projects) |
| Dependent type pretty-printing | 4 | Medium | Low (niche) |
| Custom language code | 5 | Low | Low (future-proofing) |
| Inlining debug info | Later | High | Medium |

---

## References

[1] DWARF 5 Standard: https://dwarfstd.org/dwarf5std.html
[2] DWARF 6 Draft: https://dwarfstd.org/
[3] LLVM DIBuilder: https://llvm.org/doxygen/classllvm_1_1DIBuilder.html
[4] Rust debug info: https://rustc-dev-guide.rust-lang.org/debuginfo/
[5] Split DWARF: https://gcc.gnu.org/wiki/DebugFission
[6] PDB format: https://github.com/microsoft/microsoft-pdb
[7] Source maps: https://web.dev/source-maps
[8] GDB documentation: https://sourceware.org/gdb/current/onlinedocs/gdb/
[9] LLVM debug metadata: https://llvm.org/docs/SourceLevelDebugging.html
[10] Assignment tracking: https://llvm.org/docs/AssignmentTracking.html
