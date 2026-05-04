# Hardware Debug Information Systems

**Type:** Research
**Last Updated:** 2026-05-03
**Purpose:** Survey of debug information representation in hardware tools (simulators, synthesis, waveform viewers)

---

## Overview

Hardware debugging is fundamentally different from software debugging:
- **Time-based behavior:** Signals change over clock cycles, not sequential execution
- **Massive parallelism:** Thousands of signals changing simultaneously
- **Waveform-centric:** Visual inspection of signal transitions over time
- **Hierarchy preservation:** Module/instance structure is critical
- **Simulation vs Synthesis:** Different debug needs at different stages

This document covers how debug information is represented in hardware tools, particularly:
- **VCS/Verdi** (Synopsys simulation and debug)
- **Waveform formats** (FSDB, VCD)
- **Chisel/FIRRTL** (Source locators)
- **Synthesis tools** (RTL to gate-level mapping)

---

## Waveform Formats

### VCD (Value Change Dump)

**Standard format** for representing signal transitions over time.

**Structure:**
```vcd
$date
   Date text.
$end
$version
   VCS version 2023.12
$end
$timescale 1ns $end
$scope module testbench $end
$var wire 1 ! clk $end
$var wire 8 " data [7:0] $end
$var reg 1 # reset $end
$upscope $end
$enddefinitions $end
$dumpvars
0!
b00000000 "
1#
$end
#0
1!
#10
0!
b00001010 "
#20
1!
0#
```

**Key concepts:**
- **Scope/hierarchy:** `$scope module name $end` ... `$upscope`
- **Variable declaration:** `$var type width code name $end`
  - `type`: wire, reg, integer, etc.
  - `width`: bit width
  - `code`: Short identifier (!, ", #, etc.)
  - `name`: Signal name
- **Value changes:** `#timestamp` followed by value updates
  - `0!` - single bit signal ! goes to 0
  - `b00001010 "` - vector signal " becomes 8'b00001010

**Limitations:**
- Text-based, can be very large
- No compression
- Limited metadata (just signal names and hierarchy)
- No type information beyond bit width

### FSDB (Fast Signal DataBase)

**Proprietary format** from Synopsys (Verdi), optimized for performance.

**Advantages over VCD:**
- **Indexed:** Random access to any time point
- **Compressed:** 3-5X smaller files
- **Faster:** 1.5-2X faster dumping during simulation
- **Rich metadata:** Preserves more design information
- **Dynamic aliasing:** Signals with same activity are merged

**Generation (SystemVerilog):**
```systemverilog
initial begin
  $fsdbDumpfile("wave.fsdb");
  $fsdbDumpvars(0, testbench);  // depth=0 means all
  $fsdbDumpMDA();  // Include multi-dimensional arrays
end
```

**Depth parameter:**
- `0`: All signals in specified instance and all sub-instances
- `1`: Only signals in current instance (no sub-modules)
- `2`: Current instance + one level of sub-instances

**Options:**
- `+all` - Everything (memory, MDA, packed arrays, structs, unions)
- `+IO_Only` - Only port signals
- `+Reg_Only` - Only registers
- `+mda` - Multi-dimensional arrays
- `+parameter` - Include parameters
- `+functions` - Enable function dumping

**Conversion:**
```bash
# FSDB to VCD (for compatibility)
verdi -fsdb wave.fsdb -ssf -ssy -ssv -o wave.vcd
# Or use WaveUtils
fsdb2vcd wave.fsdb wave.vcd  # 3X faster conversion
```

---

## VCS (Synopsys VCS) Debug Information

### Compilation Flags

**Debug visibility control:**
```bash
# Full debug (slowest, maximum visibility)
vcs -debug_all design.v testbench.v

# Optimized debug (recommended)
vcs -debug_access+all design.v testbench.v

# Minimal debug (just line info)
vcs -debug_access+r design.v testbench.v

# No debug (fastest simulation)
vcs design.v testbench.v
```

**`-debug_access` levels:**
- `+r` - Read access (view signal values)
- `+w` - Write access (force signals)
- `+f` - Functions/tasks
- `+cbk` - Callback access
- `+all` - Everything

**Trade-off:** More debug = slower simulation + larger memory

### Integration with Verdi


**DVT (Design and Verification Tools)** - Eclipse/VS Code plugin

**Features:**
- **Language support:** Verilog, SystemVerilog, VHDL, e Language
- **Debugger integration:** Works with major simulators
- **Interactive debugging:**
  - Set breakpoints in source code
  - Step through simulation
  - Inspect variables
  - Call stack view
  - Watch expressions

**How it works:**
1. DVT loads a debugger library into simulator
2. Simulator communicates with IDE via socket/IPC
3. IDE shows source code with current execution point
4. User can control simulation from IDE

**Simulator support:**
- VCS (Synopsys)
- Xcelium (Cadence)
- ModelSim/Questa (Siemens)
- Riviera-PRO (Aldec)
- Verilator (open-source)

**Example workflow:**
```systemverilog
// In source file
module my_module(input clk, input [7:0] data);
  always @(posedge clk) begin
    // Set breakpoint here in IDE
    if (data > 8'h80) begin
      $display("High value: %h", data);
    end
  end
endmodule
```

**Benefits:**
- No context switching (code + debug in one place)
- Faster iteration
- Better understanding (see code while debugging)

---

## Debug Information Hierarchy

### Module Hierarchy

**Preserved in waveform dumps:**
```
testbench
├── dut
│   ├── cpu
│   │   ├── alu
│   │   ├── registers
│   │   └── control
│   ├── memory
│   └── io
└── monitor
```

**VCD representation:**
```vcd
$scope module testbench $end
  $scope module dut $end
    $scope module cpu $end
      $scope module alu $end
        $var wire 32 A result [31:0] $end
      $upscope $end
    $upscope $end
  $upscope $end
$upscope $end
```

**FSDB:** Preserves same hierarchy, allows fast navigation

**Why it matters:**
- Signal names are only unique within scope
- Debugging requires understanding structure
- Cross-probing uses hierarchy paths
- Performance analysis (which module is active?)

### Signal Naming

**Full hierarchical path:**
```
testbench.dut.cpu.alu.result[31:0]
```

**Challenges:**
- **Escaped names:** SystemVerilog allows `\my-signal`
- **Generated names:** Synthesis creates `_T_123` temporaries
- **Arrays:** `memory[0]`, `memory[1]`, ...
- **Packed arrays:** `data[7:0]`
- **Structs:** `packet.header.src_addr`

**Verdi quirks (from GitHub issues):**
- Backslashes prepended: `\signal_name[6:0]`
- Module name must match VCD top module
- Parameterized modules expanded to multiple instances

---

## Implications for HWML

### 1. Dual Debug Strategy

**HWML elaboration (software):**
- Use standard DWARF (from previous research)
- Debug meta-level Scala/Rust-like code
- Source locations already tracked
- Variable inspection in elaborator

**Generated hardware (waveform):**
- Emit source locators in generated Verilog
- Use Chisel-style `@[file line:col]` comments
- Generate VCD/FSDB with hierarchy
- Map signals back to HWML source

### 2. Source Locator Strategy

**Follow Chisel's approach:**

```scala
// In HWML AST
trait HasSourceInfo {
  def sourceInfo: Option[SourceInfo]
}

case class SourceInfo(file: String, line: Int, col: Int) {
  def toComment: String = s"// @[$file $line:$col]"
  def toFIRRTL: String = s"@[$file $line:$col]"
}
```

**Emit in generated Verilog:**
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

**Benefits:**
- Standard waveform viewers show comments
- Debuggers can parse back to source
- No tool modifications required
- Works with existing flows

### 3. Waveform Generation

**HWML should:**

**Option A: Generate VCD dumps**
- Emit `$dumpfile()` / `$dumpvars()` in testbenches
- Portable, works everywhere
- Large files, slower

**Option B: Generate FSDB dumps (if targeting VCS)**
- Emit `$fsdbDumpfile()` / `$fsdbDumpvars()`
- Fast, compressed
- Requires Verdi license

**Option C: Both (best)**
- Default to VCD (open)
- Flag for FSDB when available
- Let user choose

**Example generated testbench:**
```verilog
initial begin
  `ifdef DUMP_FSDB
    $fsdbDumpfile("wave.fsdb");
    $fsdbDumpvars(0, testbench);
  `else
    $dumpfile("wave.vcd");
    $dumpvars(0, testbench);
  `endif
end
```

### 4. Hierarchy Preservation

**HWML module structure must map to Verilog modules.**

```hwml
module Counter {
  reg count : UInt<8>

  submodule alu = ALU {
    // ...
  }
}
```

**Generated Verilog:**
```verilog
module Counter(...);
  reg [7:0] count;

  ALU alu(
    // connections
  );
endmodule
```

**Waveform shows:**
```
Counter
├── count[7:0]
└── alu
    └── (ALU internals)
```

**Critical:** Don't flatten hierarchy in code generation (unless user requests it)

### 5. Signal Naming Convention

**Preserve HWML names in Verilog:**

```hwml
def mySignal : Bit = ...
let tempValue = a + b
```

**Generated:**
```verilog
wire mySignal;  // Good - preserved
wire tempValue; // Good - preserved
wire _T_42;     // Bad - generated, no source mapping
```

**Avoid:**
- Anonymous temporaries
- Mangled names (unless necessary for keywords)
- Lost source identity

**Use:**
- Sanitize for Verilog keywords (`begin` → `_begin`)
- Append suffix for disambiguation (`count_0`, `count_1`)
- But keep core name recognizable

### 6. Interactive Debug Integration

**Future possibility: HWML → DVT integration**

1. **Generate DVT project files**
2. **Emit debug metadata** DVT can consume
3. **Source mapping** from HWML → Verilog
4. **Breakpoints in HWML** map to Verilog lines
5. **Variable inspection** shows HWML names

**Challenges:**
- DVT expects Verilog/SV source
- Need bidirectional mapping
- Elaboration vs simulation time

**Near-term:** Focus on waveform + source locators (simpler, works now)

---

## Comparison: Software vs Hardware Debug

| Aspect | Software (DWARF) | Hardware (VCD/FSDB) |
|--------|------------------|---------------------|
| **Time Model** | Sequential execution | Clock cycles, parallel events |
| **State** | Call stack, registers | Signal values over time |
| **Format** | Binary debug sections | Text/indexed waveforms |
| **Viewer** | GDB, LLDB | Verdi, GTKWave, ModelSim |
| **Breakpoints** | Address-based | Time-based or condition-based |
| **Stepping** | Instruction/line | Clock cycle |
| **Type Info** | Full type system | Bit widths only |
| **Hierarchy** | Call stack | Module instance tree |
| **Location** | Instruction pointer | Current simulation time |

**Key insight:** Hardware debugging is **post-mortem analysis** of recorded waveforms, not interactive stepping through live execution (in most flows).

---

## Recommendations for HWML

### Phase 1: Basic Source Mapping (Immediate)

1. **Attach SourceInfo to all AST nodes**
   - Already designed in `location-information-design.md`
   - Complete Line:Column implementation

2. **Emit source locators in Verilog**
   - Chisel-style `@[file line:col]` comments
   - On every signal declaration
   - On every assignment
   - On every module instantiation

3. **Generate VCD dumps in testbenches**
   - Auto-emit `$dumpfile` / `$dumpvars`
   - Preserve module hierarchy
   - Preserve signal names

### Phase 2: Enhanced Debug Info (6 months)

4. **Bidirectional source mapping**
   - Tool to parse Verilog comments
   - Map waveform signals → HWML source
   - Interactive query: "where is this signal defined?"

5. **Waveform annotation**
   - Generate `.svcf` (Save file) for Verdi
   - Pre-mark interesting signals
   - Set up useful views

6. **FSDB support**
   - Conditional compilation for FSDB
   - Performance benefits for large designs

### Phase 3: Advanced Integration (Future)

7. **IDE integration**
   - LSP extension: "show in waveform"
   - Click signal in code → jump to waveform time
   - Click waveform → jump to source

8. **Synthesis debug support**
   - Preserve annotations through synthesis
   - Track signal transformations
   - Map optimized netlist back to source

9. **Custom debug metadata**
   - HWML-specific annotations
   - Dependent type information
   - Stage tracking (meta vs object level)

---

## References

### Tools & Documentation
- **Synopsys VCS User Guide** V-2023.12
- **Verdi Documentation** - Synopsys
- **DVT Eclipse Plugin** - AMIQ EDA
- **Chisel Source Locators** - https://www.chisel-lang.org/docs/explanations/source-locators

### Standards
- **VCD Format** - IEEE 1364 (Verilog standard)
- **SystemVerilog** - IEEE 1800

### Research Papers
- **SynAlign** - "Automatic Mapping of Post-Optimized Netlists to Source Code" (2025)

### Related HWML Docs
- `wiki/research/debug-info-systems.md` - Software debug info (DWARF, LLVM)
- `design/to-ingest/debug-info-research.md` - Original DWARF research
- `design/to-ingest/location-information-design.md` - Location architecture

---

## See Also

- [[research/debug-info-systems]] - Software debug information (DWARF, LLVM, etc.)
- [[decisions/ADR-001-lcf-kernel]] - Kernel architecture (error handling)
- [[entities/nbe]] - NbE (stepping through evaluation)

---

**Status:** Research complete. Ready for implementation planning and ADR creation.
