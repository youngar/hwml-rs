# HWML CIRCT Backend

This crate provides a backend for compiling HWML to Verilog using [CIRCT](https://circt.llvm.org/) (Circuit IR Compilers and Tools).

## Architecture

The backend consists of two crates:

1. **`hwml_circt_sys`**: Low-level FFI bindings to the CIRCT C API
2. **`hwml_circt`**: Safe, high-level Rust API for compiling HWML to Verilog

## Installation

### Prerequisites

You need CIRCT installed on your system. Choose one of the following methods:

#### Option 1: Homebrew (Recommended for macOS/Linux)

```bash
brew install llvm circt
```

#### Option 2: Nix

```bash
nix develop
```

The Nix flake provides LLVM automatically. CIRCT support is coming soon.

#### Option 3: Manual Installation

Download and install CIRCT from [circt.llvm.org](https://circt.llvm.org/), then set:

```bash
export CIRCT_SYS_PREFIX=/path/to/circt
```

#### Option 4: Build from Source (30+ minutes)

```bash
# Initialize the CIRCT submodule
git submodule update --init external/circt

# Build with source compilation enabled
cargo build --features build-from-source
```

## Usage

```rust
use hwml_circt::CirctBackend;
use hwml_core::declaration::Module;

// Create a backend
let backend = CirctBackend::new()?;

// Compile HWML module to Verilog
let verilog = backend.compile_to_verilog(&module)?;
println!("{}", verilog);
```

## Development Status

This backend is currently in early development. The following features are implemented:

- [x] FFI bindings generation
- [x] MLIR context management
- [x] CIRCT dialect registration (HW, Comb, Seq)
- [ ] Complete HWML → CIRCT translation
- [ ] Verilog export
- [ ] Full test coverage

## Architecture Details

### Translation Pipeline

1. **Parse**: HWML source → HWML AST (handled by `hwml_core`)
2. **Translate**: HWML AST → CIRCT IR (this crate)
3. **Export**: CIRCT IR → Verilog (this crate)

### CIRCT Dialects Used

- **HW**: HardwareUniverse structural dialect (modules, ports, instances)
- **Comb**: Combinational logic operations
- **Seq**: Sequential logic (registers, clocks)

## Troubleshooting

### Build Errors

If you see "CIRCT not found" errors:

1. Verify CIRCT is installed: `which circt-opt`
2. Check LLVM version matches: `llvm-config --version` (should be 18+)
3. Set `CIRCT_SYS_PREFIX` if installed in non-standard location

### Version Compatibility

- LLVM: 18.x or later
- CIRCT: Latest from main branch
- Melior: 0.26 (LLVM 21 support)

## Contributing

See the main HWML repository for contribution guidelines.

## License

See the main HWML repository for license information.

