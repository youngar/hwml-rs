# HWML CIRCT Examples

This directory contains examples demonstrating the HWML CIRCT backend.

## Examples

### `minimal_hsyntax.rs` - Minimal Syntax Translation

**Status**: ✅ Implemented

This example demonstrates the minimal working translation from HWML's hardware-level syntax (`Syntax`) to CIRCT IR.

**What it does**:
- Creates a simple hardware expression: `Xor One Zero`
- Translates it to a CIRCT HW module named "Top"
- Generates MLIR IR with:
  - `hw.constant` operations for `0` and `1`
  - `comb.xor` operation for XOR
  - `hw.output` operation for the result
  - `hw.module` wrapper

**Run it**:
```bash
cargo run --example minimal_hsyntax -p hwml_circt
```

**Expected output**:
```
╔════════════════════════════════════════════════════════════╗
║    HWML CIRCT: Minimal Syntax Translation Example        ║
╚════════════════════════════════════════════════════════════╝

Step 1: Creating CIRCT context...
✓ Context created

Step 2: Creating Syntax expression...
  Expression: (Xor One Zero)
  Expected result: 1 XOR 0 = 1

Step 3: Translating to CIRCT...
✓ Translation successful

Step 4: Verifying MLIR module...
✓ Module is valid

╔════════════════════════════════════════════════════════════╗
║    Generated MLIR IR                                       ║
╚════════════════════════════════════════════════════════════╝

hw.module @Top() -> (out: i1) {
  %c0 = hw.constant 0 : i1
  %c1 = hw.constant 1 : i1
  %0 = comb.xor %c1, %c0 : i1
  hw.output %0 : i1
}
```

**What's implemented**:
- ✅ Syntax expression creation (`Zero`, `One`, `Xor`)
- ✅ Translation to CIRCT operations
- ✅ MLIR module generation
- ✅ Module verification

**Next steps**:
- Add Verilog export
- Support more operations (AND, OR, NOT)
- Support multi-bit values
- Add module inputs

---

### `basic.rs` - Basic Backend Usage

**Status**: ✅ Compiles (Verilog export pending)

Demonstrates the high-level `CirctBackend` API for compiling HWML modules.

**What it does**:
- Creates an empty HWML module
- Initializes the CIRCT backend
- Compiles to MLIR IR (for inspection)
- Attempts Verilog export (currently returns placeholder error)

**Run it**:
```bash
cargo run --example basic -p hwml_circt
```

**What's implemented**:
- ✅ Backend initialization
- ✅ MLIR compilation
- ⚠️ Verilog export (placeholder - needs implementation)

---

### `adder.rs` - HardwareUniverse Type Creation

**Status**: ✅ Compiles

Demonstrates creating hardware types and planning module structure.

**What it does**:
- Creates a CIRCT context with registered dialects
- Defines various integer types (1-bit, 8-bit, 16-bit, 32-bit)
- Shows planned module signature for an 8-bit adder
- Displays expected Verilog output

**Run it**:
```bash
cargo run --example adder -p hwml_circt
```

**What's implemented**:
- ✅ CIRCT context creation
- ✅ Dialect registration (HW, Comb, Seq)
- ✅ Integer type creation
- 🚧 Module creation (in progress)
- 🚧 Operation builders (in progress)
- 🚧 Verilog export (in progress)

---

## Development Workflow

### Adding a New Example

1. Create a new file in `crates/hwml-circt/examples/`
2. Add it to `Cargo.toml` if needed (examples are auto-discovered)
3. Document it in this README

### Testing Examples

```bash
# Run all examples
cargo run --example basic -p hwml_circt
cargo run --example minimal_hsyntax -p hwml_circt
cargo run --example adder -p hwml_circt

# Run with CIRCT debugging
MLIR_ENABLE_DUMP=1 cargo run --example minimal_hsyntax -p hwml_circt
```

### Debugging

If an example fails:

1. **Check CIRCT installation**:
   ```bash
   which circt-opt
   circt-opt --version
   ```

2. **Print MLIR module**:
   ```rust
   println!("{}", mlir_module.to_string());
   ```

3. **Verify module**:
   ```rust
   if !mlir_module.verify() {
       eprintln!("Module verification failed!");
   }
   ```

## Recent Updates (2026-01-15)

All examples have been updated to use the new raw MLIR C API instead of the `melior` crate:

- **Removed dependency**: `melior` (was causing LLVM version conflicts)
- **New wrappers**: Using `MlirModuleWrapper`, `MlirContextWrapper`, etc. from `hwml_circt_sys`
- **API changes**:
  - `mlir_module.as_operation().verify()` → `mlir_module.verify()`
  - `println!("{}", mlir_module.as_operation())` → `println!("{}", mlir_module.to_string())`
  - `Location::unknown(ctx)` → `ctx.unknown_location()`

All examples now compile successfully! ✅

## Resources

- [CIRCT Documentation](https://circt.llvm.org/)
- [MLIR Documentation](https://mlir.llvm.org/)
- [HWML CIRCT Developer Guide](../../../doc/CIRCT_DEVELOPER_GUIDE.md)
- [CIRCT Quick Start](../../../doc/CIRCT_QUICKSTART.md)

