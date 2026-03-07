# HWML

[![CI](https://github.com/youngar/hwml-rs/actions/workflows/ci.yml/badge.svg)](https://github.com/youngar/hwml-rs/actions/workflows/ci.yml)

HWML is an in-development hardware description language equipped with a powerful metaprogramming layer.

**[📖 Read the Documentation](https://youngar.github.io/hwml-rs/)**

```hwml
meta def option.map (f : ^a -> ^b) (x : ^(option a)) : ^(option b) :=
  [
    x match {
      | some v => f v
      | none   => none
    }
  ]
```

## Features

- **Powerful metaprogramming** - Stage hardware generation with dependent types
- **CIRCT backend** - Compile to Verilog via MLIR/CIRCT
- **Type-safe hardware** - Catch errors at compile time

## Quick Start

### Compile HardwareUniverse to Verilog

```bash
# Build with CIRCT support
cargo build --features circt

# Compile a simple XOR circuit
cargo run --features circt -- --core -f examples/xor.hwml --emit-verilog
```

**Input** (`examples/xor.hwml`):
```hwml
^[ Xor One Zero ]
```

**Output**:
```verilog
module Top(
  output out
);
  assign out = 1'b1 ^ 1'b0;
endmodule
```

## Documentation

- **[HWML Core IR Reference Manual](https://youngar.github.io/hwml-rs/)** - Type-checked documentation (also available [locally](./docs/book/index.html))
- [Development Notes](./docs/design/Development.md)
- [Design Documents](./docs/design/) - Implementation plans and technical notes
