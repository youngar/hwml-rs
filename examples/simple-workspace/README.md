# Simple Workspace Example

This example demonstrates HWML's workspace aggregation system.

## Structure

```
simple-workspace/
├── hwml.toml           # Workspace manifest
└── src/
    ├── main.hwml       # Main module definitions
    └── util.hwml       # Utility definitions
```

## Running

### Workspace Mode (New!)

Load the entire workspace with all files automatically aggregated:

```bash
cargo run -- --workspace examples/simple-workspace/hwml.toml
```

Or with verbose output:

```bash
cargo run -- --workspace examples/simple-workspace/hwml.toml -v
```

### Single File Mode (Legacy)

Process just one file:

```bash
cargo run -- --file examples/simple-workspace/src/main.hwml
```

## What Happens

In **workspace mode**, the compiler:

1. Parses `hwml.toml` to find the library name and dependencies
2. Discovers all `.hwml` files in the workspace
3. Aggregates all declarations into a global symbol table
4. Separates concrete definitions (to be lowered to Verilog) from parametric ones (compile-time only)
5. Checks for collisions across all files

## Expected Output

```
Concrete Definitions (will be lowered to Verilog):
==================================================
  "Example.MyModule" (Constant)
  "Example.TopLevel" (Constant)
  "Example.Util.Helper" (Constant)

Workspace loaded successfully!
Ready for elaboration and Verilog emission.
```

## Key Points

- **No imports needed!** All files in the workspace are automatically visible to each other
- **Namespace organization:** `namespace Example { ... }` creates `Example.MyModule`
- **Concrete vs Parametric:** All these definitions are concrete (no meta-level parameters)
- **Ready for Verilog:** Each concrete definition will become a Verilog module
