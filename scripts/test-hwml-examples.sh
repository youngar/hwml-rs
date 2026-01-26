#!/usr/bin/env bash
# Test HWML examples through the CLI with CIRCT backend

set -e

echo "╔════════════════════════════════════════════════════════════╗"
echo "║  Testing HWML Examples with CIRCT Backend                 ║"
echo "╚════════════════════════════════════════════════════════════╝"
echo ""

# Check if we're in a Nix shell with the updated environment
if [[ "$CIRCT_SYS_PREFIX" != *"-dev" ]]; then
    echo "❌ Error: Not in updated Nix shell!"
    echo ""
    echo "Please run:"
    echo "  exit"
    echo "  nix develop"
    echo ""
    echo "Then run this script again."
    exit 1
fi

echo "✓ Environment looks good"
echo "  CIRCT_SYS_PREFIX=$CIRCT_SYS_PREFIX"
echo "  MLIR_SYS_PREFIX=$MLIR_SYS_PREFIX"
echo "  LLVM_SYS_PREFIX=$LLVM_SYS_PREFIX"
echo ""

# Build the CLI with CIRCT support
echo "Building HWML CLI with CIRCT support..."
echo ""
if ! cargo build -p hwml --features circt; then
    echo ""
    echo "❌ Build failed!"
    echo ""
    echo "If you see 'circt-c/Dialect/Comb.h' not found, you need to:"
    echo "  1. Exit this shell: exit"
    echo "  2. Re-enter: nix develop"
    echo "  3. Run this script again"
    exit 1
fi

echo ""
echo "✓ Build successful!"
echo ""

# Test each example
EXAMPLES=(
    "examples/zero.hwml"
    "examples/one.hwml"
    "examples/xor.hwml"
    "examples/and.hwml"
)

for example in "${EXAMPLES[@]}"; do
    if [ ! -f "$example" ]; then
        echo "⚠️  Skipping $example (not found)"
        continue
    fi
    
    echo "╔════════════════════════════════════════════════════════════╗"
    echo "║  Testing: $example"
    echo "╚════════════════════════════════════════════════════════════╝"
    echo ""
    
    echo "File contents:"
    cat "$example"
    echo ""
    
    echo "─────────────────────────────────────────────────────────────"
    echo "Running: cargo run -p hwml --features circt -- --core -f $example"
    echo "─────────────────────────────────────────────────────────────"
    echo ""
    
    cargo run -p hwml --features circt -- --core -f "$example"
    
    echo ""
    echo "─────────────────────────────────────────────────────────────"
    echo "Running with MLIR output:"
    echo "─────────────────────────────────────────────────────────────"
    echo ""
    
    cargo run -p hwml --features circt -- --core -f "$example" --emit-mlir
    
    echo ""
    echo "─────────────────────────────────────────────────────────────"
    echo "Running with Verilog output:"
    echo "─────────────────────────────────────────────────────────────"
    echo ""
    
    cargo run -p hwml --features circt -- --core -f "$example" --emit-verilog
    
    echo ""
    echo "✓ $example completed successfully!"
    echo ""
    echo ""
done

echo "╔════════════════════════════════════════════════════════════╗"
echo "║  ✓ All examples tested successfully!                       ║"
echo "╚════════════════════════════════════════════════════════════╝"

