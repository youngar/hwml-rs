#!/usr/bin/env bash
# Test script to verify the CIRCT build fix

set -e

echo "╔════════════════════════════════════════════════════════════╗"
echo "║  Testing CIRCT Build Fix                                   ║"
echo "╚════════════════════════════════════════════════════════════╝"
echo ""

# Check environment variables
echo "1. Checking environment variables..."
echo ""

if [ -z "$CIRCT_SYS_PREFIX" ]; then
    echo "❌ CIRCT_SYS_PREFIX is not set!"
    echo "   Please run: nix develop"
    exit 1
fi

echo "✓ CIRCT_SYS_PREFIX=$CIRCT_SYS_PREFIX"

if [ -z "$MLIR_SYS_PREFIX" ]; then
    echo "❌ MLIR_SYS_PREFIX is not set!"
    exit 1
fi

echo "✓ MLIR_SYS_PREFIX=$MLIR_SYS_PREFIX"

if [ -z "$LLVM_SYS_PREFIX" ]; then
    echo "❌ LLVM_SYS_PREFIX is not set!"
    exit 1
fi

echo "✓ LLVM_SYS_PREFIX=$LLVM_SYS_PREFIX"
echo ""

# Check that we're using dev outputs (not out)
echo "2. Verifying we're using dev outputs..."
echo ""

if [[ "$CIRCT_SYS_PREFIX" == *"-dev" ]]; then
    echo "✓ CIRCT_SYS_PREFIX points to dev output"
else
    echo "❌ CIRCT_SYS_PREFIX does not point to dev output!"
    echo "   Got: $CIRCT_SYS_PREFIX"
    exit 1
fi

if [[ "$MLIR_SYS_PREFIX" == *"-dev" ]]; then
    echo "✓ MLIR_SYS_PREFIX points to dev output"
else
    echo "❌ MLIR_SYS_PREFIX does not point to dev output!"
    exit 1
fi

if [[ "$LLVM_SYS_PREFIX" == *"-dev" ]]; then
    echo "✓ LLVM_SYS_PREFIX points to dev output"
else
    echo "❌ LLVM_SYS_PREFIX does not point to dev output!"
    exit 1
fi

echo ""

# Check that headers exist
echo "3. Checking that headers exist..."
echo ""

# CIRCT headers (note the nested include/include structure)
if [ -d "$CIRCT_SYS_PREFIX/include/include/circt-c" ]; then
    echo "✓ CIRCT headers found at: $CIRCT_SYS_PREFIX/include/include/circt-c/"
    echo "  Sample files:"
    ls "$CIRCT_SYS_PREFIX/include/include/circt-c/" | head -3 | sed 's/^/    /'
elif [ -d "$CIRCT_SYS_PREFIX/include/circt-c" ]; then
    echo "✓ CIRCT headers found at: $CIRCT_SYS_PREFIX/include/circt-c/"
    echo "  Sample files:"
    ls "$CIRCT_SYS_PREFIX/include/circt-c/" | head -3 | sed 's/^/    /'
else
    echo "❌ CIRCT headers not found!"
    echo "   Checked:"
    echo "     $CIRCT_SYS_PREFIX/include/include/circt-c/"
    echo "     $CIRCT_SYS_PREFIX/include/circt-c/"
    exit 1
fi

# MLIR headers
if [ -d "$MLIR_SYS_PREFIX/include/mlir-c" ]; then
    echo "✓ MLIR headers found at: $MLIR_SYS_PREFIX/include/mlir-c/"
    echo "  Sample files:"
    ls "$MLIR_SYS_PREFIX/include/mlir-c/" | head -3 | sed 's/^/    /'
else
    echo "❌ MLIR headers not found at: $MLIR_SYS_PREFIX/include/mlir-c/"
    exit 1
fi

# LLVM headers
if [ -d "$LLVM_SYS_PREFIX/include/llvm-c" ]; then
    echo "✓ LLVM headers found at: $LLVM_SYS_PREFIX/include/llvm-c/"
    echo "  Sample files:"
    ls "$LLVM_SYS_PREFIX/include/llvm-c/" | head -3 | sed 's/^/    /'
else
    echo "❌ LLVM headers not found at: $LLVM_SYS_PREFIX/include/llvm-c/"
    exit 1
fi

echo ""

# Try building
echo "4. Attempting to build hwml_circt_sys..."
echo ""

cargo clean -p hwml_circt_sys
if cargo build -p hwml_circt_sys 2>&1 | tee /tmp/circt-build.log; then
    echo ""
    echo "╔════════════════════════════════════════════════════════════╗"
    echo "║  ✓ SUCCESS! CIRCT build fix is working!                   ║"
    echo "╚════════════════════════════════════════════════════════════╝"
    exit 0
else
    echo ""
    echo "╔════════════════════════════════════════════════════════════╗"
    echo "║  ❌ Build failed. Check the output above for errors.       ║"
    echo "╚════════════════════════════════════════════════════════════╝"
    echo ""
    echo "Build log saved to: /tmp/circt-build.log"
    exit 1
fi

