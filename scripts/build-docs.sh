#!/usr/bin/env bash
# Build the HWML documentation with validation
#
# This script:
# 1. Builds the mdbook-hwml preprocessor
# 2. Runs mdbook build (which automatically uses the preprocessor)
# 3. Reports any validation errors

set -e

echo "🔨 Building mdbook-hwml preprocessor..."
cargo build -p mdbook-hwml --release

echo ""
echo "📚 Building documentation with validation..."
mdbook build docs

echo ""
echo "✅ Documentation built successfully!"
echo "📖 Open docs/book/index.html to view"

