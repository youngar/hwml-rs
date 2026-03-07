#!/bin/bash
# Validation script to simulate GitHub Actions workflow locally
# This helps catch issues before pushing to GitHub

set -e  # Exit on error

echo "=================================================="
echo "  CI Validation Script for HWML Documentation"
echo "=================================================="
echo ""

# Colors for output
GREEN='\033[0;32m'
RED='\033[0;31m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Step 1: Validate documentation snippets
echo -e "${YELLOW}Step 1: Validating documentation snippets...${NC}"
if cargo test -p mdbook-hwml --test validate_docs --quiet; then
    echo -e "${GREEN}✓ Documentation validation passed${NC}"
else
    echo -e "${RED}✗ Documentation validation failed${NC}"
    exit 1
fi
echo ""

# Step 2: Build the mdBook
echo -e "${YELLOW}Step 2: Building mdBook...${NC}"
if command -v mdbook &> /dev/null; then
    if mdbook build docs/; then
        echo -e "${GREEN}✓ mdBook build succeeded${NC}"
        echo -e "  Output: docs/book/"
    else
        echo -e "${RED}✗ mdBook build failed${NC}"
        exit 1
    fi
else
    echo -e "${YELLOW}⚠ mdbook not installed locally${NC}"
    echo -e "  Install with: cargo install mdbook"
    echo -e "  (This step will succeed in CI)"
fi
echo ""

# Step 3: Verify core compiler has no markdown dependencies
echo -e "${YELLOW}Step 3: Verifying dependency separation...${NC}"
if cargo tree -p hwml_core | grep -E "(pulldown-cmark|walkdir)" > /dev/null; then
    echo -e "${RED}✗ hwml_core still has markdown dependencies!${NC}"
    exit 1
else
    echo -e "${GREEN}✓ hwml_core has no markdown dependencies${NC}"
fi
echo ""

# Step 4: Verify mdbook-hwml has the right dependencies
echo -e "${YELLOW}Step 4: Verifying mdbook-hwml dependencies...${NC}"
if cargo tree -p mdbook-hwml | grep -E "pulldown-cmark" > /dev/null; then
    echo -e "${GREEN}✓ mdbook-hwml has pulldown-cmark${NC}"
else
    echo -e "${RED}✗ mdbook-hwml missing pulldown-cmark!${NC}"
    exit 1
fi
echo ""

# Summary
echo "=================================================="
echo -e "${GREEN}  All validation checks passed! ✓${NC}"
echo "=================================================="
echo ""
echo "Your changes are ready to push to GitHub."
echo "The GitHub Actions workflow should succeed."
echo ""

