#!/usr/bin/env bash
#
# ECHIDNA NPM Ban Enforcement Script
# This script checks for and blocks npm/node usage
#
# SPDX-License-Identifier: MIT OR AGPL-3.0-or-later

set -euo pipefail

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

echo "🔍 ECHIDNA NPM Ban Check"
echo "========================"

VIOLATIONS=0

# Check for package-lock.json
if [ -f "package-lock.json" ]; then
    echo -e "${RED}❌ VIOLATION: package-lock.json found in root${NC}"
    VIOLATIONS=$((VIOLATIONS + 1))
fi

# Check for node_modules anywhere
if find . -type d -name "node_modules" 2>/dev/null | grep -q .; then
    echo -e "${RED}❌ VIOLATION: node_modules directory found${NC}"
    find . -type d -name "node_modules" 2>/dev/null
    VIOLATIONS=$((VIOLATIONS + 1))
fi

# Check for npm/npx usage in scripts
if grep -r "npm install\|npm i \|npx \|npm run" scripts/ 2>/dev/null | grep -v "ban-npm"; then
    echo -e "${RED}❌ VIOLATION: npm/npx commands found in scripts${NC}"
    VIOLATIONS=$((VIOLATIONS + 1))
fi

# Check for npm imports in TypeScript (should use https:// or npm: specifier)
BAD_IMPORTS=$(grep -r "from ['\"][@a-z]" src/provers/ 2>/dev/null | grep -v "from ['\"]https://" | grep -v "from ['\"]npm:" | grep -v "from ['\"]\./" | grep -v "from ['\"]\.\./" || true)
if [ -n "$BAD_IMPORTS" ]; then
    echo -e "${YELLOW}⚠️  WARNING: Bare imports found (should use https:// or npm: specifier)${NC}"
    echo "$BAD_IMPORTS"
fi

# Check Justfile for npm commands
if [ -f "Justfile" ] && grep -q "npm\|npx" Justfile; then
    echo -e "${RED}❌ VIOLATION: npm/npx found in Justfile${NC}"
    VIOLATIONS=$((VIOLATIONS + 1))
fi

# Summary
echo ""
if [ $VIOLATIONS -eq 0 ]; then
    echo -e "${GREEN}✅ No npm violations found!${NC}"
    echo ""
    echo "Approved package managers:"
    echo "  ✓ Deno (deno.json, deno task)"
    echo "  ✓ Bun (only if Deno impossible)"
    echo ""
    echo "Banned:"
    echo "  ✗ npm, npx, node_modules"
    echo "  ✗ package-lock.json"
    exit 0
else
    echo -e "${RED}❌ Found $VIOLATIONS violation(s)!${NC}"
    echo ""
    echo "To fix:"
    echo "  1. Remove package-lock.json: rm package-lock.json"
    echo "  2. Remove node_modules: rm -rf node_modules"
    echo "  3. Use 'deno task' instead of 'npm run'"
    echo "  4. Use https:// or npm: imports in Deno"
    exit 1
fi
