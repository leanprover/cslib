#!/usr/bin/env bash
# validate-pr-ci.sh — Run all CI checks for a cslib PR submission
#
# Usage: ./validate-pr-ci.sh [PATHS...]
#   PATHS: one or more file/directory paths to check for sorry and headers
#          defaults to checking Cslib/ directory
#
# Run from the cslib repo root: ~/Projects/cslib/
# This script mimics the 8 CI checks required before PR submission to leanprover/cslib.

set -euo pipefail

CSLIB_ROOT="${CSLIB_ROOT:-$(git rev-parse --show-toplevel 2>/dev/null || echo "$HOME/Projects/cslib")}"
TARGET_PATHS=("${@:-Cslib/}")
PASS=0
FAIL=0
WARNINGS=0

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

pass() { echo -e "${GREEN}PASS${NC}: $1"; ((PASS++)); }
fail() { echo -e "${RED}FAIL${NC}: $1"; ((FAIL++)); }
warn() { echo -e "${YELLOW}WARN${NC}: $1"; ((WARNINGS++)); }
header() { echo; echo "=== $1 ==="; }

cd "$CSLIB_ROOT"

echo "CSLib PR CI Validation"
echo "Working directory: $CSLIB_ROOT"
echo "Target paths: ${TARGET_PATHS[*]}"
echo "$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
echo "-------------------------------------------"

# 1. Build check
header "1. lake build"
if lake build 2>&1; then
    pass "lake build completed with zero errors"
else
    fail "lake build failed — fix errors before submitting PR"
fi

# 2. Test suite
header "2. lake test"
if lake test 2>&1; then
    pass "CslibTests suite passed"
else
    fail "lake test failed — investigate test failures"
fi

# 3. Init imports check
header "3. lake exe checkInitImports"
if lake exe checkInitImports 2>&1; then
    pass "All files import Cslib.Init"
else
    fail "checkInitImports failed — ensure all new files have 'import Cslib.Init' as first import"
fi

# 4. Environment linters
header "4. lake lint"
if lake lint 2>&1; then
    pass "Environment linters passed"
else
    fail "lake lint failed — review linter output above"
fi

# 5. Text style linters
header "5. lake exe lint-style"
if lake exe lint-style 2>&1; then
    pass "Text style linters passed"
else
    echo "Attempting auto-fix with --fix..."
    if lake exe lint-style --fix 2>&1; then
        warn "lint-style issues auto-fixed — review changes and re-run validation"
    else
        fail "lake exe lint-style failed and --fix did not resolve all issues"
    fi
fi

# 6. Import shake
header "6. lake shake"
SHAKE_OUTPUT=$(lake shake --add-public --keep-implied --keep-prefix 2>&1 || true)
echo "$SHAKE_OUTPUT"
if echo "$SHAKE_OUTPUT" | grep -q "^error:"; then
    fail "lake shake reported errors — review output above"
elif echo "$SHAKE_OUTPUT" | grep -qE "(unused import|redundant import)"; then
    warn "lake shake suggests import changes — apply them or add '-- shake: keep' comments for tactic-required imports"
else
    pass "lake shake: imports are minimal"
fi

# 7. Sorry check
header "7. Sorry check"
SORRY_FOUND=false
for target in "${TARGET_PATHS[@]}"; do
    if [ -e "$target" ]; then
        SORRY_RESULTS=$(grep -rn "sorry" "$target" --include="*.lean" 2>/dev/null || true)
        if [ -n "$SORRY_RESULTS" ]; then
            SORRY_FOUND=true
            echo "$SORRY_RESULTS"
        fi
    fi
done

if $SORRY_FOUND; then
    warn "sorry found in submitted files — verify this is intentional (only allowed for PR 8 chronicle construction, pre-disclosed)"
    echo "  If unexpected: remove sorry before submitting PR"
    echo "  If PR 8 chronicle sorry: ensure PR description includes sorry disclosure section"
else
    pass "Zero sorry in submitted files"
fi

# 8. Copyright header check
header "8. Copyright header check"
HEADER_FAIL=false
for target in "${TARGET_PATHS[@]}"; do
    if [ -e "$target" ]; then
        while IFS= read -r -d '' lean_file; do
            # Check if file starts with the expected copyright comment
            if ! head -4 "$lean_file" | grep -q "Released under Apache 2.0"; then
                echo "Missing copyright header: $lean_file"
                HEADER_FAIL=true
            fi
        done < <(find "$target" -name "*.lean" -print0 2>/dev/null)
    fi
done

if $HEADER_FAIL; then
    fail "Some files are missing Apache 2.0 copyright headers"
    echo "  Required format:"
    echo "  /-"
    echo "  Copyright (c) 2026 Benjamin Brastmckie. All rights reserved."
    echo "  Released under Apache 2.0 license as described in the file LICENSE."
    echo "  Authors: Benjamin Brastmckie"
    echo "  -/"
else
    pass "All Lean files have Apache 2.0 copyright headers"
fi

# Summary
echo
echo "==========================================="
echo "CI Validation Summary"
echo "==========================================="
echo -e "  ${GREEN}PASS${NC}: $PASS"
echo -e "  ${YELLOW}WARN${NC}: $WARNINGS"
echo -e "  ${RED}FAIL${NC}: $FAIL"
echo

if [ $FAIL -gt 0 ]; then
    echo -e "${RED}NOT READY for PR submission — fix $FAIL failing check(s) above${NC}"
    exit 1
elif [ $WARNINGS -gt 0 ]; then
    echo -e "${YELLOW}Review $WARNINGS warning(s) above before submitting PR${NC}"
    exit 0
else
    echo -e "${GREEN}All CI checks passed — ready for PR submission${NC}"
    exit 0
fi
