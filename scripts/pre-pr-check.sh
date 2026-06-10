#!/usr/bin/env bash
set -e
echo "=== Pre-PR Verification ==="

echo "1. Checking for sorry instances in PR scope..."
if grep -rn 'sorry' Cslib/Foundations/Logic/ Cslib/Logics/Modal/ Cslib/Logics/Temporal/ --include="*.lean" 2>/dev/null; then
  echo "  WARNING: sorry instances found"
else
  echo "  OK: No sorry instances"
fi

echo "2. Checking for debug artifacts..."
if grep -rn '#check\|#eval\|dbg_trace' Cslib/Foundations/Logic/ Cslib/Logics/Modal/ Cslib/Logics/Temporal/ --include="*.lean" 2>/dev/null; then
  echo "  WARNING: debug artifacts found"
else
  echo "  OK: No debug artifacts"
fi

echo "3. Checking for missing copyright headers..."
for f in $(find Cslib/Foundations/Logic/ Cslib/Logics/Modal/ Cslib/Logics/Temporal/ -name "*.lean"); do
  if ! head -1 "$f" | grep -q "^/-"; then
    echo "  WARNING: Missing header in $f"
  fi
done

echo "4. Building PR-scope modules..."
lake build Cslib.Foundations.Logic.Metalogic.Consistency
lake build Cslib.Logics.Modal.Metalogic
lake build Cslib.Logics.Temporal.Metalogic

echo "=== Pre-PR Verification Complete ==="
