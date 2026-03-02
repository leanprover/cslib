#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Usage:
  ./scripts/boole-smt.sh <file.lean> [lean_args...]

Runs `lake env lean` with:
  - `cvc5` added to PATH (from `.lake/packages/cvc5/.../bin` if available)
  - `--load-dynlib` pointing at the built cvc5 Lean bindings (if available)

This is useful for Boole/Strata examples that use:
  - `#eval Strata.Boole.verify "cvc5" ...` (needs `cvc5` on PATH)
  - `import Smt` / `smt` tactic (needs `--load-dynlib`)
EOF
}

if [[ $# -lt 1 ]] || [[ "${1:-}" == "-h" ]] || [[ "${1:-}" == "--help" ]]; then
  usage
  exit 2
fi

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
FILE="$1"
shift

if [[ ! -e "$FILE" ]]; then
  echo "error: file not found: $FILE" >&2
  exit 2
fi

DYNLIB_DIR="$ROOT/.lake/packages/cvc5/.lake/build/lib"
DYNLIB=""
if [[ -d "$DYNLIB_DIR" ]]; then
  DYNLIB="$(ls -1 "$DYNLIB_DIR"/libcvc5_cvc5.* 2>/dev/null | head -n 1 || true)"
fi

LOAD_DYNLIB_ARGS=()
if [[ -n "$DYNLIB" ]]; then
  LOAD_DYNLIB_ARGS=(--load-dynlib="$DYNLIB")
else
  echo "warning: could not find cvc5 dynlib under $DYNLIB_DIR" >&2
  echo "warning: files that use `import Smt` / the `smt` tactic may fail." >&2
  echo "hint: run \`lake build Smt\` (or \`lake build\`) to build it." >&2
fi

CVC5_BIN_DIR=""
while IFS= read -r -d '' cand; do
  CVC5_BIN_DIR="$(dirname "$cand")"
  break
done < <(find "$ROOT/.lake/packages/cvc5" -maxdepth 4 -type f -name cvc5 -path '*/bin/cvc5' -print0 2>/dev/null || true)

if [[ -n "$CVC5_BIN_DIR" ]]; then
  export PATH="$CVC5_BIN_DIR:$PATH"
else
  echo "warning: could not find a `cvc5` binary under $ROOT/.lake/packages/cvc5" >&2
  echo "warning: `#eval Strata.Boole.verify \"cvc5\" ...` may fail unless `cvc5` is on PATH." >&2
fi

exec lake env lean "${LOAD_DYNLIB_ARGS[@]}" "$FILE" "$@"
