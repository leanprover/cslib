# Research Report: CI Prep -- Sorry Fix and Global CI Baseline

**Task**: 58 -- ci_prep_sorry_fix_baseline
**Session**: sess_1749512949_a3b2c1
**Date**: 2026-06-09

## 1. The `t_le_refl` Sorry in Chronicle/Frame.lean

**Location**: `Cslib/Logics/Temporal/Metalogic/Chronicle/Frame.lean`, line 104-105

```lean
/-! ## Reflexivity (sorry'd -- same issue as bimodal) -/

theorem t_le_refl (w : TPoint Atom) : t_le w w := by
  sorry
```

**Analysis**:
- `t_le_refl` is **not used anywhere** in the codebase. A project-wide grep for `t_le_refl` returns only the definition itself at line 104.
- The section comment says "same issue as bimodal" -- the bimodal counterpart `bx_le_refl` at `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Frame.lean:154` also uses sorry and is also unused.
- **Recommendation**: Delete the theorem entirely (lines 102-105), including the section comment `/-! ## Reflexivity (sorry'd -- same issue as bimodal) -/`. Since it is unused, removal is safe and eliminates the only sorry in the PR scope.

## 2. Sorry Occurrences in PR Scope (Temporal/Modal/Foundations)

**Result**: Only 1 sorry in PR scope.

| File | Line | Details |
|------|------|---------|
| `Cslib/Logics/Temporal/Metalogic/Chronicle/Frame.lean` | 105 | `t_le_refl` -- unused, safe to delete |

**Modal**: Zero sorry instances.
**Foundations**: Zero sorry instances.

**Note**: The Bimodal directory (not in the immediate PR scope for Temporal/Modal/Foundations) contains ~20+ sorries across multiple files. These are not blockers for this task.

## 3. CI Tools Availability

| Tool | Available | Notes |
|------|-----------|-------|
| `lake build` | Yes | Standard build |
| `lake shake` | Yes | Import minimization tool |
| `lake lint` | Yes | Uses `batteries/runLinter` as lint driver |
| `lake exe lint-style` | Yes | Style checker from Mathlib scripts |
| `lake exe checkInitImports` | Yes | Custom script in `scripts/CheckInitImports.lean` |

### Current CI Tool Results

**`lake exe lint-style`**: 10 errors (all trailing whitespace):

| File | Line(s) | Issue |
|------|---------|-------|
| `Bimodal/.../ChronicleConstruction.lean` | 314 | Trailing whitespace |
| `Bimodal/.../CounterexampleElimination.lean` | 2078, 2317, 2606, 2831 | Trailing whitespace |
| `Temporal/.../ChronicleConstruction.lean` | 313 | Trailing whitespace |
| `Temporal/.../CounterexampleElimination.lean` | 1821, 2060, 2349, 2574 | Trailing whitespace |

Fix: `lake exe lint-style --fix` should handle all automatically. 4 of the 10 are in the Temporal PR scope.

**`lake exe checkInitImports`**: Failed with "object file `.lake/build/lib/lean/Cslib.olean` does not exist". Needs a full `lake build` first, then re-run.

**`lake exe lint-style` nolints**: Warning about missing `scripts/nolints-style.txt`. The file does not exist but `scripts/nolints.json` does. An empty `nolints-style.txt` should be created to suppress the warning.

## 4. Author Name Corrections

**Problem**: 166 `.lean` files use "Benjamin Brastmckie" instead of "Benjamin Brast-McKie" in copyright headers.

**Distribution**:
- PR scope (Temporal/Modal/Foundations): **54 files**
- Bimodal: **111 files**
- Other (Propositional/Embedding.lean): **1 file**

**Correct files**: 12 files already use "Benjamin Brast-McKie" (all in `Bimodal/Metalogic/Separation/` subdirectories).

**Header format** (correct):
```
/-
Copyright (c) 2025 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/
```

**Fix approach**: A simple `sed` replacement across all `.lean` files:
```bash
find Cslib/ -name "*.lean" -exec sed -i 's/Benjamin Brastmckie/Benjamin Brast-McKie/g' {} +
```

This will fix both the `Copyright` line and the `Authors` line in each file. The replacement is safe because "Benjamin Brastmckie" appears only in header comments, never in code.

**Note**: Some files use copyright year 2026, others 2025. This is not flagged as an issue since both are valid.

## 5. Additional CI-Relevant Issues

### 5a. Missing `nolints-style.txt`
- `lake exe lint-style` warns: "nolints file could not be read; treating as empty: scripts/nolints-style.txt"
- Create an empty file at `scripts/nolints-style.txt` to suppress the warning.

### 5b. Debug artifacts
- `#check` instances in `Cslib/Foundations/Data/HasFresh.lean` are inside a doc comment block, not actual code. No action needed.
- No `#eval` or `dbg_trace` found in PR scope.

### 5c. All PR-scope files have Apache headers
- Every `.lean` file in Temporal/, Modal/, and Foundations/ begins with `/-` (header block present).

### 5d. `lake build` requirement
- `lake exe checkInitImports` requires a successful `lake build` first (it needs `.olean` files).
- A full `lake build` should be run as the first step, then all other CI checks.

### 5e. `lake shake` consideration
- `lake shake` minimizes imports. It should be run but may produce many suggestions.
- This can be done after the sorry fix and name corrections, as part of the CI baseline verification.

## 6. Recommended Implementation Order

1. **Delete `t_le_refl`** from `Cslib/Logics/Temporal/Metalogic/Chronicle/Frame.lean` (lines 102-105)
2. **Fix author name** across all 166 files: `sed -i 's/Benjamin Brastmckie/Benjamin Brast-McKie/g'`
3. **Fix trailing whitespace**: `lake exe lint-style --fix`
4. **Create `scripts/nolints-style.txt`**: empty file
5. **Run `lake build`**: verify zero errors
6. **Run `lake exe checkInitImports`**: verify zero violations
7. **Run `lake lint`**: verify zero errors
8. **Run `lake shake`**: review and fix unused imports (may be many; prioritize PR-scope files)
9. **Verify**: `grep -rn sorry` in Temporal/Modal/Foundations shows zero results

## 7. Risk Assessment

- **Low risk**: Deleting unused `t_le_refl` -- no downstream dependencies.
- **Low risk**: Name correction via sed -- only affects comment headers.
- **Low risk**: Trailing whitespace fix -- no semantic changes.
- **Medium risk**: `lake shake` may suggest removing imports that are transitively needed. Each removal should be verified with `lake build`.
- **Potential blocker**: If `lake build` reveals errors unrelated to this task, those must be triaged first.
