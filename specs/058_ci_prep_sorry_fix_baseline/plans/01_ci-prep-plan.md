# Implementation Plan: CI Prep -- Sorry Fix and Global CI Baseline

- **Task**: 58 - ci_prep_sorry_fix_baseline
- **Status**: [NOT STARTED]
- **Effort**: 2 hours
- **Dependencies**: None
- **Research Inputs**: specs/058_ci_prep_sorry_fix_baseline/reports/01_ci-prep-research.md
- **Artifacts**: plans/01_ci-prep-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

This task establishes a clean CI baseline for the cslib repository before any PR branches are created. The work involves: removing the single unused sorry (`t_le_refl`) from the PR scope, correcting the author name across 166 files, fixing trailing whitespace errors, creating a missing nolints file, and running the full CI tool suite to verify zero issues. The research report confirmed all changes are low-risk with no downstream dependencies.

### Research Integration

Key findings from the research report (01_ci-prep-research.md):
- **1 sorry in PR scope**: `t_le_refl` in `Chronicle/Frame.lean:104-105`, unused anywhere -- safe to delete entirely (lines 102-105 including section comment).
- **166 files need name correction**: "Benjamin Brastmckie" to "Benjamin Brast-McKie" in copyright headers. Single `sed` command handles all.
- **10 lint-style errors**: All trailing whitespace. `lake exe lint-style --fix` handles all automatically.
- **Missing `scripts/nolints-style.txt`**: Create empty file to suppress lint-style warning.
- **All CI tools available**: `lake build`, `lake shake`, `lake lint`, `lake exe lint-style`, `lake exe checkInitImports`.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task gates the PR submission pipeline (tasks 59-64). It advances the overall "Porting BimodalLogic to CSLib" roadmap by establishing CI compliance across all modules before the first PR is submitted.

## Goals & Non-Goals

**Goals**:
- Remove the only sorry in PR scope (Temporal/Modal/Foundations)
- Fix author name "Benjamin Brastmckie" to "Benjamin Brast-McKie" across all 166 affected files
- Fix all lint-style trailing whitespace errors
- Pass full CI suite: `lake build`, `lake shake`, `lake lint`, `lake exe lint-style`, `lake exe checkInitImports`
- Verify zero sorries in PR-scope directories (Temporal, Modal, Foundations)
- Verify Apache 2.0 headers on all PR-scope files

**Non-Goals**:
- Fixing sorries in the Bimodal directory (out of PR scope, ~20+ exist)
- Running `lake shake` fixes across entire codebase (only fix PR-scope files if issues found)
- Addressing `#check` in doc comments (not actual code, per research)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `lake build` reveals unrelated errors | H | L | Triage and fix only blockers; log others |
| `lake shake` suggests many import removals | M | M | Prioritize PR-scope files; verify each removal with build |
| `sed` replacement hits unexpected content | L | L | "Benjamin Brastmckie" only appears in headers per research |
| `lake exe checkInitImports` fails | M | L | Requires successful `lake build` first; run in correct order |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 4 | 4 | 3 |

Phases within the same wave can execute in parallel.

### Phase 1: Remove Sorry and Fix Source Files [COMPLETED]

**Goal**: Eliminate the single sorry in PR scope and apply all source-level fixes (name correction, trailing whitespace, missing nolints file).

**Tasks**:
- [ ] Delete lines 102-105 from `Cslib/Logics/Temporal/Metalogic/Chronicle/Frame.lean` (section comment + `t_le_refl` theorem with sorry)
- [ ] Run `find Cslib/ -name "*.lean" -exec sed -i 's/Benjamin Brastmckie/Benjamin Brast-McKie/g' {} +` to fix author names across all 166 files
- [ ] Verify name correction: `grep -rn "Benjamin Brastmckie" Cslib/` should return zero results
- [ ] Verify correct name: `grep -rn "Benjamin Brast-McKie" Cslib/` should return 166+ results
- [ ] Create empty `scripts/nolints-style.txt` to suppress lint-style warning
- [ ] Run `lake exe lint-style --fix` to fix all 10 trailing whitespace errors
- [ ] Verify: `lake exe lint-style` reports zero errors

**Timing**: 20 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/Chronicle/Frame.lean` - delete unused sorry theorem
- `Cslib/**/*.lean` (166 files) - author name correction in copyright headers
- `scripts/nolints-style.txt` - create empty file
- Various `.lean` files (10) - trailing whitespace removal via lint-style --fix

**Verification**:
- `grep -rn sorry Cslib/Logics/Temporal/ Cslib/Logics/Modal/ Cslib/Foundations/` returns zero results
- `grep -rn "Benjamin Brastmckie" Cslib/` returns zero results
- `lake exe lint-style` returns zero errors

---

### Phase 2: Build Verification [NOT STARTED]

**Goal**: Verify the project builds cleanly after all source changes.

**Tasks**:
- [ ] Run `lake build` and verify zero errors
- [ ] If build errors occur, diagnose and fix (likely unrelated to our changes since sorry deletion and header changes are safe)

**Timing**: 30 minutes (build time)

**Depends on**: 1

**Files to modify**:
- None expected (build verification only)

**Verification**:
- `lake build` exits with code 0 and zero error output

---

### Phase 3: CI Tool Suite [NOT STARTED]

**Goal**: Run all remaining CI tools and fix any issues found.

**Tasks**:
- [ ] Run `lake exe checkInitImports` and verify zero violations
- [ ] Run `lake lint` and verify zero errors
- [ ] Run `lake shake` on PR-scope files and review suggestions
- [ ] Fix any unused imports identified by `lake shake` in PR-scope directories (Temporal, Modal, Foundations)
- [ ] Re-run `lake build` if any import changes were made to verify nothing breaks

**Timing**: 40 minutes

**Depends on**: 2

**Files to modify**:
- PR-scope `.lean` files if `lake shake` identifies unused imports

**Verification**:
- `lake exe checkInitImports` exits cleanly
- `lake lint` reports zero errors
- `lake shake` shows no actionable issues in PR-scope files
- `lake build` still passes after any import changes

---

### Phase 4: Final Validation [NOT STARTED]

**Goal**: Run comprehensive final checks to confirm the clean CI baseline.

**Tasks**:
- [ ] Verify zero sorries in PR scope: `grep -rn sorry Cslib/Logics/Temporal/ Cslib/Logics/Modal/ Cslib/Foundations/`
- [ ] Verify all PR-scope files have Apache 2.0 headers: check that every `.lean` file in Temporal/, Modal/, Foundations/ begins with the copyright block
- [ ] Verify correct author name in all files: `grep -rn "Benjamin Brastmckie" Cslib/` returns nothing
- [ ] Run full CI suite one final time: `lake build`, `lake exe lint-style`, `lake lint`, `lake exe checkInitImports`
- [ ] Document any remaining issues (e.g., Bimodal sorries, out-of-scope lint warnings) in the implementation summary

**Timing**: 30 minutes

**Depends on**: 3

**Files to modify**:
- None expected (validation only)

**Verification**:
- All CI tools pass with zero errors
- Zero sorries in PR-scope directories
- All PR-scope files have correct Apache 2.0 headers with "Benjamin Brast-McKie"

## Testing & Validation

- [ ] `lake build` produces zero errors
- [ ] `grep -rn sorry Cslib/Logics/Temporal/ Cslib/Logics/Modal/ Cslib/Foundations/` returns empty
- [ ] `grep -rn "Benjamin Brastmckie" Cslib/` returns empty
- [ ] `lake exe lint-style` reports zero errors
- [ ] `lake lint` reports zero errors
- [ ] `lake exe checkInitImports` reports zero violations
- [ ] `lake shake` shows no actionable issues in PR-scope files
- [ ] All PR-scope `.lean` files have Apache 2.0 headers

## Artifacts & Outputs

- `plans/01_ci-prep-plan.md` (this file)
- `summaries/01_ci-prep-summary.md` (to be created after implementation)

## Rollback/Contingency

All changes are reversible via git:
- Sorry deletion: `git checkout -- Cslib/Logics/Temporal/Metalogic/Chronicle/Frame.lean`
- Name corrections: `find Cslib/ -name "*.lean" -exec sed -i 's/Benjamin Brast-McKie/Benjamin Brastmckie/g' {} +`
- Lint-style fixes: `git checkout -- <affected files>`
- Nolints file: `rm scripts/nolints-style.txt`
- Import changes: `git checkout -- <affected files>`

In the unlikely event that changes cause cascading build failures, `git stash` or `git checkout .` will restore the original state completely.
