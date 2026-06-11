# Implementation Plan: PR 1.5 Propositional Hilbert Submission

- **Task**: 90 - PR 1.5 propositional Hilbert submission
- **Status**: [IN PROGRESS]
- **Effort**: 1.5 hours
- **Dependencies**: Tasks 86-89 (completed)
- **Research Inputs**: specs/090_pr_1_5_propositional_hilbert_submission/reports/01_pr-scope-review.md
- **Artifacts**: plans/01_pr-submission-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

PR 1.5 bundles all propositional/Hilbert proof system work from tasks 86-89 (lint cleanup, ND-Hilbert equivalence, intuitionistic base refactoring, derived connective rules) into a submission-ready pull request. The codebase is sorry-free and compiles cleanly. Three pre-submission fixes are needed: adding 3 missing root imports to `Cslib.lean`, removing an unused `DecidableEq` type class parameter in `FromHilbert.lean`, and verifying clean compilation. After fixes, a feature branch is created and the PR is submitted via `gh pr create`.

### Research Integration

Key findings from the scope review report:
- **3 new files** missing from `Cslib.lean`: `DerivedRules`, `Equivalence`, `HilbertDerivedRules`
- **1 unused warning**: `[DecidableEq Atom']` in `FromHilbert.lean:212` on `hilbertSubstitutionDeriv`
- **Zero sorries**, no debug artifacts, no modal leakage
- **16 total files** in PR scope (3 new + 13 modified) across `Foundations/Logic/` and `Logics/Propositional/`
- PR 1.5 must land before PR 2 due to the cross-cutting `PropositionalHilbert` -> `ClassicalHilbert` rename

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This plan advances the following roadmap items:
- Propositional Hilbert theorems (already listed under Completed)
- The 3-level hierarchy refactoring (MinimalHilbert -> IntuitionisticHilbert -> ClassicalHilbert) and ND-Hilbert equivalence are new contributions that extend the Completed items

## Goals & Non-Goals

**Goals**:
- Fix all must-fix and should-fix issues identified in research
- Verify clean `lake build` with zero warnings in propositional scope
- Create a feature branch containing only propositional/Foundations changes
- Submit PR 1.5 via GitHub CLI with a clear description of the 16-file changeset

**Non-Goals**:
- Modifying any modal, temporal, or bimodal files (those belong to PR 2+)
- Addressing the docstring TODO in `Basic.lean:219` (design note, not a defect)
- Rebasing or updating the existing PR 1 (#629)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Removing `DecidableEq` breaks downstream code | H | L | The parameter is unused per linter; `lake build` will catch any breakage |
| Feature branch diverges from main | M | L | Branch from current HEAD on main; submit immediately |
| PR scope includes unintended modal changes | H | L | Research confirmed zero modal leakage; verify with scoped grep |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3 | 1, 2 |
| 3 | 4 | 3 |

Phases within the same wave can execute in parallel.

### Phase 1: Add Missing Root Imports [IN PROGRESS]

**Goal**: Register the 3 new NaturalDeduction files in `Cslib.lean` so they are included in the library build.

**Tasks**:
- [ ] Add `public import Cslib.Logics.Propositional.NaturalDeduction.DerivedRules` after the `FromHilbert` import (line 295)
- [ ] Add `public import Cslib.Logics.Propositional.NaturalDeduction.Equivalence` after `DerivedRules`
- [ ] Add `public import Cslib.Logics.Propositional.NaturalDeduction.HilbertDerivedRules` after `Equivalence`

**Timing**: 5 minutes

**Depends on**: none

**Files to modify**:
- `Cslib.lean` - Add 3 import lines after line 295

**Verification**:
- `grep -c "DerivedRules\|Equivalence\|HilbertDerivedRules" Cslib.lean` returns 3

---

### Phase 2: Fix Unused DecidableEq Warning [NOT STARTED]

**Goal**: Remove the unused `[DecidableEq Atom']` type class parameter from `hilbertSubstitutionDeriv` to eliminate the lint warning.

**Tasks**:
- [ ] Remove `[DecidableEq Atom']` from the type signature of `hilbertSubstitutionDeriv` at line 212 of `FromHilbert.lean`
- [ ] Verify via `lean_goal` or `lake build` that the definition still compiles without the parameter

**Timing**: 10 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/FromHilbert.lean` - Remove `[DecidableEq Atom']` from `hilbertSubstitutionDeriv` signature (line 212)

**Verification**:
- `grep "DecidableEq" Cslib/Logics/Propositional/NaturalDeduction/FromHilbert.lean` returns no matches
- File compiles without warnings

---

### Phase 3: Verify Clean Compilation [NOT STARTED]

**Goal**: Confirm the full project builds cleanly after the fixes, with zero errors and no new warnings in propositional scope.

**Tasks**:
- [ ] Run `lake build` and confirm exit code 0
- [ ] Check for warnings in propositional scope: `lake build 2>&1 | grep -i "Propositional\|FromHilbert"`
- [ ] Verify zero sorries: `grep -rn "sorry" Cslib/Logics/Propositional/ Cslib/Foundations/Logic/`
- [ ] Verify no debug artifacts: `grep -rn "#check\|#eval\|#print" Cslib/Logics/Propositional/ Cslib/Foundations/Logic/`

**Timing**: 15 minutes (mostly build time)

**Depends on**: 1, 2

**Files to modify**:
- None (verification only)

**Verification**:
- `lake build` succeeds with exit code 0
- No sorry occurrences in propositional/Foundations scope
- No debug artifacts in propositional/Foundations scope

---

### Phase 4: Create Feature Branch and Submit PR [NOT STARTED]

**Goal**: Create a feature branch, commit all changes, and submit PR 1.5 via GitHub CLI.

**Tasks**:
- [ ] Create and switch to feature branch `pr1.5/propositional-hilbert`
- [ ] Stage all propositional/Foundations changes
- [ ] Create commit with descriptive message summarizing the 16-file changeset
- [ ] Push branch to origin
- [ ] Submit PR via `gh pr create` targeting `main` with:
  - Title: `feat(Logics/Propositional): PR 1.5 propositional Hilbert system`
  - Body: scope summary (3 new files, 13 modified), key changes (3-level hierarchy, ND-Hilbert equivalence, derived rules, lint cleanup), dependency note (PR 1.5 must merge before PR 2)

**Timing**: 30 minutes

**Depends on**: 3

**Files to modify**:
- `Cslib.lean` - Already modified in Phase 1
- `Cslib/Logics/Propositional/NaturalDeduction/FromHilbert.lean` - Already modified in Phase 2
- All other propositional/Foundations files staged as-is

**Verification**:
- PR URL is returned by `gh pr create`
- PR description accurately lists the 16-file scope
- Branch is pushed to origin

## Testing & Validation

- [ ] `lake build` succeeds with exit code 0 after all fixes
- [ ] Zero sorries in `Cslib/Logics/Propositional/` and `Cslib/Foundations/Logic/`
- [ ] Zero debug artifacts (#check, #eval, #print) in propositional scope
- [ ] No remaining lint warnings for `DecidableEq` in `FromHilbert.lean`
- [ ] Three new imports present in `Cslib.lean`
- [ ] PR created and accessible via GitHub

## Artifacts & Outputs

- `specs/090_pr_1_5_propositional_hilbert_submission/plans/01_pr-submission-plan.md` (this file)
- `specs/090_pr_1_5_propositional_hilbert_submission/summaries/01_pr-submission-summary.md` (after implementation)
- GitHub PR URL (created in Phase 4)

## Rollback/Contingency

If the `DecidableEq` removal causes compilation failures:
1. Re-add `[DecidableEq Atom']` to `hilbertSubstitutionDeriv`
2. Add `open scoped Classical in` before the definition instead
3. If neither works, suppress the linter warning with `@[nolint unusedArguments]`

If the PR submission fails:
1. Verify GitHub CLI authentication: `gh auth status`
2. Verify remote is set: `git remote -v`
3. Fall back to manual PR creation via GitHub web UI
