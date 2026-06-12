# Implementation Plan: Sub-PR 3.1 Temporal Formula Type

- **Task**: 159 - Sub-PR 3.1: Temporal formula type
- **Status**: [COMPLETED]
- **Effort**: 1.5 hours
- **Dependencies**: Task 138 (PR #633 -- Connectives.lean must be merged or used as base branch)
- **Research Inputs**: specs/159_subpr_3_1_temporal_formula/reports/01_temporal-formula-research.md
- **Artifacts**: plans/01_temporal-formula-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

This plan covers creating and submitting a GitHub PR to `leanprover/cslib` for the temporal logic `Formula` inductive type. The file `Cslib/Logics/Temporal/Syntax/Formula.lean` (549 lines) already exists locally and builds cleanly with zero `sorry` instances. The implementation work is PR submission -- branching from the `pr1/foundations-logic` base (which provides the `Connectives.lean` dependency), cherry-picking or copying the file, verifying CI, and opening the PR. This is a stacked PR: it depends on PR #633.

### Research Integration

Research (report 01) confirmed:
- Formula.lean is 549 lines, sorry-free, passes all lints and builds
- Depends on `Cslib.Foundations.Logic.Connectives` from PR #633 (currently OPEN)
- File does not exist in `upstream/main` or on `pr1/foundations-logic`
- Barrel import (`Cslib.lean` line 395) exists locally but not upstream
- Stacked PR approach (branching from `pr1/foundations-logic`) is recommended
- PR #633 is listed under author `benbrastmckie`, currently OPEN

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consultation was requested for this plan.

## Goals & Non-Goals

**Goals**:
- Create a PR branch from `pr1/foundations-logic` containing Formula.lean
- Update the barrel import file (`Cslib.lean`) via `lake exe mk_all --module`
- Verify all CSLib CI checks pass on the branch
- Open a GitHub PR to `leanprover/cslib` with proper title, description, and AI disclosure

**Non-Goals**:
- Modifying the Formula.lean content (file is already complete and verified)
- Submitting downstream files (BigConj, Context, Subformulas) -- those are separate PRs
- Waiting for PR #633 to merge before creating this PR (stacked PR approach)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| PR #633 not yet merged, causing CI failure on PR target branch | M | M | Use stacked PR (base on `pr1/foundations-logic`); GitHub shows dependency chain |
| Formula.lean has diverged from local main since research | L | L | Diff-check Formula.lean against the version verified in research |
| `lake exe mk_all --module` generates unexpected barrel changes | L | L | Run on clean branch, review diff before committing |
| PR reviewers request changes to Formula.lean | M | M | File follows all conventions; address review feedback if needed |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

### Phase 1: Create PR Branch and Add Formula.lean [COMPLETED]

**Goal**: Create a clean branch from `pr1/foundations-logic` containing only the Formula.lean file and barrel import update.

**Tasks**:
- [ ] Create branch `feat/temporal-formula` from `pr1/foundations-logic`
- [ ] Copy `Cslib/Logics/Temporal/Syntax/Formula.lean` from local main to the new branch
- [ ] Create necessary directory structure (`Cslib/Logics/Temporal/Syntax/`)
- [ ] Run `lake exe mk_all --module` to update `Cslib.lean` with the new import
- [ ] Verify only the expected files changed: `Formula.lean` (new) and `Cslib.lean` (+1 line)
- [ ] Commit changes with message: `feat(Logics/Temporal): add temporal logic formula type`

**Timing**: 30 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Temporal/Syntax/Formula.lean` - New file (549 lines)
- `Cslib.lean` - Add `public import Cslib.Logics.Temporal.Syntax.Formula`

**Verification**:
- `git diff --stat` shows exactly 2 files changed
- Formula.lean matches the researched 549-line version

---

### Phase 2: CI Verification [COMPLETED]

**Goal**: Run the full CSLib CI verification pipeline on the PR branch to confirm the submission is clean.

**Tasks**:
- [ ] Run `lake build Cslib.Logics.Temporal.Syntax.Formula` (scoped build)
- [ ] Run `lake exe checkInitImports` (verify `Cslib.Init` import)
- [ ] Run `lake exe lint-style` (text linting)
- [ ] Run `lake test` (CslibTests suite)
- [ ] Run `lake exe mk_all --module` and verify no diff (barrel file current)
- [ ] Verify zero `sorry` in file: `grep -c "sorry" Cslib/Logics/Temporal/Syntax/Formula.lean`
- [ ] Run `lake shake --add-public --keep-implied --keep-prefix` (import minimization check)

**Timing**: 30 minutes

**Depends on**: 1

**Files to modify**:
- None (verification only; fix any issues if found)

**Verification**:
- All 7 CI checks pass with zero errors
- No `sorry` found in the file

---

### Phase 3: Open GitHub PR [NOT STARTED] *(deviation: skipped -- user explicitly asked to prepare but not submit PR)*

**Goal**: Submit the PR to `leanprover/cslib` with proper metadata, description, and AI disclosure.

**Tasks**:
- [ ] Push branch `feat/temporal-formula` to `origin`
- [ ] Create PR via `gh pr create` targeting `leanprover/cslib` main branch, with base `pr1/foundations-logic`
- [ ] PR title: `feat(Logics/Temporal): add temporal logic formula type with primitives and derived operators`
- [ ] PR description includes: summary of Formula inductive (5 primitives), derived connectives, typeclass registrations, swapTemporal involution, countability instances
- [ ] PR description includes dependency note: "Depends on PR #633 (Foundations/Logic)"
- [ ] PR description includes AI disclosure per CSLib policy
- [ ] Verify PR appears on GitHub and CI triggers

**Timing**: 30 minutes

**Depends on**: 2

**Files to modify**:
- None (PR submission only)

**Verification**:
- PR URL returned by `gh pr create`
- PR is visible on `leanprover/cslib` with correct base branch
- CI begins running on the PR

## Testing & Validation

- [ ] `lake build Cslib.Logics.Temporal.Syntax.Formula` passes
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] `lake test` passes
- [ ] `lake exe mk_all --module` produces no diff
- [ ] Zero `sorry` in file
- [ ] PR is created and CI triggers

## Artifacts & Outputs

- `specs/159_subpr_3_1_temporal_formula/plans/01_temporal-formula-plan.md` (this file)
- `specs/159_subpr_3_1_temporal_formula/summaries/01_temporal-formula-summary.md` (after implementation)
- GitHub PR on `leanprover/cslib` (feat/temporal-formula branch)

## Rollback/Contingency

- If CI fails on the PR branch: fix issues locally, amend commit, force-push
- If PR #633 base causes conflicts: rebase `feat/temporal-formula` on latest `pr1/foundations-logic`
- If Formula.lean needs content changes: edit on the branch, re-run CI, update commit
- Delete the branch with `git branch -D feat/temporal-formula` and `git push origin --delete feat/temporal-formula` to fully revert
