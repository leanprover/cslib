# Implementation Plan: Combined PR 1+1.5 Submission

- **Task**: 91 - Combined PR 1+1.5 propositional Hilbert submission
- **Status**: [IMPLEMENTING]
- **Effort**: 2-3 hours (mostly build/test time)
- **Dependencies**: Tasks 86-89 (completed), PR #629 (to be closed)
- **Research Inputs**: specs/091_pr_1_5_propositional_hilbert_submission/reports/01_pr-scope-review.md
- **Artifacts**: plans/02_combined-pr-submission.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

Close PR #629 and resubmit a combined PR containing both the original PR 1 content (Foundations/Logic + Propositional proof systems) and the PR 1.5 additions (tasks 86-89: lint cleanup, ND-Hilbert equivalence, intuitionistic base hierarchy, derived connective rules). The existing `pr1/foundations-logic` branch is updated in-place by selectively applying PR 1.5 file changes, then all CI checks from CONTRIBUTING.md are run before resubmission.

### Research Integration

Key findings from the scope review (report 01) and branch analysis:
- **16 files** need updating on the PR branch: 3 new files, 13 modified
- **15 of 16 files** are identical between end-of-task-89 (`71607caf`) and current main — safe to pull from main
- **1 file** (`ProofSystem.lean`) was modified by task 92 (modal cube) after task 89 — must use version from `71607caf` to exclude modal cube additions (ModalTHilbert, ModalDHilbert, ModalS4Hilbert, tag types) that belong in PR 2
- **Cslib.lean** needs only 3 new imports added surgically (DerivedRules, Equivalence, HilbertDerivedRules) — NOT the full main version which includes 128+ Modal/Temporal/Bimodal imports
- **No cherry-pick needed**: since the PR branch has squashed commits, direct file checkout from the correct source commits is cleaner and avoids conflicts with out-of-scope files (Bimodal/Temporal instances, noshake.json)
- **PR #629** has 0 reviews, 0 comments — nothing lost by closing and resubmitting

### Prior Plan Reference

Supersedes `plans/01_pr-submission-plan.md` which targeted a standalone PR 1.5. The new plan combines PR 1 and PR 1.5 into a single submission.

### Roadmap Alignment

This plan advances:
- Propositional Hilbert theorems (extends Completed items)
- 3-level typeclass hierarchy (MinimalHilbert -> IntuitionisticHilbert -> ClassicalHilbert)
- ND-Hilbert extensional equivalence
- Derived connective rules for both proof systems

## Goals & Non-Goals

**Goals**:
- Update `pr1/foundations-logic` with all PR 1.5 changes (tasks 86-89)
- Review code quality for anything worth fixing or improving
- Pass all CI checks described in CONTRIBUTING.md
- Close PR #629 and resubmit as a combined PR

**Non-Goals**:
- Including modal cube work (tasks 92-98) — that's PR 2
- Including Modal/Temporal/Bimodal imports in Cslib.lean
- Modifying any files outside Foundations/Logic, Logics/Propositional, Foundations/Data/ListHelpers.lean, and Cslib.lean

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| File checkout creates merge conflicts with PR branch state | H | L | PR branch has squashed equivalent of pre-task-86 state; task 86-89 diffs should apply cleanly. Fall back to manual conflict resolution. |
| ProofSystem.lean from `71607caf` includes modal classes that upstream doesn't have yet | M | L | Already present in PR 1 (ModalHilbert, ModalS5Hilbert, etc.); the PR 1 branch already includes these generic definitions. Task 88 just renames the base. The modal cube classes (task 92) are excluded. |
| CI fails on upstream-incompatible changes | H | M | Run full CI locally before submitting. If shake/lint issues arise, fix them in Phase 3. |
| Upstream main has advanced since PR branch was created | M | L | PR branch merge-base is current upstream HEAD (`b9d8076d`). No rebase needed. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

### Phase 1: Apply PR 1.5 Changes to Feature Branch [COMPLETED]

**Goal**: Update `pr1/foundations-logic` with all PR 1.5 content from tasks 86-89, without including modal cube (task 92+) or out-of-scope changes.

**Tasks**:
- [ ] Switch to `pr1/foundations-logic`: `git checkout pr1/foundations-logic`
- [ ] Apply ProofSystem.lean from end-of-task-89 (NOT main, to exclude modal cube additions):
  ```bash
  git checkout 71607caf -- Cslib/Foundations/Logic/ProofSystem.lean
  ```
- [ ] Apply 14 remaining files from main (identical between `71607caf` and main):
  ```bash
  git checkout main -- \
    Cslib/Foundations/Data/ListHelpers.lean \
    Cslib/Foundations/Logic/Theorems.lean \
    Cslib/Foundations/Logic/Theorems/BigConj.lean \
    Cslib/Foundations/Logic/Theorems/Combinators.lean \
    Cslib/Foundations/Logic/Theorems/Propositional/Connectives.lean \
    Cslib/Foundations/Logic/Theorems/Propositional/Core.lean \
    Cslib/Foundations/Logic/Theorems/Temporal/FrameConditions.lean \
    Cslib/Logics/Propositional/Defs.lean \
    Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean \
    Cslib/Logics/Propositional/Metalogic/MCS.lean \
    Cslib/Logics/Propositional/NaturalDeduction/DerivedRules.lean \
    Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean \
    Cslib/Logics/Propositional/NaturalDeduction/HilbertDerivedRules.lean \
    Cslib/Logics/Propositional/ProofSystem/Instances.lean
  ```
- [ ] Add 3 new NaturalDeduction imports to `Cslib.lean` (after the existing `FromHilbert` import line):
  ```lean
  public import Cslib.Logics.Propositional.NaturalDeduction.DerivedRules
  public import Cslib.Logics.Propositional.NaturalDeduction.Equivalence
  public import Cslib.Logics.Propositional.NaturalDeduction.HilbertDerivedRules
  ```
- [ ] Commit: `feat(Logics/Propositional): add Hilbert-ND equivalence, derived rules, and intuitionistic hierarchy`

**Timing**: 15 minutes

**Depends on**: none

**Files to modify**:
- 13 existing files updated via checkout
- 3 new files created via checkout (DerivedRules.lean, Equivalence.lean, HilbertDerivedRules.lean)
- `Cslib.lean` — 3 import lines added manually

**Verification**:
- `git diff --stat HEAD~1` shows 16 files changed
- `git diff HEAD -- Cslib.lean` shows only 3 new import lines
- No Modal/Temporal/Bimodal files modified
- No modal cube classes (ModalTHilbert, ModalDHilbert, ModalS4Hilbert) in ProofSystem.lean

---

### Phase 2: Code Quality Review [COMPLETED]

**Goal**: Review the complete PR branch for code quality issues worth fixing before submission.

**Tasks**:
- [ ] Zero sorry check:
  ```bash
  grep -rn "sorry" Cslib/Logics/Propositional/ Cslib/Foundations/Logic/ Cslib/Foundations/Data/ListHelpers.lean
  ```
- [ ] Zero debug artifacts:
  ```bash
  grep -rn "#check\|#eval\|#print" Cslib/Logics/Propositional/ Cslib/Foundations/Logic/
  ```
- [ ] Fix unused `[DecidableEq Atom']` warning in `FromHilbert.lean:210-217` — remove the parameter from `hilbertSubstitutionDeriv`
- [ ] Review proof style per CONTRIBUTING.md: check for overly golfed proofs, ensure documentation references, check notation scoping
- [ ] Check Apache 2.0 copyright headers on all new files (DerivedRules.lean, Equivalence.lean, HilbertDerivedRules.lean)
- [ ] Verify module keyword and public imports follow upstream conventions
- [ ] Check for any TODO/FIXME/HACK that should be resolved
- [ ] If any issues found, fix and amend the Phase 1 commit

**Timing**: 30 minutes

**Depends on**: Phase 1

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/FromHilbert.lean` — remove `[DecidableEq Atom']`
- Any files with quality issues discovered during review

**Verification**:
- Zero sorry, zero debug artifacts
- No linter warnings in PR-scope files
- All new files have proper headers and documentation

---

### Phase 3: Run Full CI Test Suite [COMPLETED]

**Goal**: Run all CI checks from CONTRIBUTING.md on the feature branch to ensure the combined PR passes upstream CI.

**Tasks**:
- [ ] Full build: `lake build`
- [ ] Test suite: `lake test`
- [ ] Init imports check: `lake exe checkInitImports`
- [ ] Environment linters: `lake lint`
- [ ] Text linters: `lake exe lint-style` (use `--fix` if issues found)
- [ ] Root import completeness: `lake exe mk_all --module` (use `--check` to verify, no-op expected)
- [ ] Import minimization: `lake shake --add-public --keep-implied --keep-prefix` (review recommendations; apply with `--fix` if safe)
- [ ] If any check fails, fix the issue, amend the commit, and re-run the failed check

**Timing**: 1-2 hours (mostly build time; lake build ~20-30 min, lake shake ~15-20 min)

**Depends on**: Phase 2

**Files to modify**:
- Any files that fail CI checks (fix in place)

**Verification**:
- All 7 CI checks pass with exit code 0
- No new warnings introduced by the PR changes

**Note on `lake shake`**: Upstream CI currently has shake commented out, but recommendations should still be reviewed. Only apply changes that don't break `checkInitImports` or the build. Use `--fix` cautiously — some recommendations break transitive imports.

**Note on `lake build`**: This runs on the feature branch which lacks Modal/Temporal/Bimodal files that exist on our local main. The build will compile only what's on the branch (upstream + Foundations/Propositional additions). Ensure it succeeds on this reduced scope.

---

### Phase 4: Close #629 and Submit Combined PR [COMPLETED]

**Goal**: Close the old PR and submit the combined PR 1+1.5.

**Tasks**:
- [ ] Close PR #629 with a comment explaining the consolidation:
  ```bash
  gh pr close 629 --comment "Closing to resubmit as a combined PR that includes both the original Foundations/Logic content and the subsequent propositional Hilbert additions (ND-Hilbert equivalence, intuitionistic base hierarchy, derived connective rules)."
  ```
- [ ] Force-push the updated `pr1/foundations-logic` branch:
  ```bash
  git push origin pr1/foundations-logic --force-with-lease
  ```
- [ ] Submit new PR via `gh pr create` with:
  - **Title**: `feat(Foundations/Logic): Hilbert proof systems, ND equivalence, and intuitionistic hierarchy`
  - **Base**: `main` (upstream)
  - **Body**: Combined scope description covering both PR 1 and PR 1.5 content:
    - Summary of the full 28-file changeset (25 original + 3 new)
    - Core definitions (InferenceSystem, 3-level Hilbert hierarchy, connective classes)
    - Theorem libraries (combinators, propositional, modal, temporal)
    - Metalogic (Lindenbaum, MCS, deduction theorem)
    - ND system (Basic, FromHilbert, DerivedRules, Equivalence, HilbertDerivedRules)
    - Design notes (Lukasiewicz encoding, Hilbert-vs-ND, 3-level hierarchy)
    - AI disclosure per CONTRIBUTING.md
    - Note that this consolidates the content from closed PR #629

**Timing**: 20 minutes

**Depends on**: Phase 3

**Files to modify**: none (submission only)

**Verification**:
- PR #629 is closed
- New PR is created and accessible
- PR description accurately lists the full scope
- Branch is pushed to origin

## Testing & Validation

- [ ] `lake build` succeeds with exit code 0
- [ ] `lake test` passes
- [ ] `lake exe checkInitImports` passes
- [ ] `lake lint` passes
- [ ] `lake exe lint-style` passes (or `--fix` applied)
- [ ] `lake exe mk_all --module --check` passes
- [ ] `lake shake --add-public --keep-implied --keep-prefix` reviewed
- [ ] Zero sorry in PR-scope files
- [ ] Zero debug artifacts in PR-scope files
- [ ] No modal cube classes (ModalTHilbert/DHilbert/S4Hilbert) in ProofSystem.lean
- [ ] No Bimodal/Modal/Temporal imports in Cslib.lean
- [ ] PR created with correct scope description

## Artifacts & Outputs

- `specs/091_pr_1_5_propositional_hilbert_submission/plans/02_combined-pr-submission.md` (this file)
- `specs/091_pr_1_5_propositional_hilbert_submission/summaries/02_combined-pr-summary.md` (after implementation)
- GitHub PR URL (created in Phase 4)

## Rollback/Contingency

If file checkouts create merge conflicts on the PR branch:
1. Stash changes: `git stash`
2. Fall back to generating a diff and applying manually:
   ```bash
   git diff pr1/foundations-logic 71607caf -- <file> | git apply
   ```

If CI checks fail on the feature branch due to missing upstream dependencies:
1. Rebase `pr1/foundations-logic` onto latest `upstream/main`: `git fetch upstream && git rebase upstream/main`
2. Re-apply the PR 1.5 changes
3. Re-run CI checks

If the combined PR is too large for review:
1. Add a "Reviewing Guide" section to the PR description pointing reviewers to the most important files first (ProofSystem.lean, Equivalence.lean, DerivedRules.lean)
2. Offer to split into smaller review chunks if requested by maintainers
