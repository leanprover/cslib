# Implementation Plan: Sub-PR 1.1.1 Proposition Type to Lukasiewicz Convention

- **Task**: 138 - Sub-PR 1.1.1: Proposition type to Lukasiewicz convention
- **Status**: [NOT STARTED]
- **Effort**: 1.5 hours
- **Dependencies**: Task 125 (parent plan), upstream remote configured
- **Research Inputs**: reports/01_proposition-refactor.md
- **Artifacts**: plans/01_proposition-refactor.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

Extract the Lukasiewicz convention refactor from local main into a standalone PR against upstream/main. The local main branch already contains all correct, type-checked code; implementation is a file extraction and git branch management task. The PR introduces bot/imp as primitive Proposition constructors (replacing and/or/impl), adds the Connectives.lean typeclass hierarchy, simplifies NaturalDeduction/Basic.lean from 10 rules to 5, and adds the ChagrovZakharyaschev1997 reference. Total diff is approximately 292 lines across 6 files.

### Research Integration

Research report `reports/01_proposition-refactor.md` confirmed:
- All 4 Lean files exist on local main and type-check without errors
- Upstream has the old and/or/impl constructors; Connectives.lean does not exist upstream
- ChagrovZakharyaschev1997 exists in local references.bib but not upstream
- Diff estimate is ~292 lines (176 insertions, 104 deletions), well under 500-line limit
- No downstream breakage risk since dependent files do not exist upstream

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task advances the Foundations/Logic layer of the CSLib roadmap, specifically establishing the shared Connectives infrastructure and Lukasiewicz convention that all downstream logic modules depend on.

## Goals & Non-Goals

**Goals**:
- Create a clean branch from upstream/main with exactly the 6 files changed
- Pass the full CSLib CI pipeline (lake build, lake test, checkInitImports, lint-style, mk_all --check)
- Submit a PR with proper title, description, AI disclosure, and Zulip topic link

**Non-Goals**:
- Writing or modifying Lean proofs (all code already exists on local main)
- Including DerivedRules.lean, Axioms.lean, ProofSystem.lean, or any other files from later PRs
- Creating the Zulip topic (assumed already done per task 125 Phase 1)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `lake shake` flags the `import` -> `public import` change in InferenceSystem.lean | L | L | Revert to `public import` if needed; single-line fix |
| `lake exe mk_all --check` fails due to extra/missing imports in Cslib.lean | M | L | Run `lake exe mk_all --module` to regenerate, then verify diff |
| Merge conflict with concurrent upstream changes | L | L | The files being touched are not actively modified upstream; rebase if needed |
| references.bib format mismatch with upstream conventions | L | L | Match existing entry formatting; BibTeX is tolerant of style variation |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel.

### Phase 1: Branch Creation and File Extraction [NOT STARTED]

**Goal**: Create a clean branch from upstream/main and extract the 6 target files from local main.

**Tasks**:
- [ ] Fetch latest upstream: `git fetch upstream`
- [ ] Create and switch to branch: `git checkout -b refactor/proposition-lukasiewicz upstream/main`
- [ ] Extract 4 Lean files from local main:
  - `git checkout main -- Cslib/Foundations/Logic/Connectives.lean`
  - `git checkout main -- Cslib/Logics/Propositional/Defs.lean`
  - `git checkout main -- Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`
  - `git checkout main -- Cslib/Foundations/Logic/InferenceSystem.lean`
- [ ] Extract the ChagrovZakharyaschev1997 entry from local main's references.bib into the branch's references.bib (add only that one entry, preserving alphabetical order)
- [ ] Add the Connectives.lean import to Cslib.lean: `public import Cslib.Foundations.Logic.Connectives`
- [ ] Run `lake exe mk_all --module --check` to verify Cslib.lean is correct (or run `lake exe mk_all --module` to regenerate if needed)
- [ ] Stage and commit: `git add -A && git commit -m "refactor: Proposition type to Lukasiewicz convention"`

**Timing**: 30 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/Connectives.lean` - NEW (98 lines, extracted from local main)
- `Cslib/Logics/Propositional/Defs.lean` - REPLACE (bot/imp primitives, derived connectives)
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` - REPLACE (5 rules replacing 10)
- `Cslib/Foundations/Logic/InferenceSystem.lean` - REPLACE (minor visibility + docstring)
- `references.bib` - ADD ChagrovZakharyaschev1997 entry
- `Cslib.lean` - ADD Connectives import line

**Verification**:
- `git diff upstream/main --stat` shows exactly 6 files changed
- `git diff upstream/main | wc -l` is approximately 292 lines
- No files from later PRs (DerivedRules, Axioms, ProofSystem, Semantics, etc.) are included

---

### Phase 2: CI Verification and Fixes [NOT STARTED]

**Goal**: Run the full CSLib CI pipeline on the branch and fix any issues.

**Tasks**:
- [ ] Run `lake build` and verify clean compilation
- [ ] Run `lake test` and verify CslibTests pass
- [ ] Run `lake exe checkInitImports` and verify all files import Cslib.Init (directly or transitively)
- [ ] Run `lake exe lint-style` and fix any style issues
- [ ] Run `lake shake --add-public --keep-implied --keep-prefix` and verify no unnecessary dependencies
- [ ] Run `lake exe mk_all --module --check` to verify Cslib.lean completeness
- [ ] If any CI step fails, diagnose and fix on the branch, then amend or add a fixup commit

**Timing**: 40 minutes

**Depends on**: 1

**Files to modify**:
- Potentially any of the 6 files from Phase 1 if CI reveals issues
- Most likely no changes needed (code is already verified on local main)

**Verification**:
- All 6 CI commands exit with code 0
- No warnings or errors in any output

---

### Phase 3: PR Submission [NOT STARTED]

**Goal**: Push the branch to origin and create the PR against upstream/main with proper metadata.

**Tasks**:
- [ ] Push branch to origin: `git push -u origin refactor/proposition-lukasiewicz`
- [ ] Create PR using `gh pr create` with:
  - **Title**: `refactor: Proposition type to Lukasiewicz convention`
  - **Base**: `upstream/main` (i.e., `leanprover/cslib:main`)
  - **Body** including:
    - Summary of the Lukasiewicz convention (bot/imp as primitives, derived connectives)
    - Reference to Chagrov & Zakharyaschev, *Modal Logic* (1997), Chapter 1
    - Link to PR #633 (the original large PR)
    - Link to the Zulip topic
    - File-by-file change summary
    - AI disclosure per CONTRIBUTING.md
- [ ] Verify PR appears correctly on GitHub

**Timing**: 20 minutes

**Depends on**: 2

**Files to modify**:
- No file changes; git push and PR creation only

**Verification**:
- PR is visible on GitHub with correct title, description, and base branch
- PR diff shows exactly the expected 6 files
- CI checks begin running on the PR

## Testing & Validation

- [ ] `lake build` compiles without errors on the PR branch
- [ ] `lake test` passes all CslibTests
- [ ] `lake exe checkInitImports` reports no violations
- [ ] `lake exe lint-style` reports no style issues
- [ ] `lake shake --add-public --keep-implied --keep-prefix` reports no dependency issues
- [ ] `lake exe mk_all --module --check` passes
- [ ] `git diff upstream/main --stat` shows exactly 6 files
- [ ] Total diff is under 500 lines

## Artifacts & Outputs

- `specs/138_subpr_1_1_1_proposition_refactor/plans/01_proposition-refactor.md` (this plan)
- `specs/138_subpr_1_1_1_proposition_refactor/reports/01_proposition-refactor.md` (research report)
- Branch `refactor/proposition-lukasiewicz` on origin
- Pull request against `leanprover/cslib:main`

## Rollback/Contingency

If the PR branch has issues that cannot be resolved:
1. Delete the branch locally: `git checkout main && git branch -D refactor/proposition-lukasiewicz`
2. Delete the remote branch: `git push origin --delete refactor/proposition-lukasiewicz`
3. Close the PR if already created
4. Re-extract files from local main onto a fresh branch from upstream/main
