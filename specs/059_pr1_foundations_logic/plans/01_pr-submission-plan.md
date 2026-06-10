# Implementation Plan: PR 1 Submission -- Foundations/Logic

- **Task**: 59 - pr1_foundations_logic
- **Status**: [NOT STARTED]
- **Effort**: 2 hours
- **Dependencies**: Task 58 (CI prep -- completed)
- **Research Inputs**: specs/059_pr1_foundations_logic/reports/01_primitive-connectives-justification.md
- **Artifacts**: plans/01_pr-submission-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

Submit the first PR for the cslib repository containing all 15 Foundations/Logic files (3,621 lines total). The PR covers core definitions (InferenceSystem, Connectives, Axioms, ProofSystem, LogicalEquivalence), theorem libraries (Combinators, Propositional, Modal, Temporal, BigConj), and metalogic foundations (Consistency/Lindenbaum). This is the foundational layer that all subsequent PRs (Modal metalogic, Temporal semantics, etc.) depend on. The PR description will integrate research findings justifying the {bot, imp} primitive connective choice.

### Research Integration

The research report (01_primitive-connectives-justification.md) provides six key arguments for the PR description: (1) historical basis in Church 1956 / Tarski-Bernays-Wajsberg, (2) clean classical/intuitionistic separation via single Peirce axiom, (3) Curry-Howard alignment (imp = function type, bot = Empty), (4) polymorphic abbrev design avoiding typeclass diamonds, (5) Lukasiewicz-derived connectives get definitional equality for free, (6) MCS foundations parameterized over the minimal {bot, imp} interface.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This plan advances the "Submit PRs" task chain (tasks 59-64). PR 1 must merge first since all downstream PRs (Modal metalogic, Temporal semantics, Temporal metalogic, Chronicle infrastructure, Completeness) import from Foundations/Logic.

## Goals & Non-Goals

**Goals**:
- Create feature branch `feat/foundations-logic` from `main`
- Verify all 15 files pass CI checks (build, sorry-free, headers, lint)
- Add missing `public import` lines to `Cslib.lean` (10 modules not yet registered)
- Run `lake exe mk_all` to regenerate `Cslib.lean` consistently
- Write a compelling PR description integrating research findings on primitive connective choice
- Submit the PR via `gh pr create`

**Non-Goals**:
- Modifying any Lean source code (all files are assumed ready from task 58 CI baseline)
- Addressing reviewer feedback (that is post-submission work)
- Submitting any files outside `Cslib/Foundations/Logic/` and `Cslib.lean`

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `lake build` fails on branch | H | L | Task 58 established clean baseline; run build early in Phase 1 |
| `lake exe mk_all` reorders or adds unexpected imports | M | M | Diff `Cslib.lean` after mk_all; only commit Foundations/Logic additions |
| `lake shake` flags unused imports in Foundations files | M | L | Run shake and fix before branching; these are well-tested files |
| CI linter rejects style issues | M | L | Run `lake lint` and `lake exe lint-style` pre-submission |
| `InferenceSystem.lean` and `LogicalEquivalence.lean` authored by Fabrizio Montesi | L | L | Headers are correct Apache 2.0; no action needed, just note in PR |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel.

### Phase 1: Pre-PR Verification [NOT STARTED]

**Goal**: Confirm all 15 files are CI-clean on main before creating the feature branch.

**Tasks**:
- [ ] Run `lake build` and confirm zero errors
- [ ] Run `grep -rn "sorry" Cslib/Foundations/Logic/` and confirm zero hits
- [ ] Verify all 15 files have Apache 2.0 headers with correct author attribution
- [ ] Run `lake exe mk_all` and diff `Cslib.lean` to identify needed additions
- [ ] Add the 10 missing `public import` lines to `Cslib.lean` for Theorems/*, Metalogic/Consistency
- [ ] Run `lake build` again after Cslib.lean changes to confirm no regressions
- [ ] Run `lake exe checkInitImports` (if available) to verify import graph consistency

**Timing**: 45 minutes

**Depends on**: none

**Files to modify**:
- `Cslib.lean` -- add 10 missing `public import` lines for Foundations/Logic modules

**Verification**:
- `lake build` exits 0
- `grep -rn sorry Cslib/Foundations/Logic/` returns nothing
- All 15 files have `Released under Apache 2.0 license` in header
- `Cslib.lean` includes all 15 Foundations/Logic modules

---

### Phase 2: Branch Creation and PR Description [NOT STARTED]

**Goal**: Create feature branch, write PR title and description integrating research findings.

**Tasks**:
- [ ] Create feature branch: `git checkout -b feat/foundations-logic`
- [ ] Stage `Cslib.lean` changes (the only file modified on this branch)
- [ ] Commit with message `task 59: add Foundations/Logic public imports to Cslib.lean`
- [ ] Draft PR description with these sections:
  - **Summary**: 15 files, ~3,600 lines, covers propositional/modal/temporal theorem infrastructure + MCS foundations
  - **Primitive connective justification**: {bot, imp} basis following Church (1956), Tarski-Bernays-Wajsberg; derived connectives via Lukasiewicz encoding
  - **Classical/intuitionistic separation**: single Peirce axiom draws the boundary
  - **Curry-Howard alignment**: imp = function type, bot = Empty, K/S axioms = K/S combinators
  - **Typeclass architecture**: HasBot + HasImp atomic classes; no HasNeg/HasAnd/HasOr avoids diamond inheritance
  - **File inventory table**: all 15 files with line counts and roles
  - **MCS scope justification**: included because Modal and Temporal metalogic import Consistency
  - **Dependency graph**: showing import chain from InferenceSystem down to leaf theorems

**Timing**: 45 minutes

**Depends on**: 1

**Files to modify**:
- None (PR description is passed to `gh pr create`, not a file)

**Verification**:
- Feature branch exists with clean commit
- PR description draft covers all six research integration points

---

### Phase 3: CI Checks and PR Submission [NOT STARTED]

**Goal**: Run final CI checks on the feature branch and submit the PR.

**Tasks**:
- [ ] Run `lake build` on feature branch (should be clean)
- [ ] Run `lake shake` to check for unused imports in the 15 files
- [ ] Run `lake lint` or `lake exe lint-style` if available
- [ ] Submit PR via `gh pr create` with:
  - Title: `feat(Foundations/Logic): propositional theorems, modal S5 theorems, and MCS consistency foundations`
  - Body: the description drafted in Phase 2
  - Base branch: `main`
- [ ] Verify PR was created successfully and record the PR URL

**Timing**: 30 minutes

**Depends on**: 2

**Files to modify**:
- None (PR submission only)

**Verification**:
- `gh pr create` returns a PR URL
- PR is visible on GitHub with correct title, description, and file diff
- PR diff shows only `Cslib.lean` changes (the 15 Foundations/Logic .lean files already exist on main)

---

## Testing & Validation

- [ ] `lake build` exits 0 on feature branch
- [ ] Zero `sorry` instances in `Cslib/Foundations/Logic/`
- [ ] All 15 files have correct Apache 2.0 headers
- [ ] `Cslib.lean` includes all 15 Foundations/Logic `public import` lines
- [ ] PR created on GitHub with correct title and description
- [ ] PR diff is minimal (only `Cslib.lean` additions, no unrelated changes)

## Artifacts & Outputs

- `specs/059_pr1_foundations_logic/plans/01_pr-submission-plan.md` (this file)
- `specs/059_pr1_foundations_logic/summaries/01_pr-submission-summary.md` (post-implementation)
- GitHub PR URL (recorded in summary)

## Rollback/Contingency

- If `lake build` fails: investigate error, fix on main first, then retry branch creation
- If `lake shake` flags unused imports: remove them before PR submission
- If PR submission fails: verify `gh` auth with `gh auth status`, re-authenticate if needed
- Branch can be deleted with `git branch -d feat/foundations-logic` if PR needs to be abandoned
