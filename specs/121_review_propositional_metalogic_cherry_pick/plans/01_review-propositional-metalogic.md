# Implementation Plan: Task #121

- **Task**: 121 - Review propositional metalogic and cherry-pick to pr1/foundations-logic
- **Status**: [NOT STARTED]
- **Effort**: 4 hours
- **Dependencies**: None (all source code exists on main, branch exists)
- **Research Inputs**: specs/121_review_propositional_metalogic_cherry_pick/reports/01_review-propositional-metalogic.md
- **Artifacts**: plans/01_review-propositional-metalogic.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

Transfer all propositional Hilbert metalogic and parameterized ND equivalence code from main to the pr1/foundations-logic branch using diff-based file copy (not cherry-pick, due to squash-conflict issues identified in research). The scope covers 22 propositional Lean files (~4,300 lines) plus 2 cross-logic FromPropositional embedding files, selective ProofSystem.lean updates, and Cslib.lean import additions. The work is organized into quality review, file transfer (new then modified), selective shared-file updates, integration, and verification. The task prepares the branch for PR submission but does not submit the PR.

### Research Integration

Key findings from the research report (01_review-propositional-metalogic.md):
- All 22 propositional files on main are sorry-free, have proper headers/docstrings, and follow CONTRIBUTING.md
- The branch has a squashed commit (2d5ea2c6) making individual cherry-picks conflict-prone; diff-based copy is the safe strategy
- 13 NEW files (11 propositional + 2 FromPropositional) and 8 MODIFIED files need to transfer
- ProofSystem.lean has mixed content (propositional tag types needed, modal bundled classes out of scope)
- Cslib.lean needs ~17 additional import lines
- Minimal logic is correctly excluded from ND equivalence (no hilbert_iff_nd_min exists)
- Foundations/Data/ListHelpers.lean and Foundations/Logic/Theorems/Propositional/ are already identical on both branches

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This plan advances:
- Propositional metalogic proof system and completeness results under `Logics/Propositional/`
- Cross-logic embeddings (FromPropositional) linking propositional to modal and temporal modules

The ROADMAP.md "Completed" section already lists modal, temporal, and bimodal metalogic. This task brings the propositional metalogic to the PR branch, filling a foundational gap in the dependency structure.

## Goals & Non-Goals

**Goals**:
- Verify all propositional code on main meets CONTRIBUTING.md standards
- Transfer all in-scope propositional files from main to pr1/foundations-logic
- Ensure the branch builds cleanly with all new content
- Produce a clean, coherent branch state ready for PR review

**Non-Goals**:
- Submit the PR (task scope is branch preparation only)
- Modify any files on main
- Transfer modal bundled classes, bimodal embedding files, or temporal-specific content
- Add minimal logic ND equivalence (correctly excluded -- MinPropAxiom lacks EFQ)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| ProofSystem.lean selective edit introduces modal dependency issues | H | L | Only add HilbertInt/HilbertMin tag types; verify propositional files do not reference modal classes |
| Cslib.lean import ordering breaks mk_all check | M | M | Run `lake exe mk_all --module` to regenerate canonical order |
| Copied files have implicit dependency on main-only changes | H | L | Run `lake build` on branch after all copies; research confirmed propositional files only depend on Foundations + Propositional |
| Build timeout on full `lake build` verification | M | L | Use `lake build Cslib.Logics.Propositional` for targeted check first, then full build |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |

Phases within the same wave can execute in parallel. This plan is fully sequential because each phase builds on the branch state left by the prior phase.

### Phase 1: Quality Review on Main [COMPLETED]

**Goal**: Confirm all in-scope propositional files on main meet CONTRIBUTING.md standards and are sorry-free

**Tasks**:
- [x] Grep all in-scope files for `sorry` to confirm none exist *(completed)*
- [x] Verify all files have `module` keyword (enables Cslib.Init linting) *(completed)*
- [x] Verify all files have Apache 2.0 copyright headers *(completed)*
- [x] Verify all definitions/theorems have docstrings (`/--` format) *(deviation: altered -- Instances.lean and IntMinInstances.lean have 0 docstrings but contain only typeclass instances; consistent with codebase pattern, non-blocking)*
- [x] Verify module headers use `/-! ... -/` format with main results listed *(completed)*
- [x] Confirm minimal logic is excluded from ND equivalence (no `hilbert_iff_nd_min`) *(completed)*
- [x] Confirm `hilbert_iff_nd` requires EFQ witness, correctly excluding MinPropAxiom *(completed)*
- [x] Document any quality issues found (expected: none based on research) *(completed -- no blocking issues)*

**Timing**: 30 minutes

**Depends on**: none

**Files to review** (read-only, no modifications on main):
- `Cslib/Logics/Propositional/Defs.lean`
- `Cslib/Logics/Propositional/ProofSystem/Axioms.lean`
- `Cslib/Logics/Propositional/ProofSystem/Derivation.lean`
- `Cslib/Logics/Propositional/ProofSystem/Instances.lean`
- `Cslib/Logics/Propositional/ProofSystem/IntMinInstances.lean`
- `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean`
- `Cslib/Logics/Propositional/Metalogic/MCS.lean`
- `Cslib/Logics/Propositional/Metalogic/Soundness.lean`
- `Cslib/Logics/Propositional/Metalogic/Completeness.lean`
- `Cslib/Logics/Propositional/Metalogic/IntSoundness.lean`
- `Cslib/Logics/Propositional/Metalogic/IntLindenbaum.lean`
- `Cslib/Logics/Propositional/Metalogic/IntCompleteness.lean`
- `Cslib/Logics/Propositional/Metalogic/MinSoundness.lean`
- `Cslib/Logics/Propositional/Metalogic/MinLindenbaum.lean`
- `Cslib/Logics/Propositional/Metalogic/MinCompleteness.lean`
- `Cslib/Logics/Propositional/Semantics/Basic.lean`
- `Cslib/Logics/Propositional/Semantics/Kripke.lean`
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`
- `Cslib/Logics/Propositional/NaturalDeduction/FromHilbert.lean`
- `Cslib/Logics/Propositional/NaturalDeduction/HilbertDerivedRules.lean`
- `Cslib/Logics/Propositional/NaturalDeduction/DerivedRules.lean`
- `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean`
- `Cslib/Logics/Modal/FromPropositional.lean`
- `Cslib/Logics/Temporal/FromPropositional.lean`

**Verification**:
- All files pass grep checks (no sorry, has module, has headers)
- Quality review documented with pass/fail per criterion

---

### Phase 2: Copy New Files to Branch [NOT STARTED]

**Goal**: Add all 13 files that exist on main but not on pr1/foundations-logic

**Tasks**:
- [ ] Switch to pr1/foundations-logic branch
- [ ] Create necessary directories on branch (Semantics/, if missing)
- [ ] Copy 11 new propositional files from main using `git show main:path > path`:
  - `Cslib/Logics/Propositional/Semantics/Basic.lean`
  - `Cslib/Logics/Propositional/Semantics/Kripke.lean`
  - `Cslib/Logics/Propositional/ProofSystem/IntMinInstances.lean`
  - `Cslib/Logics/Propositional/Metalogic/Soundness.lean`
  - `Cslib/Logics/Propositional/Metalogic/Completeness.lean`
  - `Cslib/Logics/Propositional/Metalogic/IntSoundness.lean`
  - `Cslib/Logics/Propositional/Metalogic/IntLindenbaum.lean`
  - `Cslib/Logics/Propositional/Metalogic/IntCompleteness.lean`
  - `Cslib/Logics/Propositional/Metalogic/MinSoundness.lean`
  - `Cslib/Logics/Propositional/Metalogic/MinLindenbaum.lean`
  - `Cslib/Logics/Propositional/Metalogic/MinCompleteness.lean`
- [ ] Copy 2 new cross-logic embedding files from main:
  - `Cslib/Logics/Modal/FromPropositional.lean`
  - `Cslib/Logics/Temporal/FromPropositional.lean`
- [ ] Git add all 13 new files
- [ ] Create commit: `feat(Logics/Propositional): add semantics, metalogic, and cross-logic embeddings`

**Timing**: 30 minutes

**Depends on**: 1

**Files to create** (on pr1/foundations-logic):
- 11 propositional files listed above
- `Cslib/Logics/Modal/FromPropositional.lean`
- `Cslib/Logics/Temporal/FromPropositional.lean`

**Verification**:
- All 13 files exist on branch
- `git diff main -- <file>` shows no differences for each new file
- Commit is clean with only new files

---

### Phase 3: Update Modified Files on Branch [NOT STARTED]

**Goal**: Replace 8 modified propositional files on branch with their main versions, and selectively update ProofSystem.lean

**Tasks**:
- [ ] Copy 8 modified propositional files from main, overwriting branch versions:
  - `Cslib/Logics/Propositional/ProofSystem/Axioms.lean` (adds IntPropAxiom, MinPropAxiom, subsumption)
  - `Cslib/Logics/Propositional/ProofSystem/Derivation.lean` (parameterized DerivationTree, Deriv, Derivable)
  - `Cslib/Logics/Propositional/ProofSystem/Instances.lean` (minor updates)
  - `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean` (parameterized over Axioms)
  - `Cslib/Logics/Propositional/Metalogic/MCS.lean` (parameterized MCS properties)
  - `Cslib/Logics/Propositional/NaturalDeduction/FromHilbert.lean` (parameterized over Axioms)
  - `Cslib/Logics/Propositional/NaturalDeduction/HilbertDerivedRules.lean` (parameterized, intuitionistic/classical layers)
  - `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` (parameterized hilbert_iff_nd)
- [ ] Selectively update `Cslib/Foundations/Logic/ProofSystem.lean`:
  - Extract ONLY the `HilbertInt` and `HilbertMin` tag type definitions from main
  - Do NOT copy modal bundled class additions (tasks 92, 100) -- these are out of scope
  - Verify the diff contains only propositional additions
- [ ] Git add all modified files
- [ ] Create commit: `feat(Logics/Propositional): parameterize proof system and ND equivalence over axiom sets`

**Timing**: 1 hour

**Depends on**: 2

**Files to modify** (on pr1/foundations-logic):
- 8 propositional files listed above (full replacement from main)
- `Cslib/Foundations/Logic/ProofSystem.lean` (selective additions only)

**Verification**:
- For the 8 propositional files: `git diff main -- <file>` shows zero differences
- For ProofSystem.lean: diff shows only HilbertInt/HilbertMin additions, no modal content
- Commit contains exactly 9 changed files

---

### Phase 4: Integration -- Update Cslib.lean and Verify Imports [NOT STARTED]

**Goal**: Add all missing propositional import lines to Cslib.lean and ensure import consistency

**Tasks**:
- [ ] Run `lake exe mk_all --module` on the branch to auto-generate correct Cslib.lean imports
- [ ] Verify the diff adds the expected ~17 propositional import lines
- [ ] Verify no unrelated imports were added or removed
- [ ] Run `lake exe checkInitImports` to verify all files import Cslib.Init
- [ ] Run `lake shake --add-public --keep-implied --keep-prefix` to check import minimization (use `--fix` if needed)
- [ ] Git add Cslib.lean and any import-fix changes
- [ ] Create commit: `chore(Cslib): add propositional metalogic and embedding imports`

**Timing**: 1 hour

**Depends on**: 3

**Files to modify** (on pr1/foundations-logic):
- `Cslib.lean` - add ~17 import lines for propositional files

**Verification**:
- `lake exe mk_all --module` reports no missing imports
- `lake exe checkInitImports` passes
- `lake shake` reports no unnecessary imports (or issues are fixed)

---

### Phase 5: Full Build and Final Verification [NOT STARTED]

**Goal**: Verify the branch builds cleanly, passes all CI-equivalent checks, and is ready for PR

**Tasks**:
- [ ] Run `lake build` on pr1/foundations-logic to verify full compilation
- [ ] Grep all propositional files on branch for `sorry` (confirm zero)
- [ ] Run `lake exe lint-style` for text linting compliance
- [ ] Verify commit history is clean and descriptive (3 commits from phases 2-4)
- [ ] Verify the complete file list on branch matches expectations:
  - 22 propositional files under `Cslib/Logics/Propositional/`
  - 2 cross-logic files (`Modal/FromPropositional.lean`, `Temporal/FromPropositional.lean`)
  - Updated `Cslib/Foundations/Logic/ProofSystem.lean` with propositional tag types
  - Updated `Cslib.lean` with all imports
- [ ] Verify out-of-scope content is NOT present:
  - No modal bundled classes added to ProofSystem.lean
  - No bimodal or temporal-specific files added
  - No `hilbert_iff_nd_min` definition (minimal ND equivalence correctly absent)
- [ ] Switch back to main branch

**Timing**: 1 hour

**Depends on**: 4

**Files to verify** (read-only checks):
- All propositional files on branch
- `Cslib.lean` import completeness
- `Cslib/Foundations/Logic/ProofSystem.lean` scope correctness

**Verification**:
- `lake build` succeeds with zero errors
- Zero `sorry` found across all files
- `lake exe lint-style` passes
- Branch has exactly 3 new commits (phases 2, 3, 4)
- All scope boundaries verified

## Testing & Validation

- [ ] `lake build` succeeds on pr1/foundations-logic with zero errors
- [ ] `lake exe checkInitImports` passes (all files import Cslib.Init)
- [ ] `lake exe mk_all --module` reports no missing imports in Cslib.lean
- [ ] `lake shake --add-public --keep-implied --keep-prefix` passes
- [ ] `lake exe lint-style` passes with no errors
- [ ] Zero `sorry` in any propositional file on branch
- [ ] No modal bundled classes in ProofSystem.lean diff
- [ ] No `hilbert_iff_nd_min` exists (minimal ND equivalence correctly excluded)

## Artifacts & Outputs

- `specs/121_review_propositional_metalogic_cherry_pick/plans/01_review-propositional-metalogic.md` (this plan)
- `specs/121_review_propositional_metalogic_cherry_pick/summaries/01_review-propositional-metalogic-summary.md` (post-implementation)
- Branch `pr1/foundations-logic` with 3 clean commits containing all propositional metalogic content

## Rollback/Contingency

If the branch state becomes corrupted during file copy:
1. `git checkout pr1/foundations-logic` and `git reset --hard origin/pr1/foundations-logic` to restore the original branch state
2. All source files remain unmodified on main
3. Re-execute from Phase 2

If ProofSystem.lean selective edit causes build failures:
1. Revert ProofSystem.lean to branch version: `git checkout pr1/foundations-logic -- Cslib/Foundations/Logic/ProofSystem.lean`
2. Re-examine which specific lines are needed
3. Apply a more conservative edit
