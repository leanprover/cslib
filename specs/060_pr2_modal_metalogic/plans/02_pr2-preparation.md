# Implementation Plan: PR2 Modal Metalogic Preparation and Submission

- **Task**: 60 - pr2_modal_metalogic
- **Status**: [NOT STARTED]
- **Effort**: 2 hours
- **Dependencies**: PR1 branch (pr1/foundations-logic) must exist and be up-to-date
- **Research Inputs**: reports/02_pr2-preparation.md
- **Artifacts**: plans/02_pr2-preparation.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

Prepare and submit PR2 which adds soundness and completeness theorems for all 15 normal modal logics in the modal cube (K, T, D, B, K4, K5, K45, S4, S5, D4, D5, D45, DB, TB, KB5). The PR introduces 38 new files (~6,772 lines), modifies 2 existing Modal files (Basic.lean, Denotation.lean for Lukasiewicz primitive refactoring), updates ProofSystem.lean (+115 lines, 13 new typeclasses), and deletes LogicalEquivalence.lean. The branch strategy is to create `pr2/modal-metalogic` from `pr1/foundations-logic` HEAD and selectively checkout files from main. All code already exists on main and is sorry-free; this task is purely branch management and PR submission.

### Research Integration

Research report `reports/02_pr2-preparation.md` provided complete file manifest (43 files), dependency analysis, branch strategy with `git checkout main -- <file>` approach, CI readiness verification (zero sorry, zero debug artifacts, all copyright headers present), docstring audit (3 stale BimodalLogic path references), and a draft PR description.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This plan advances the following roadmap items:
- "Modal metalogic: DeductionTheorem, MCS, Soundness, Completeness" in `Logics/Modal/Metalogic/` (already listed as completed in ROADMAP.md, this PR packages the work for upstream submission)

## Goals & Non-Goals

**Goals**:
- Create a clean `pr2/modal-metalogic` branch from PR1 HEAD with exactly the PR2-scope files
- Pass all CI checks: `lake build --wfail --iofail`, `mk_all --check`, `checkInitImports`, lint-style
- Submit PR with comprehensive description targeting `pr1/foundations-logic`

**Non-Goals**:
- Writing new Lean proofs (all proofs already exist on main)
- Including Temporal or Bimodal files in PR2
- Including HasFresh.lean or other unrelated changes
- Modifying Foundation files beyond ProofSystem.lean

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| PR1 branch has diverged or been force-pushed | H | L | Verify PR1 HEAD matches expected commit before branching |
| Basic.lean/Denotation.lean checkout introduces conflicts with PR1 versions | H | L | Research confirmed `git checkout main --` is safe; verify diff after checkout |
| Cslib.lean import list is incomplete or includes excluded files | M | M | Cross-reference against research file manifest; run `mk_all --check` |
| Build fails due to missing Foundation dependencies | H | L | Foundation dependencies are identical between PR1 and main per research |
| Stale BimodalLogic docstring references cause lint failure | L | M | Fix in cleanup phase before PR submission |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |
| 6 | 6 | 5 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Create PR2 Branch [NOT STARTED]

**Goal**: Create the `pr2/modal-metalogic` branch from the HEAD of `pr1/foundations-logic`.

**Tasks**:
- [ ] Verify `pr1/foundations-logic` branch exists and identify its HEAD commit
- [ ] Create `pr2/modal-metalogic` branch from `pr1/foundations-logic` HEAD
- [ ] Verify the new branch is correctly based on PR1

**Timing**: 5 minutes

**Depends on**: none

**Files to modify**:
- (no files modified, branch creation only)

**Verification**:
- `git log --oneline -1 pr2/modal-metalogic` matches `git log --oneline -1 pr1/foundations-logic`
- `git branch --contains pr1/foundations-logic | grep pr2/modal-metalogic`

---

### Phase 2: File Operations [NOT STARTED]

**Goal**: Delete incompatible files and checkout all PR2-scope files from main onto the PR2 branch.

**Tasks**:
- [ ] Switch to `pr2/modal-metalogic` branch
- [ ] Delete `Cslib/Logics/Modal/LogicalEquivalence.lean` (uses old primitives, incompatible with Lukasiewicz refactoring)
- [ ] Checkout modified files from main: `Basic.lean`, `Denotation.lean` (Lukasiewicz primitive refactoring)
- [ ] Checkout modified Foundation file from main: `Cslib/Foundations/Logic/ProofSystem.lean` (+13 typeclasses, +14 tag types)
- [ ] Checkout all new Modal metalogic files from main: `Cslib/Logics/Modal/Metalogic/` directory (35 files)
- [ ] Checkout `Cslib/Logics/Modal/ProofSystem/Instances.lean` from main
- [ ] Checkout `Cslib/Logics/Modal/FromPropositional.lean` from main
- [ ] Checkout `Cslib/Logics/Modal/Metalogic.lean` barrel file from main
- [ ] Verify file count: expect 38 new files, 3 modified files (Basic, Denotation, ProofSystem), 1 deleted

**Timing**: 15 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/LogicalEquivalence.lean` - DELETE
- `Cslib/Logics/Modal/Basic.lean` - checkout from main (Lukasiewicz primitives)
- `Cslib/Logics/Modal/Denotation.lean` - checkout from main (updated for new primitives)
- `Cslib/Foundations/Logic/ProofSystem.lean` - checkout from main (+115 lines)
- `Cslib/Logics/Modal/Metalogic/` - checkout entire directory from main (35 files)
- `Cslib/Logics/Modal/ProofSystem/Instances.lean` - checkout from main
- `Cslib/Logics/Modal/FromPropositional.lean` - checkout from main
- `Cslib/Logics/Modal/Metalogic.lean` - checkout from main

**Verification**:
- `git status` shows expected additions, modifications, and deletion
- `ls Cslib/Logics/Modal/Metalogic/ | wc -l` shows expected file count
- `git diff --stat pr1/foundations-logic` shows correct scope
- No Temporal or Bimodal files are included

---

### Phase 3: Update Cslib.lean Imports [NOT STARTED]

**Goal**: Update the root `Cslib.lean` file to add all 41 Modal metalogic imports and remove the LogicalEquivalence import.

**Tasks**:
- [ ] Remove `public import Cslib.Logics.Modal.LogicalEquivalence` line from Cslib.lean
- [ ] Add 41 Modal metalogic imports (Metalogic barrel, all Metalogic/* files, ProofSystem/Instances, FromPropositional) -- extract exact list from main's Cslib.lean, excluding Bimodal and Temporal imports
- [ ] Verify no Temporal or Bimodal imports were accidentally included
- [ ] Commit all changes from Phases 2-3 as a single logical commit

**Timing**: 15 minutes

**Depends on**: 2

**Files to modify**:
- `Cslib.lean` - remove LogicalEquivalence import, add 41 Modal metalogic imports

**Verification**:
- `grep -c 'Modal' Cslib.lean` reflects expected import count
- `grep 'Temporal\|Bimodal' Cslib.lean` returns no hits (unless pre-existing unrelated imports)
- `grep 'LogicalEquivalence' Cslib.lean` returns no hits

---

### Phase 4: Build Verification [NOT STARTED]

**Goal**: Verify the PR2 branch builds successfully with zero warnings and all CI checks pass.

**Tasks**:
- [ ] Run `lake build Cslib.Logics.Modal.Metalogic` to build all metalogic files
- [ ] Run `lake build Cslib.Logics.Modal.FromPropositional` to verify PL embedding
- [ ] Run `lake build --wfail --iofail` for full project build with warnings-as-errors
- [ ] Run `lake exe mk_all --check --module` to verify Cslib.lean completeness
- [ ] Run `lake exe checkInitImports` for import hygiene

**Timing**: 30 minutes (dominated by build time)

**Depends on**: 3

**Files to modify**:
- (no files modified, verification only; fix any issues discovered)

**Verification**:
- All five commands exit with code 0
- No sorry instances: `grep -rn 'sorry' Cslib/Logics/Modal/ --include="*.lean"` returns empty
- No debug artifacts: `grep -rn '#check\|#eval\|dbg_trace' Cslib/Logics/Modal/ --include="*.lean"` returns empty

---

### Phase 5: Cosmetic Cleanup and Pre-Submission Checks [NOT STARTED]

**Goal**: Fix minor cosmetic issues identified in research and run final lint checks.

**Tasks**:
- [ ] Add module docstring to `Metalogic.lean` barrel file if linter requires it (check if existing docstring position satisfies lint-style-action)
- [ ] Fix 3 stale BimodalLogic path references in docstrings:
  - `Metalogic/DerivationTree.lean:40` -- update `BimodalLogic/Theories/Bimodal/ProofSystem/Derivation.lean` reference
  - `Metalogic/DeductionTheorem.lean:33` -- update `BimodalLogic/Theories/Bimodal/Metalogic/Core/DeductionTheorem.lean` reference
  - `Metalogic/MCS.lean:33` -- update `BimodalLogic/Theories/Bimodal/Metalogic/Core/MCSProperties.lean` reference
- [ ] Verify all 41 Modal .lean files have copyright headers: `head -1 <file>` starts with `/-`
- [ ] Run lint-style checks if available (`scripts/lint-style.sh` or equivalent)
- [ ] Commit cleanup changes if any modifications were made

**Timing**: 15 minutes

**Depends on**: 4

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic.lean` - possible docstring addition
- `Cslib/Logics/Modal/Metalogic/DerivationTree.lean` - fix stale reference
- `Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean` - fix stale reference
- `Cslib/Logics/Modal/Metalogic/MCS.lean` - fix stale reference

**Verification**:
- `grep -rn 'BimodalLogic' Cslib/Logics/Modal/ --include="*.lean"` returns no hits
- Lint checks pass
- Build still passes after cleanup changes

---

### Phase 6: Push and Create PR [NOT STARTED]

**Goal**: Push the PR2 branch to origin and create the pull request with the draft description from research.

**Tasks**:
- [ ] Push `pr2/modal-metalogic` branch to origin
- [ ] Create PR targeting `pr1/foundations-logic` using `gh pr create` with the draft title and body from research report Section 7:
  - Title: `feat(Logics/Modal): soundness and completeness for all 15 modal cube systems`
  - Body: Full description including summary, mathematical contributions, systems covered, design decisions, stats, file list, and test plan
- [ ] Verify PR was created successfully and link is accessible
- [ ] Record PR URL

**Timing**: 10 minutes

**Depends on**: 5

**Files to modify**:
- (no files modified, git operations only)

**Verification**:
- `gh pr view --json url` returns valid PR URL
- PR targets correct base branch (`pr1/foundations-logic`)
- PR description matches the draft from research

## Testing & Validation

- [ ] `lake build --wfail --iofail` passes with zero warnings
- [ ] `lake exe mk_all --check --module` passes (Cslib.lean is complete)
- [ ] `lake exe checkInitImports` passes (import hygiene)
- [ ] `grep -rn 'sorry' Cslib/Logics/Modal/ --include="*.lean"` returns empty
- [ ] `grep -rn '#check\|#eval\|dbg_trace' Cslib/Logics/Modal/ --include="*.lean"` returns empty
- [ ] `git diff --stat pr1/foundations-logic` shows only PR2-scope files (no Temporal/Bimodal)
- [ ] lint-style checks pass
- [ ] PR is created and accessible

## Artifacts & Outputs

- `specs/060_pr2_modal_metalogic/plans/02_pr2-preparation.md` (this plan)
- `pr2/modal-metalogic` branch (git branch)
- GitHub PR targeting `pr1/foundations-logic`

## Rollback/Contingency

If the branch is in a broken state:
1. Delete the local and remote branch: `git branch -D pr2/modal-metalogic && git push origin --delete pr2/modal-metalogic`
2. Re-create from PR1 HEAD and repeat the file operations
3. If PR1 branch itself has issues, coordinate with PR1 review before proceeding

If build fails after file checkout:
1. Compare Foundation files between PR1 and main to identify divergence
2. Check whether additional Foundation changes are needed
3. If incompatible, escalate -- may need to rebase PR1 onto main first
