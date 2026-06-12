# Implementation Plan: Sub-PR 2.1 Lukasiewicz Primitive Refactoring

- **Task**: 145 - Sub-PR 2.1: Lukasiewicz primitive refactoring
- **Status**: [NOT STARTED]
- **Effort**: 3 hours
- **Dependencies**: None (gateway PR for PR 2 chain)
- **Research Inputs**: specs/145_subpr_2_1_lukasiewicz_primitives/reports/01_lukasiewicz-primitives.md
- **Artifacts**: plans/01_lukasiewicz-primitives.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

Refactors Modal/Basic.lean from `{atom, not, and, diamond}` primitives to `{atom, bot, imp, box}` primitives following the Lukasiewicz convention, updates Modal/Denotation.lean to match the new constructors, and rewrites Modal/LogicalEquivalence.lean with new Context constructors. All `grind`-based proofs in axiom validity theorems are replaced with explicit term-mode proofs. The fork's main branch already contains the completed refactoring; the work is to create a clean PR branch from `upstream/main` and apply the changes, excluding the `Cslib.Foundations.Logic.Connectives` import (which belongs to Sub-PR 1.1.1, task 138).

### Worktree Isolation

All implementation work MUST use a git worktree (`isolation: "worktree"`) to avoid disrupting the `main` branch. Other agents are actively working on `main`, so no branch checkouts are permitted in the primary working tree. The implementation agent creates the `refactor/modal-lukasiewicz` branch inside the worktree, performs all edits and builds there, and pushes the branch to `origin` before the worktree is cleaned up.

### Research Integration

Research report `reports/01_lukasiewicz-primitives.md` provided:
- Complete grind inventory: 20+ proofs in Basic.lean, 3 in Denotation.lean, all in LogicalEquivalence.lean
- Import dependency analysis: 6 files import Basic.lean; only Denotation.lean and LogicalEquivalence.lean are in scope
- Connectives import exclusion: `import Cslib.Foundations.Logic.Connectives` and `ModalConnectives` instance must be excluded
- Three theory-level proofs (`TheoryEq.ext_iff`, `satisfies_theory`, `not_theoryEq_satisfies`) still use grind in the fork; research recommends replacing them for completeness
- Diff budget: ~478 lines after Connectives exclusion (within bounds)

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

Advances the PR 2 (Modal Metalogic) submission track. Task 145 is the gateway PR that establishes the Lukasiewicz convention enabling all 13 subsequent sub-PRs (tasks 146-158).

## Goals & Non-Goals

**Goals**:
- Change Proposition inductive from `{atom, not, and, diamond}` to `{atom, bot, imp, box}` constructors
- Define derived connectives (neg, top, or, and, diamond, iff) as `abbrev`s
- Rewrite `Satisfies` to match new primitive constructors
- Add explicit satisfaction theorems for derived connectives (`neg_iff`, `diamond_iff`, `and_iff`, `or_iff`)
- Replace all `grind`-based proofs with explicit term-mode proofs in axiom validity theorems
- Update Denotation.lean for new primitives with explicit proofs
- Rewrite LogicalEquivalence.lean with new Context constructors (`hole`, `impL`, `impR`, `box`)
- Create a clean PR branch from `upstream/main`
- Pass full CI pipeline

**Non-Goals**:
- Including the `Cslib.Foundations.Logic.Connectives` import or `ModalConnectives` instance (belongs to task 138)
- Modifying files outside the three target files (Basic.lean, Denotation.lean, LogicalEquivalence.lean)
- Adding `DecidableEq`/`BEq` deriving (deferred; not essential for this PR)
- Submitting the PR to upstream (separate manual step)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Connectives import leaks into PR branch | H | M | Explicitly verify no `Cslib.Foundations.Logic.Connectives` import; grep before commit |
| Cube.lean breaks due to changed Proposition structure | M | L | Run `lake build` which builds all files; theorem names are preserved |
| Three remaining grind proofs resist explicit replacement | L | L | These operate on set membership, not Proposition structure; straightforward `Set.ext_iff` replacements |
| Diff exceeds 500-line review limit | M | M | Fork already has completed refactoring; cherry-pick precisely, exclude non-essential additions |
| Term-mode proofs are subtly wrong | H | L | `lake build` catches type errors; `lake test` validates behavior |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3, 4 | 2 |
| 4 | 5 | 3, 4 |
| 5 | 6 | 5 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Worktree and Branch Setup [NOT STARTED]

**Goal**: Create a git worktree with a clean PR branch from `upstream/main` for the Lukasiewicz refactoring, without disrupting the primary `main` working tree.

**Worktree constraint**: Other agents are working on `main`. All work MUST happen in an isolated worktree. The implementation agent MUST be spawned with `isolation: "worktree"`.

**Tasks**:
- [ ] Fetch latest upstream: `git fetch upstream`
- [ ] Create branch from upstream/main inside the worktree: `git checkout -b refactor/modal-lukasiewicz upstream/main`
- [ ] Verify branch is clean and tracks upstream: `git log --oneline -3`
- [ ] Verify the three target files exist on this branch with old primitives: `grep "not\|and\|diamond" Cslib/Logics/Modal/Basic.lean | head -5`

**Timing**: 10 minutes

**Depends on**: none

**Files to modify**:
- None (branch management only)

**Verification**:
- `git branch --show-current` returns `refactor/modal-lukasiewicz`
- Basic.lean on this branch has `not`, `and`, `diamond` constructors
- Primary working tree is still on `main` (unaffected)

---

### Phase 2: Basic.lean Refactoring [COMPLETED]

**Goal**: Transform Basic.lean from `{atom, not, and, diamond}` to `{atom, bot, imp, box}` primitives with derived connectives and explicit term-mode proofs.

**Tasks**:
- [ ] Cherry-pick or manually apply the Proposition inductive changes:
  - Replace `not (phi : Proposition Atom)` with `bot`
  - Replace `and (phi1 phi2 : Proposition Atom)` with `imp (phi1 phi2 : Proposition Atom)`
  - Replace `diamond (phi : Proposition Atom)` with `box (phi : Proposition Atom)`
- [ ] Add derived connective `abbrev` definitions:
  - `neg phi := imp phi bot`
  - `top := imp bot bot`
  - `or phi1 phi2 := imp (imp phi1 bot) phi2`
  - `and phi1 phi2 := imp (imp phi1 (imp phi2 bot)) bot`
  - `diamond phi := neg (box (neg phi))`
  - `iff phi1 phi2 := and (imp phi1 phi2) (imp phi2 phi1)`
- [ ] Update scoped notation declarations to match new constructors
- [ ] Rewrite `Satisfies` to match on `{atom, bot, imp, box}`:
  - `.atom p => m.v w p`
  - `.bot => False`
  - `.imp phi1 phi2 => Satisfies m w phi1 -> Satisfies m w phi2`
  - `.box phi => forall w', m.r w w' -> Satisfies m w' phi`
- [ ] Add satisfaction theorems for derived connectives:
  - `Satisfies.neg_iff` -- negation unfolding
  - `Satisfies.diamond_iff` -- possibility as dual of box
  - `Satisfies.and_iff` -- conjunction unfolding
  - `Satisfies.or_iff` -- disjunction unfolding
- [ ] Replace all grind-based axiom validity proofs with explicit term-mode proofs:
  - `Satisfies.k` -- distribution axiom
  - `Satisfies.dual` -- box-diamond duality
  - `Satisfies.t` and `Satisfies.t_refl` -- reflexivity
  - `Satisfies.t_box_diamond` -- T schema consequence
  - `Satisfies.b` and `Satisfies.b_symm` -- symmetry
  - `Satisfies.four` and `Satisfies.four_trans` -- transitivity
  - `Satisfies.five` and `Satisfies.five_rightEuclidean` -- Euclidean
  - `Satisfies.d` and `Satisfies.d_serial` -- seriality
- [ ] Replace three remaining theory-level grind proofs:
  - `TheoryEq.ext_iff` -- replace with `Set.ext_iff` or `Iff.intro` + `Set.mem_setOf_eq`
  - `satisfies_theory` -- replace with direct set membership proof
  - `not_theoryEq_satisfies` -- replace with explicit unfold + classical reasoning
- [ ] **CRITICAL**: Exclude `import Cslib.Foundations.Logic.Connectives` line
- [ ] **CRITICAL**: Exclude `ModalConnectives` instance block
- [ ] **CRITICAL**: Exclude `instance : Bot (Proposition Atom)` if present
- [ ] Update module docstring to describe new primitives and Lukasiewicz convention
- [ ] Run `lake build Cslib.Logics.Modal.Basic` to verify compilation

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Basic.lean` -- primitive constructors, derived connectives, Satisfies, all proofs (~250 diff lines)

**Verification**:
- `lake build Cslib.Logics.Modal.Basic` succeeds with no errors
- `grep -c "grind" Cslib/Logics/Modal/Basic.lean` returns 0 for tactic-level grind (attribute annotations like `@[scoped grind]` are acceptable)
- `grep "Connectives" Cslib/Logics/Modal/Basic.lean` returns empty (no Connectives import)
- File contains `| bot` and `| imp` and `| box` constructors

---

### Phase 3: Denotation.lean Updates [COMPLETED]

**Goal**: Update Denotation.lean to match on `{atom, bot, imp, box}` constructors and replace grind proofs with explicit ones.

**Tasks**:
- [ ] Update the denotation function to match new constructors:
  - `.atom p => {w | m.v w p}` (unchanged)
  - `.bot => empty` (new)
  - `.imp phi1 phi2 => compl (denotation phi1) union (denotation phi2)` or equivalent
  - `.box phi => {w | forall w', m.r w w' -> w' in denotation phi}` (new)
- [ ] Replace `satisfies_mem_denotation` proof:
  - From `by induction ... <;> grind`
  - To explicit case-by-case with `simp only`, `constructor`, `rcases`
- [ ] Replace `neg_denotation` (renamed from `not_denotation`) proof:
  - From `by grind [...]`
  - To explicit `simp only` + `push_neg` + case split
- [ ] Replace `theoryEq_denotation_eq` proof:
  - From `by Iff.intro <;> grind [...]`
  - To explicit constructor with `satisfies_mem_denotation`
- [ ] Run `lake build Cslib.Logics.Modal.Denotation` to verify compilation

**Timing**: 30 minutes

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Modal/Denotation.lean` -- constructor matching, 3 proof replacements (~52 diff lines)

**Verification**:
- `lake build Cslib.Logics.Modal.Denotation` succeeds
- `grep -c "grind" Cslib/Logics/Modal/Denotation.lean` returns 0 for tactic-level grind

---

### Phase 4: LogicalEquivalence.lean Rewrite [COMPLETED]

**Goal**: Rewrite LogicalEquivalence.lean with new Context constructors matching `{imp, box}` primitives.

**Tasks**:
- [ ] Replace `Proposition.Context` inductive constructors:
  - From: `{hole, not, andL, andR, diamond}` (matching old primitives)
  - To: `{hole, impL, impR, box}` (matching new primitives)
- [ ] Rewrite `Context.fill` function for new constructors
- [ ] Define `LogicallyEquivalent` directly (not via typeclass)
- [ ] Prove `congruence` theorem with explicit proofs (no grind)
- [ ] Remove `import Cslib.Foundations.Logic.LogicalEquivalence` if present (no typeclass dependency)
- [ ] Remove any typeclass instantiation that references the old structure
- [ ] Verify the file is self-contained (~84 lines in fork version)
- [ ] Run `lake build Cslib.Logics.Modal.LogicalEquivalence` to verify compilation

**Timing**: 30 minutes

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Modal/LogicalEquivalence.lean` -- complete rewrite (~176 diff lines)

**Verification**:
- `lake build Cslib.Logics.Modal.LogicalEquivalence` succeeds
- `grep -c "grind" Cslib/Logics/Modal/LogicalEquivalence.lean` returns 0
- No references to `Cslib.Foundations.Logic.LogicalEquivalence` typeclass

---

### Phase 5: CI Verification [COMPLETED]

**Goal**: Run the full CI pipeline to confirm no regressions across the entire codebase.

**Tasks**:
- [ ] Run `lake build` (full project build -- catches any downstream breakage in Cube.lean, Metalogic/, etc.)
- [ ] Run `lake test` (CslibTests suite)
- [ ] Run `lake exe checkInitImports` (verify Cslib.Init imports)
- [ ] Run `lake exe lint-style` (style linting)
- [ ] Run `lake shake --add-public --keep-implied --keep-prefix` (dependency analysis)
- [ ] Verify no `sorry` in the three modified files: `grep -r "sorry" Cslib/Logics/Modal/Basic.lean Cslib/Logics/Modal/Denotation.lean Cslib/Logics/Modal/LogicalEquivalence.lean`
- [ ] Verify Connectives exclusion one final time: `grep -r "Connectives" Cslib/Logics/Modal/Basic.lean`
- [ ] Check total diff size: `git diff upstream/main --stat` -- confirm under ~500 lines

**Timing**: 20 minutes (mostly waiting for lake build)

**Depends on**: 3, 4

**Files to modify**:
- None (verification only)

**Verification**:
- All 5 CI commands exit with code 0
- No sorry in modified files
- No Connectives import
- Diff under 500 lines

---

### Phase 6: Final Review, Commit, and Push [IN PROGRESS]

**Goal**: Review the complete changeset, create the commit, push the branch to `origin`, and prepare PR metadata.

**Tasks**:
- [ ] Review `git diff upstream/main` for the three files -- ensure no extraneous changes
- [ ] Verify theorem names are preserved (especially `Satisfies.k`, `Satisfies.t` used by Cube.lean)
- [ ] Verify all `@[scoped grind]` attribute annotations are retained (these register lemmas, not proofs)
- [ ] Create commit: `task 145 phase 6: Lukasiewicz primitive refactoring`
- [ ] Push branch to origin: `git push -u origin refactor/modal-lukasiewicz` (required before worktree cleanup)
- [ ] Prepare PR description draft (title: `refactor(Modal): Lukasiewicz primitive convention for modal propositions`)

**Timing**: 10 minutes

**Depends on**: 5

**Files to modify**:
- None (review, commit, and push only)

**Verification**:
- Commit created on `refactor/modal-lukasiewicz` branch
- Branch pushed to `origin`
- All three files present in commit
- No other files modified

## Testing & Validation

- [ ] `lake build` passes (full project, no errors)
- [ ] `lake test` passes (CslibTests suite)
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] `lake shake` passes (no unused dependencies)
- [ ] Zero `sorry` in modified files
- [ ] Zero tactic-level `grind` usage in modified files (attribute annotations acceptable)
- [ ] No `Cslib.Foundations.Logic.Connectives` import
- [ ] Total diff under 500 lines against upstream/main
- [ ] Theorem names preserved for downstream consumers (Cube.lean)

## Artifacts & Outputs

- `specs/145_subpr_2_1_lukasiewicz_primitives/plans/01_lukasiewicz-primitives.md` (this plan)
- `specs/145_subpr_2_1_lukasiewicz_primitives/summaries/01_lukasiewicz-primitives-summary.md` (after implementation)
- Branch: `refactor/modal-lukasiewicz` (from upstream/main, created in worktree)
- Modified files (within worktree):
  - `Cslib/Logics/Modal/Basic.lean`
  - `Cslib/Logics/Modal/Denotation.lean`
  - `Cslib/Logics/Modal/LogicalEquivalence.lean`

**Worktree note**: All file modifications happen in the isolated worktree. The primary `main` working tree is never touched. The branch is pushed to `origin` before the worktree is cleaned up.

## Rollback/Contingency

If the refactoring causes unexpected downstream breakage:
1. The worktree is isolated -- simply delete the worktree branch: `git branch -D refactor/modal-lukasiewicz`
2. The primary `main` working tree is never modified, so no rollback is needed there
3. Re-examine the fork's diff to identify what caused the issue

If individual proofs fail to compile:
1. Check the fork's main branch for the exact proof term
2. Use `lean_goal` MCP tool to inspect proof state
3. Use `lean_multi_attempt` to test alternative proof strategies
