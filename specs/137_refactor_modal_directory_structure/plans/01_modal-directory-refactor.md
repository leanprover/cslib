# Implementation Plan: Refactor Modal/ Directory Structure

- **Task**: 137 - Refactor Modal/ directory structure for the modal cube
- **Status**: [IMPLEMENTING]
- **Effort**: 6 hours
- **Dependencies**: None
- **Research Inputs**: specs/137_refactor_modal_directory_structure/reports/01_directory-structure-research.md
- **Artifacts**: plans/01_modal-directory-refactor.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

Reorganize `Cslib/Logics/Modal/` to make its architecture self-documenting while respecting the upstream/fork boundary. The monolithic `ProofSystem/Instances.lean` (1531 lines) is split into 15 per-system files. The flat `Metalogic/` directory (30 files) is reorganized into `Metalogic/Systems/{K,T,D,...}/` subdirectories. Work is divided into two PRs: PR 1 touches only fork-created files (no upstream merge conflict risk), PR 2 restores a missing upstream file. Definition of done: `lake build` passes after each phase, `lake exe mk_all --module` regenerates the barrel, and the final tree matches the proposed structure.

### Research Integration

Key findings from the research report:
- 4 upstream files (Basic, Cube, Denotation, LogicalEquivalence -- last one missing from fork), 37 fork-only files
- `ProofSystem/Instances.lean` at 1531 lines is the primary maintenance burden
- All 28 system-specific Metalogic files import `Cslib.Logics.Modal.ProofSystem.Instances`
- Import graph is strictly hierarchical (no cycles) -- safe to restructure
- `Metalogic.lean` barrel file already aggregates all imports (simplifies migration)
- External consumers: only `Bimodal/Embedding/` imports `Modal/Basic.lean` and `Modal/FromPropositional.lean` (unaffected by PR 1)

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task advances the "Logics / Modal" module organization described in the project roadmap. A cleaner directory structure supports future modal logic extensions (decidability, model theory) and maintains clean PR boundaries with upstream CSLib.

## Goals & Non-Goals

**Goals**:
- Split `ProofSystem/Instances.lean` (1531 lines) into 15 per-system files with a barrel aggregator
- Group 28 system-specific Metalogic files into `Metalogic/Systems/{System}/` directories
- Maintain backward-compatible imports via barrel files
- Pass full CI after each structural change
- Produce two separate PRs (fork-only vs upstream-touching)

**Non-Goals**:
- Refactor or reduce boilerplate within the axiom predicates (future task)
- Rename/split `Basic.lean` (too much import churn for minimal benefit)
- Change namespace structure (`Cslib.Logics.Modal` stays as-is)
- Resolve the B/KB naming inconsistency (future task)
- Extract S5-specific code from `DerivationTree.lean` (future task)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Import path changes break downstream files | H | M | Use barrel files for backward compat; run `lake build` after each move batch |
| `lake exe mk_all --module` produces unexpected ordering | L | L | Run it once and verify diff manually |
| Lean module caching confused by moves | M | L | Run `lake clean` if incremental build fails |
| Namespace collisions from `Systems/K/Soundness.lean` vs `Metalogic/Soundness.lean` | M | L | New files use same namespaces as originals (just different file paths) |
| Git history lost on file moves | L | M | Use `git mv` for trackable moves; verify with `git log --follow` |

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

### Phase 1: Split Instances.lean into Per-System Files [COMPLETED]

**Goal**: Break the 1531-line monolith into 15 focused files plus a barrel aggregator.

**Tasks**:
- [ ] Create directory `Cslib/Logics/Modal/ProofSystem/Instances/`
- [ ] Extract `KAxiom` inductive + K instance registrations into `Instances/K.lean`
- [ ] Extract `TAxiom` inductive + T instance registrations into `Instances/T.lean`
- [ ] Extract `DAxiom` inductive + D instance registrations into `Instances/D.lean`
- [ ] Extract `BAxiom` inductive + KB instance registrations into `Instances/B.lean`
- [ ] Extract `K4Axiom` inductive + K4 instances into `Instances/K4.lean`
- [ ] Extract `K5Axiom` inductive + K5 instances into `Instances/K5.lean`
- [ ] Extract `K45Axiom` inductive + K45 instances into `Instances/K45.lean`
- [ ] Extract `S4Axiom` inductive + S4 instances into `Instances/S4.lean`
- [ ] Extract `S5Axiom` (= `ModalAxiom`) + S5 instances into `Instances/S5.lean`
- [ ] Extract `TBAxiom` inductive + TB instances into `Instances/TB.lean`
- [ ] Extract `KB5Axiom` inductive + KB5 instances into `Instances/KB5.lean`
- [ ] Extract `D4Axiom` inductive + D4 instances into `Instances/D4.lean`
- [ ] Extract `D5Axiom` inductive + D5 instances into `Instances/D5.lean`
- [ ] Extract `D45Axiom` inductive + D45 instances into `Instances/D45.lean`
- [ ] Extract `DBAxiom` inductive + DB instances into `Instances/DB.lean`
- [ ] Convert original `Instances.lean` into barrel file importing all 15 sub-files
- [ ] Each sub-file imports `Cslib.Logics.Modal.Metalogic.DerivationTree` and `Cslib.Foundations.Logic.ProofSystem`
- [ ] Verify `lake build Cslib.Logics.Modal.ProofSystem.Instances` passes

**Timing**: 2 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/ProofSystem/Instances.lean` - Convert to barrel aggregator
- `Cslib/Logics/Modal/ProofSystem/Instances/K.lean` - New file
- `Cslib/Logics/Modal/ProofSystem/Instances/T.lean` - New file
- `Cslib/Logics/Modal/ProofSystem/Instances/D.lean` - New file
- `Cslib/Logics/Modal/ProofSystem/Instances/B.lean` - New file
- `Cslib/Logics/Modal/ProofSystem/Instances/K4.lean` - New file
- `Cslib/Logics/Modal/ProofSystem/Instances/K5.lean` - New file
- `Cslib/Logics/Modal/ProofSystem/Instances/K45.lean` - New file
- `Cslib/Logics/Modal/ProofSystem/Instances/S4.lean` - New file
- `Cslib/Logics/Modal/ProofSystem/Instances/S5.lean` - New file
- `Cslib/Logics/Modal/ProofSystem/Instances/TB.lean` - New file
- `Cslib/Logics/Modal/ProofSystem/Instances/KB5.lean` - New file
- `Cslib/Logics/Modal/ProofSystem/Instances/D4.lean` - New file
- `Cslib/Logics/Modal/ProofSystem/Instances/D5.lean` - New file
- `Cslib/Logics/Modal/ProofSystem/Instances/D45.lean` - New file
- `Cslib/Logics/Modal/ProofSystem/Instances/DB.lean` - New file

**Verification**:
- `lake build Cslib.Logics.Modal.ProofSystem.Instances` passes
- All 15 sub-files compile individually
- No file exceeds 200 lines

---

### Phase 2: Move Metalogic System-Specific Files into Systems/ Directories [COMPLETED]

**Goal**: Reorganize the 28 system-specific soundness/completeness files into per-system subdirectories.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/Systems/` directory
- [ ] Create subdirectories: `K/`, `T/`, `D/`, `B/`, `K4/`, `K5/`, `K45/`, `S4/`, `S5/`, `TB/`, `KB5/`, `D4/`, `D5/`, `D45/`, `DB/`
- [ ] Move `KSoundness.lean` to `Systems/K/Soundness.lean` (update module header and imports)
- [ ] Move `KCompleteness.lean` to `Systems/K/Completeness.lean`
- [ ] Move `TSoundness.lean` to `Systems/T/Soundness.lean`
- [ ] Move `TCompleteness.lean` to `Systems/T/Completeness.lean`
- [ ] Move `DSoundness.lean` to `Systems/D/Soundness.lean`
- [ ] Move `DCompleteness.lean` to `Systems/D/Completeness.lean`
- [ ] Move `BSoundness.lean` to `Systems/B/Soundness.lean`
- [ ] Move `BCompleteness.lean` to `Systems/B/Completeness.lean`
- [ ] Move `K4Soundness.lean` to `Systems/K4/Soundness.lean`
- [ ] Move `K4Completeness.lean` to `Systems/K4/Completeness.lean`
- [ ] Move `K5Soundness.lean` to `Systems/K5/Soundness.lean`
- [ ] Move `K5Completeness.lean` to `Systems/K5/Completeness.lean`
- [ ] Move `K45Soundness.lean` to `Systems/K45/Soundness.lean`
- [ ] Move `K45Completeness.lean` to `Systems/K45/Completeness.lean`
- [ ] Move `S4Soundness.lean` to `Systems/S4/Soundness.lean`
- [ ] Move `S4Completeness.lean` to `Systems/S4/Completeness.lean`
- [ ] Move `S5Soundness.lean` to `Systems/S5/Soundness.lean`
- [ ] Move `S5Completeness.lean` to `Systems/S5/Completeness.lean`
- [ ] Move `TBSoundness.lean` to `Systems/TB/Soundness.lean`
- [ ] Move `TBCompleteness.lean` to `Systems/TB/Completeness.lean`
- [ ] Move `KB5Soundness.lean` to `Systems/KB5/Soundness.lean`
- [ ] Move `KB5Completeness.lean` to `Systems/KB5/Completeness.lean`
- [ ] Move `D4Soundness.lean` to `Systems/D4/Soundness.lean`
- [ ] Move `D4Completeness.lean` to `Systems/D4/Completeness.lean`
- [ ] Move `D5Soundness.lean` to `Systems/D5/Soundness.lean`
- [ ] Move `D5Completeness.lean` to `Systems/D5/Completeness.lean`
- [ ] Move `D45Soundness.lean` to `Systems/D45/Soundness.lean`
- [ ] Move `D45Completeness.lean` to `Systems/D45/Completeness.lean`
- [ ] Move `DBSoundness.lean` to `Systems/DB/Soundness.lean`
- [ ] Move `DBCompleteness.lean` to `Systems/DB/Completeness.lean`
- [ ] Update `module` declaration in each moved file to match new path
- [ ] Update internal cross-references (e.g., `DCompleteness` imports `DSoundness` -- now `Systems.D.Soundness`)
- [ ] Verify `lake build Cslib.Logics.Modal.Metalogic.Systems.K.Soundness` passes (spot check)

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- 28 files moved from `Metalogic/` to `Metalogic/Systems/{System}/`
- Internal import paths updated in each file (e.g., `Cslib.Logics.Modal.Metalogic.KSoundness` becomes `Cslib.Logics.Modal.Metalogic.Systems.K.Soundness`)

**Verification**:
- Spot-check 3 systems with `lake build` on their module paths
- No files remain in `Metalogic/` with system-prefix names (K*, T*, B*, D*, S4*, S5*, KB5*, TB*)

---

### Phase 3: Update Barrel Files and Cross-References [COMPLETED]

**Goal**: Update `Metalogic.lean` barrel, internal cross-references between system files, and `Cslib.lean`.

**Tasks**:
- [ ] Rewrite `Metalogic.lean` barrel to import from new `Systems/` paths (30 import lines change)
- [ ] Update any system file that imports another system file (e.g., `D4Completeness` imports `DCompleteness` -- now `Systems.D.Completeness`)
- [ ] Update system-specific Instances imports: each `Systems/{X}/Soundness.lean` imports `Cslib.Logics.Modal.ProofSystem.Instances` (this path is unchanged due to Phase 1 barrel -- verify no change needed)
- [ ] Run `lake exe mk_all --module` to regenerate `Cslib.lean`
- [ ] Run `lake build` to verify full project compiles

**Timing**: 1 hour

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic.lean` - Update all system-specific import paths
- `Cslib.lean` - Regenerated by `lake exe mk_all --module`
- System files with cross-system imports (D4, D5, D45, DB completeness files import D completeness; K4, K5, K45, KB5, B completeness files import K completeness)

**Verification**:
- `lake build` passes (full project)
- `lake exe checkInitImports` passes
- `grep -r "Cslib.Logics.Modal.Metalogic.KSoundness" Cslib/` returns zero hits (old paths gone)

---

### Phase 4: CI Verification and PR 1 Preparation [NOT STARTED]

**Goal**: Run the full CSLib CI pipeline and prepare the fork-only PR.

**Tasks**:
- [ ] Run `lake build` (full project build)
- [ ] Run `lake exe checkInitImports`
- [ ] Run `lake lint`
- [ ] Run `lake exe lint-style`
- [ ] Run `lake test`
- [ ] Run `lake shake --add-public --keep-implied --keep-prefix` (import minimization check)
- [ ] Fix any lint or style issues introduced by the refactoring
- [ ] Verify no `sorry` or vacuous definitions were introduced
- [ ] Create feature branch `refactor/modal-directory-pr1`
- [ ] Commit with message: `refactor(Modal): split Instances.lean and organize Metalogic/Systems/`

**Timing**: 30 minutes

**Depends on**: 3

**Files to modify**:
- Any files flagged by linters (style fixes only)

**Verification**:
- All 6 CI commands pass without errors
- Git status shows only the intended file moves and barrel updates
- No upstream files (Basic.lean, Cube.lean, Denotation.lean) appear in the diff

---

### Phase 5: Restore LogicalEquivalence.lean from Upstream [NOT STARTED]

**Goal**: Bring back the missing upstream file `LogicalEquivalence.lean` to the fork's main branch.

**Tasks**:
- [ ] Fetch latest upstream: `git fetch upstream`
- [ ] Identify the commit/file for `LogicalEquivalence.lean` on `upstream/main`
- [ ] Cherry-pick or copy the file to `Cslib/Logics/Modal/LogicalEquivalence.lean`
- [ ] Ensure the file has `import Cslib.Init` as required
- [ ] Verify imports within the file resolve correctly
- [ ] Run `lake exe mk_all --module` to add to `Cslib.lean` barrel
- [ ] Run `lake build Cslib.Logics.Modal.LogicalEquivalence` to verify it compiles

**Timing**: 30 minutes

**Depends on**: 4

**Files to modify**:
- `Cslib/Logics/Modal/LogicalEquivalence.lean` - New file (restored from upstream)
- `Cslib.lean` - Regenerated to include new file

**Verification**:
- `lake build Cslib.Logics.Modal.LogicalEquivalence` passes
- File contents match upstream/main version
- `lake exe checkInitImports` passes

---

### Phase 6: PR 2 Preparation and Final Verification [NOT STARTED]

**Goal**: Prepare the upstream-coordination PR and run final verification.

**Tasks**:
- [ ] Create feature branch `refactor/modal-directory-pr2` (from PR 1 branch or main after PR 1 merge)
- [ ] Run full CI pipeline: `lake build`, `lake exe checkInitImports`, `lake lint`, `lake exe lint-style`, `lake test`
- [ ] Commit with message: `feat(Modal): restore LogicalEquivalence.lean from upstream`
- [ ] Verify the overall directory structure matches the target layout
- [ ] Document in PR description that this restores upstream parity

**Timing**: 30 minutes

**Depends on**: 5

**Files to modify**:
- None beyond Phase 5 artifacts (this phase is verification and git operations)

**Verification**:
- Full CI passes
- `find Cslib/Logics/Modal -name "*.lean" | wc -l` shows 42 files (41 original + 15 new Instance files - 1 original Instances.lean removed + 1 LogicalEquivalence restored = ~56 files)
- Directory tree matches proposed structure from research report

## Testing & Validation

- [ ] `lake build` passes after each phase (incremental verification)
- [ ] `lake exe checkInitImports` passes (all files import `Cslib.Init`)
- [ ] `lake lint` passes (no new linting errors introduced)
- [ ] `lake exe lint-style` passes (style conformance)
- [ ] `lake test` passes (CslibTests suite unaffected)
- [ ] `lake shake --add-public --keep-implied --keep-prefix` passes (import minimization)
- [ ] No upstream files modified in PR 1 (verified by diff inspection)
- [ ] External consumers (`Bimodal/Embedding/`) unaffected (import paths unchanged)
- [ ] Barrel imports (`Metalogic.lean`, `Instances.lean`) re-export everything for backward compat

## Artifacts & Outputs

- `specs/137_refactor_modal_directory_structure/plans/01_modal-directory-refactor.md` (this plan)
- PR 1: Feature branch `refactor/modal-directory-pr1` with Instances split + Metalogic/Systems reorganization
- PR 2: Feature branch `refactor/modal-directory-pr2` with LogicalEquivalence.lean restoration
- Updated `Cslib.lean` barrel (auto-generated)
- Updated `Metalogic.lean` barrel (manual)

## Rollback/Contingency

- **Phase 1-3 rollback**: `git checkout main -- Cslib/Logics/Modal/` restores original structure. The barrel file approach means no downstream code needs reverting.
- **Build failure during moves**: If `lake build` fails mid-phase, the barrel files still point to old paths until updated. Partially moved files can be moved back without cascading failures.
- **lake clean**: If Lean module caching causes stale errors after moves, run `lake clean && lake build` to rebuild from scratch.
- **PR rejection**: Since PR 1 is fork-only, it can be reverted without affecting upstream merge-ability. PR 2 is a single file addition, trivially revertible.
