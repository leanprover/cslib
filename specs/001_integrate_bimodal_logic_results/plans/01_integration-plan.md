# Implementation Plan: Task #1

- **Task**: 1 - Integrate BimodalLogic results into cslib
- **Status**: [IMPLEMENTING]
- **Effort**: 18 hours
- **Dependencies**: None
- **Research Inputs**: specs/001_integrate_bimodal_logic_results/reports/01_team-research.md
- **Artifacts**: plans/01_integration-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

This plan covers the full lifecycle of integrating the sorry-free core of the BimodalLogic library (~70 files, ~30k lines) into cslib as a series of 10 modular PRs under `Cslib/Logics/Temporal/`. The work spans two repositories: BimodalLogic (source, at `/home/benjamin/Projects/BimodalLogic/`) needs toolchain upgrade and sorry elimination tasks created there, while cslib (target, at `/home/benjamin/Projects/cslib/`) needs porting tasks created here for each PR. The plan is structured as a task creation and coordination plan -- creating the right tasks in each repo with correct numbering, dependencies, and descriptions so that subsequent `/implement` runs can execute the actual porting work.

### Research Integration

The team research report (4 teammates) provided:
- **Teammate A**: Module map, 3-tier classification (Tier 1 standalone sorry-free, Tier 2 sorry-free larger, Tier 3 has sorries)
- **Teammate B**: Complete 9-layer dependency graph, detailed 10-PR plan with file lists and line counts, version compatibility analysis
- **Teammate C**: Sorry inventory (35 active sorries in 11+ files outside Boneyard), style mismatch catalog, content exclusion list
- **Teammate D**: Strategic fit analysis, cross-connection opportunities (InferenceSystem, LTS, OmegaSequence.Temporal, Modal Cube)

Key consensus: Follow Teammate B's 10-PR plan, exclude all sorry-containing files from initial PRs, target `Cslib/Logics/Temporal/` namespace.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Create all necessary tasks in cslib (this repo) for receiving ported code -- one task per PR
- Create preparation tasks in BimodalLogic repo for toolchain upgrade and sorry elimination
- Define clear dependency ordering between tasks in both repos
- Establish the porting protocol (namespace rename, module declarations, copyright headers, linting)
- Produce a task dependency graph that enables parallel execution where possible

**Non-Goals**:
- Actually porting any Lean code in this plan (that happens during `/implement` of individual tasks)
- Resolving the ~35 active sorries in BimodalLogic's advanced metalogic modules
- Porting BimodalLogic's ML automation tooling (Automation/, dataset generators, REPL bridges)
- Porting tests, Boneyard, docs/latex/typst, or Examples
- Integrating BimodalLogic custom tactics (modal_search, apply_axiom, modal_t) -- deferred to future work
- Deciding the final namespace (Temporal vs Bimodal) -- that requires Zulip discussion with maintainers

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Lean 4.27 to 4.31 toolchain gap causes extensive breakage during porting | H | M | Create a BimodalLogic task to upgrade toolchain first; discover porting patterns on Syntax (smallest module) before scaling |
| cslib maintainers reject namespace choice or PR strategy | H | M | Open Zulip discussion early (Phase 1); propose Temporal namespace with rationale; be prepared to rename |
| Mathlib API drift between v4.27 and current cslib pin causes proof breakage | M | M | Upgrade BimodalLogic's Mathlib first; identify broken APIs before porting |
| Sorry-free classification is inaccurate (some "sorry" in comments counted vs code) | L | L | Verified: core modules (Syntax, Semantics, ProofSystem, Core, Decidability, Separation, ConservativeExtension) confirmed zero actual sorry tactic usage |
| PR review bottleneck -- 10 sequential PRs may take months | M | H | Keep PRs small and independent; submit PRs 1-3 first to establish pattern; later PRs can overlap in review |
| BimodalLogic repo has 71 active tasks and next_project_number=291 -- creating tasks there may conflict with active work | L | L | Use BimodalLogic's own task system; numbers 291+ are available |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 2, 3 |
| 4 | 5 | 4 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Create BimodalLogic Preparation Tasks [COMPLETED]

**Goal**: Create tasks in the BimodalLogic repo (`/home/benjamin/Projects/BimodalLogic/`) for toolchain upgrade and source preparation before any porting can begin.

**Tasks**:
- [x] Create task 291 in BimodalLogic: "Upgrade Lean toolchain from v4.27 to v4.31 and update Mathlib" -- this is the critical prerequisite; all porting work depends on BimodalLogic building on the same toolchain as cslib *(completed)*
- [x] Create task 292 in BimodalLogic: "Add copyright headers (Apache 2.0) to all source files under Theories/Bimodal/" -- cslib requires headers on all files; ~160 files need headers added *(completed)*
- [x] Create task 293 in BimodalLogic: "Audit and fix Mathlib linter compliance across sorry-free modules" -- run Mathlib-style linters, fix naming conventions, add missing docstrings *(completed)*
- [x] Create task 294 in BimodalLogic: "Eliminate sorry in Theorems/ModalS5.lean and Theorems/Perpetuity/Principles.lean" -- these files are needed for PR 4 (Derived Theorems) but have 1-3 sorry each; small enough to resolve *(completed)*
- [x] Update BimodalLogic specs/state.json with new tasks (project numbers 291-294) *(completed)*
- [x] Update BimodalLogic specs/TODO.md with new task entries *(completed)*
- [x] Set dependencies: 292, 293, 294 all depend on 291 (toolchain must upgrade first) *(completed)*

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `/home/benjamin/Projects/BimodalLogic/specs/state.json` - Add 4 new task entries
- `/home/benjamin/Projects/BimodalLogic/specs/TODO.md` - Add 4 new task descriptions

**Verification**:
- BimodalLogic state.json has next_project_number=295
- BimodalLogic TODO.md lists tasks 291-294 with correct descriptions, dependencies, and [NOT STARTED] status
- Task types set to `lean4`

---

### Phase 2: Create cslib Porting Tasks (PRs 1-5) [COMPLETED]

**Goal**: Create tasks in cslib (this repo) for the first 5 PRs, covering Syntax, Semantics, ProofSystem, Derived Theorems, and Frame Conditions + Soundness. These are the foundational PRs.

**Tasks**:
- [x] Create task 2 in cslib: "Port Temporal Syntax (PR 1): Atom, Formula, Context, BigConj, Subformulas" -- ~2,500 lines, 5 files, Mathlib-only dependencies, target `Cslib/Logics/Temporal/Syntax/` *(completed)*
- [x] Create task 3 in cslib: "Port Task Frame Semantics (PR 2): TaskFrame, WorldHistory, TaskModel, Truth, Validity" -- ~2,200 lines, 5 files, depends on task 2, target `Cslib/Logics/Temporal/Semantics/` *(completed)*
- [x] Create task 4 in cslib: "Port Proof System (PR 3): Axioms, Derivation, Derivable, Substitution, LinearityDerivedFacts" -- ~2,000 lines, 5 files, depends on task 2, target `Cslib/Logics/Temporal/ProofSystem/` *(completed)*
- [x] Create task 5 in cslib: "Port Derived Theorems (PR 4): Combinators, Propositional/*, ContextualProofs, GeneralizedNecessitation" -- ~3,000 lines, 6+ files, depends on task 4, target `Cslib/Logics/Temporal/Theorems/` *(completed)*
- [x] Create task 6 in cslib: "Port Frame Conditions and Soundness (PR 5): FrameClass, Validity, Soundness, SoundnessLemmas, DenseSoundness, DiscreteSoundness" -- ~3,500 lines, 10+ files, depends on tasks 3 and 4, target `Cslib/Logics/Temporal/FrameConditions/` and `Cslib/Logics/Temporal/Metalogic/Soundness/` *(completed)*
- [x] Update cslib specs/state.json with tasks 2-6 *(completed)*
- [x] Update cslib specs/TODO.md with task descriptions including dependency information *(completed)*
- [x] Each task description should include: source files list, target path, line count estimate, PR title, porting checklist (namespace rename, module declarations, import Cslib.Init, copyright headers, lake shake, linter compliance) *(completed)*

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- `specs/state.json` - Add tasks 2-6, set next_project_number=7
- `specs/TODO.md` - Add 5 new task entries with full descriptions

**Verification**:
- cslib state.json has 6 active projects (1 existing + 5 new)
- Each new task has correct dependency references
- Task descriptions include porting protocol checklist
- All tasks marked [NOT STARTED] with task_type=lean4

---

### Phase 3: Create cslib Porting Tasks (PRs 6-10) [COMPLETED]

**Goal**: Create tasks in cslib for the remaining 5 PRs, covering MCS/Deduction, Completeness, Decidability, Separation, and Conservative Extension.

**Tasks**:
- [x] Create task 7 in cslib: "Port Deduction Infrastructure and MCS Theory (PR 6): DeductionTheorem, MaximalConsistent, MCSProperties, RestrictedMCS" -- ~2,500 lines, 6 files, depends on tasks 4 and 5, target `Cslib/Logics/Temporal/Metalogic/Core/` *(completed)*
- [x] Create task 8 in cslib: "Port Strong Completeness (PR 7): Completeness.lean" -- ~520 lines, 1 file, depends on tasks 6 and 7, target `Cslib/Logics/Temporal/Metalogic/` *(completed)*
- [x] Create task 9 in cslib: "Port Decidability and Tableau (PR 8): SignedFormula, Tableau, Closure, Saturation, ProofExtraction, Correctness, DecisionProcedure, CountermodelExtraction, FMP/*" -- ~10,000 lines, 18+ files, depends on tasks 4 and 7, target `Cslib/Logics/Temporal/Metalogic/Decidability/` *(completed)*
- [x] Create task 10 in cslib: "Port Separation Theorem (PR 9): WeakCanonical/Separation/* (16 files)" -- ~3,500 lines, 16 files, depends on tasks 4, 5, and 7, target `Cslib/Logics/Temporal/Metalogic/Separation/` *(completed)*
- [x] Create task 11 in cslib: "Port Conservative Extension (PR 10): ExtFormula, ExtDerivation, Substitution, Lifting" -- ~1,500 lines, 4 files, depends on task 4, target `Cslib/Logics/Temporal/Metalogic/ConservativeExtension/` *(completed)*
- [x] Update cslib specs/state.json with tasks 7-11 *(completed)*
- [x] Update cslib specs/TODO.md with task descriptions *(completed)*

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- `specs/state.json` - Add tasks 7-11, set next_project_number=12
- `specs/TODO.md` - Add 5 new task entries with full descriptions

**Verification**:
- cslib state.json has 11 active projects total
- Dependency graph is consistent: task 8 depends on 6+7, task 9 depends on 4+7, etc.
- Task 9 (Decidability) is the largest at ~10k lines -- may benefit from splitting during planning

---

### Phase 4: Create Coordination and PR Submission Task [COMPLETED]

**Goal**: Create a coordination task in cslib that tracks the overall PR submission process, maintainer communication, and cross-repo dependency management.

**Tasks**:
- [x] Create task 12 in cslib: "Coordinate cslib PR submission for Temporal Logic integration" -- tracks: Zulip discussion with maintainers, namespace decision, PR submission order, review cycles, CI compliance *(completed)*
- [x] Task 12 description should include: (a) Open Zulip thread proposing Temporal Logic integration, (b) confirm namespace choice (Cslib.Logics.Temporal vs alternatives), (c) submit PRs in dependency order starting with PR 1 (Syntax), (d) address reviewer feedback per PR, (e) run CI checks (lake build, lake shake, linting) before each submission *(completed)*
- [x] Create task 13 in cslib: "Proof-of-concept port of Syntax module to validate porting approach" -- this is the derisking task: actually port the 5 Syntax files before creating the full PR, to discover porting patterns and estimate per-file effort *(completed)*
- [x] Task 13 depends on BimodalLogic task 291 (toolchain upgrade) and should be done before implementing tasks 2-11 *(completed)*
- [x] Update cslib specs/state.json with tasks 12-13 *(completed)*
- [x] Update cslib specs/TODO.md *(completed)*

**Timing**: 1.5 hours

**Depends on**: 2, 3

**Files to modify**:
- `specs/state.json` - Add tasks 12-13, set next_project_number=14
- `specs/TODO.md` - Add 2 new task entries

**Verification**:
- Task 12 captures the full coordination workflow
- Task 13 is positioned as an early derisking step
- All dependency relationships are documented

---

### Phase 5: Validate Task Graph and Write Cross-Repo Dependency Map [COMPLETED]

**Goal**: Verify consistency of all created tasks across both repos, produce a dependency visualization, and ensure the task graph is sound.

**Tasks**:
- [x] Read back all created tasks from cslib state.json and TODO.md -- verify 13 tasks total (1 existing + 12 new) *(completed: 13 tasks confirmed, next_project_number=14)*
- [x] Read back all created tasks from BimodalLogic state.json and TODO.md -- verify 4 new tasks (291-294) *(completed: tasks 291-294 confirmed, next_project_number=295)*
- [x] Verify cross-repo dependencies are documented in task descriptions: cslib tasks 2-11 all depend on BimodalLogic task 291 (toolchain upgrade); cslib task 5 (PR 4 Theorems) depends on BimodalLogic task 294 (sorry elimination in ModalS5/Perpetuity) *(completed)*
- [x] Verify intra-cslib dependency graph matches the PR dependency ordering from the research:
  - Task 2 (Syntax): no cslib dependencies *(verified)*
  - Task 3 (Semantics): depends on 2 *(verified)*
  - Task 4 (ProofSystem): depends on 2 *(verified)*
  - Task 5 (Theorems): depends on 4 *(verified)*
  - Task 6 (FrameConditions+Soundness): depends on 3, 4 *(verified)*
  - Task 7 (MCS/Deduction): depends on 4, 5 *(verified)*
  - Task 8 (Completeness): depends on 6, 7 *(verified)*
  - Task 9 (Decidability): depends on 4, 7 *(verified)*
  - Task 10 (Separation): depends on 4, 5, 7 *(verified)*
  - Task 11 (ConservativeExtension): depends on 4 *(verified)*
  - Task 12 (Coordination): no hard dependencies (ongoing) *(verified)*
  - Task 13 (Proof-of-concept): depends on BimodalLogic 291 *(verified)*
- [x] Add a summary comment to task 1's TODO.md entry listing all child tasks created *(completed)*

**Timing**: 1 hour

**Depends on**: 4

**Files to modify**:
- `specs/TODO.md` - Add dependency summary to task 1 entry
- `specs/state.json` - Final consistency check, no expected changes

**Verification**:
- No orphan tasks (every dependency target exists)
- No circular dependencies
- BimodalLogic tasks use correct numbering (291+)
- cslib tasks use correct numbering (2+)
- Task 1 updated with cross-references to all created subtasks

---

## Testing & Validation

- [ ] cslib `specs/state.json` parses as valid JSON with `jq .` 
- [ ] cslib `specs/TODO.md` has entries for tasks 1-13
- [ ] BimodalLogic `specs/state.json` parses as valid JSON with `jq .`
- [ ] BimodalLogic `specs/TODO.md` has entries for tasks 291-294
- [ ] No task number collisions in either repo
- [ ] Dependency graph has no cycles (verify by topological sort)
- [ ] Each cslib porting task description includes: source file list, target path, estimated line count, PR title, porting checklist

## Artifacts & Outputs

- `specs/001_integrate_bimodal_logic_results/plans/01_integration-plan.md` (this file)
- `specs/state.json` (updated with tasks 2-13)
- `specs/TODO.md` (updated with tasks 2-13)
- `/home/benjamin/Projects/BimodalLogic/specs/state.json` (updated with tasks 291-294)
- `/home/benjamin/Projects/BimodalLogic/specs/TODO.md` (updated with tasks 291-294)

## Rollback/Contingency

- **If BimodalLogic toolchain upgrade fails**: The porting tasks in cslib remain valid but blocked; investigate specific Lean 4.27-to-4.31 migration issues and potentially create intermediate upgrade steps (4.27 -> 4.28 -> ... -> 4.31)
- **If namespace is rejected**: Rename is mechanical -- sed-based replacement across all porting task descriptions; the PR content itself is not yet written
- **If PRs are too large for review**: Split task 9 (Decidability, ~10k lines) into two sub-tasks: 9a (Tableau/DecisionProcedure) and 9b (FMP)
- **Rollback of task creation**: `git revert` the commit that created the tasks; state.json and TODO.md are version-controlled
