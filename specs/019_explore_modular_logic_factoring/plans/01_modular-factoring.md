# Implementation Plan: Modular Logic Factoring -- Task Restructuring

- **Task**: 19 - Explore modular logic factoring
- **Status**: [NOT STARTED]
- **Effort**: 4 hours
- **Dependencies**: None (this is a META task that restructures other tasks)
- **Research Inputs**: specs/019_explore_modular_logic_factoring/reports/01_factoring-synthesis.md
- **Artifacts**: plans/01_modular-factoring.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

This plan restructures the task graph for cslib's logic porting work. The research synthesis identified ~5,000 lines of BimodalLogic source code that are not inherently bimodal: ~2,900 lines are purely propositional (Combinators, Propositional theorems, ContextualProofs, BigConj, DeductionTheorem), ~1,200 lines are purely modal (S4/S5 derived theorems, GeneralizedNecessitation), and ~920 lines are purely temporal (TemporalDerived, frame condition typeclasses). Currently, tasks 2-11 direct all this content into `Bimodal/`, conflating reusable material with genuinely bimodal code. This plan revises tasks 2-11 and creates new tasks so that components live at the most general level, imports flow naturally (Foundations -> Propositional -> Modal/Temporal -> Bimodal), and no module is overloaded.

Definition of done: All tasks in TODO.md and state.json reflect the modular factoring. Each existing task (2-11) has been revised or confirmed unchanged. New tasks exist for Propositional Hilbert theorems, Modal proof system + theorems, and Temporal axioms + proof system + theorems. The dependency graph enforces the import hierarchy. Task 12 (PR coordination) has been updated to reflect the new PR structure.

### Research Integration

The research synthesis (`reports/01_factoring-synthesis.md`) provided the component classification that drives this plan:

- **Propositional extraction** (~2,900 lines): Combinators, Propositional/{Core,Connectives,Reasoning}, ContextualProofs, BigConj, DeductionTheorem -- all use only `atom`, `bot`, `imp` and can be stated with `[PropositionalHilbert S]` signatures in `Foundations/Logic/Theorems/`.
- **Modal extraction** (~1,200 lines): S4/S5 derived theorems, GeneralizedNecessitation -- use `box` but never `untl`/`snce`, target `Modal/Theorems/` with `[ModalS5Hilbert S]`.
- **Temporal extraction** (~920 lines): TemporalDerived, frame condition typeclasses -- use `untl`/`snce` but never `box`, target `Temporal/` with `[TemporalBXHilbert S]`.
- **Architectural recommendation**: Port directly to typeclasses (Option 2), not concrete-then-generalize. The typeclass infrastructure already exists in `Foundations/Logic/ProofSystem.lean`.
- **Critical gap identified**: `TemporalBXHilbert` is essentially empty -- needs ~20 temporal axiom `abbrev`s and `HasAxiom*` classes before temporal theorems can be stated.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Revise task descriptions for tasks 2-11 so each component lives at the most general level
- Create new tasks for standalone Propositional, Modal, and Temporal module development
- Establish a dependency graph where: Foundations -> Modal/Temporal -> Bimodal, with both Modal and Temporal depending on Propositional foundations
- Ensure task 12 (PR coordination) reflects the new multi-module PR structure
- Keep the total estimated effort comparable (redistributed, not inflated)

**Non-Goals**:
- Actually implementing any Lean code (this is a META task)
- Changing the existing typeclass hierarchy or formula types (those are stable from task 14)
- Restructuring tasks 15-18 (those are independent infrastructure/meta tasks)
- Modifying the Foundations/Logic/ typeclass files (Connectives, Axioms, ProofSystem)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Typeclass-generic proofs harder than expected | H | M | Research found proofs are structurally simple (MP + axiom instantiation). If a proof resists generalization, it stays in Bimodal/ and is ported concretely. |
| Too many new tasks fragments the work | M | L | Keep new tasks coarse-grained: one for Propositional theorems, one for Modal proof system + theorems, one for Temporal infrastructure. |
| Temporal axiom completion blocks multiple tasks | H | M | Make temporal axiom `abbrev` completion an explicit prerequisite phase within the Temporal task, not a hidden dependency. |
| Existing task descriptions in TODO.md are long and complex to edit | L | M | Use bulk edits with clear before/after patterns. Verify state.json and TODO.md stay synchronized. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 1, 2 |
| 4 | 4 | 2, 3 |

Phases within the same wave can execute in parallel.

### Phase 1: Design the New Task Graph [NOT STARTED]

**Goal**: Produce the complete revised task list with descriptions, dependencies, and effort estimates before making any file changes. This is the design phase that all edits flow from.

**Tasks**:
- [ ] Define new tasks to be created:
  - **Task 20: Propositional Hilbert Theorems** -- Port Combinators, Propositional/{Core,Connectives,Reasoning}, ContextualProofs, BigConj, DeductionTheorem as `[PropositionalHilbert S]` lemmas in `Cslib/Foundations/Logic/Theorems/`. ~2,900 lines. Dependencies: none (typeclass infrastructure already exists). This is Wave 1 work.
  - **Task 21: Modal Proof System and Theorems** -- (a) Create `Modal.DerivationTree` with `ModalHilbert`/`ModalS5Hilbert` instances in `Cslib/Logics/Modal/ProofSystem/`. (b) Port S4/S5 derived theorems and GeneralizedNecessitation as `[ModalS5Hilbert S]` lemmas in `Cslib/Logics/Modal/Theorems/`. (c) Add `Modal.Proposition.subst` and substitution theorem. ~1,600 lines total (400 proof system + 1,200 theorems). Dependencies: Task 20 (propositional theorems are imported by modal theorems). Also depends on Task 16 (DecidableEq for Modal.Proposition).
  - **Task 22: Temporal Infrastructure and Theorems** -- (a) Complete temporal axiom `abbrev`s (~20 definitions) and `HasAxiom*` typeclasses in `Cslib/Foundations/Logic/Axioms.lean` and `Cslib/Foundations/Logic/ProofSystem.lean`. (b) Create `Temporal.DerivationTree` with `TemporalBXHilbert` instance in `Cslib/Logics/Temporal/ProofSystem/`. (c) Port TemporalDerived (~790 lines) as `[TemporalBXHilbert S]` lemmas in `Cslib/Logics/Temporal/Theorems/`. (d) Port temporal frame condition typeclasses (~130 lines). ~1,350 lines total. Dependencies: Task 20 (propositional theorems are imported by temporal theorems).
- [ ] Define revised descriptions for existing tasks:
  - **Task 2** (Bimodal Syntax): Unchanged in scope -- Context, BigConj, Subformulas operate on `Bimodal.Formula` with all 6 constructors. Note: the *generic* BigConj and Context will also be created in Task 20 at the typeclass level; Task 2 ports the bimodal-specific versions that reference `Bimodal.Formula` constructors directly. Remove reference to standalone BigConj/Context porting since that moves to Task 20.
  - **Task 3** (Bimodal Semantics): Unchanged -- task frame semantics is inherently bimodal.
  - **Task 4** (Bimodal Proof System): Revise to depend on Tasks 20, 22 instead of just Task 2. The bimodal `Axiom` inductive and `DerivationTree` now import propositional and temporal typeclass theorems rather than defining them inline. Remove the sub-task about completing temporal axiom `abbrev`s (that moves to Task 22). Keep: concrete 42-axiom inductive, DerivationTree (7 rules), Derivable, Substitution, `BimodalTMHilbert` instance registration.
  - **Task 5** (Bimodal Derived Theorems): Revise scope dramatically. Remove: Combinators (~300 lines, moved to Task 20), Propositional/ (~1,100 lines, moved to Task 20), ContextualProofs (~500 lines, moved to Task 20), GeneralizedNecessitation (~400 lines, moved to Task 21), ModalS4/S5 (~800 lines, moved to Task 21), TemporalDerived (~790 lines, moved to Task 22). Keep: Perpetuity/ (~800 lines, inherently bimodal). Scope drops from ~7,300 lines to ~800 lines. Dependencies: Tasks 4, 21, 22 (imports modal and temporal theorems). Effort drops from Large to Small.
  - **Task 6** (Bimodal Frame Conditions + Soundness): Remove temporal frame condition extraction (~130 lines, moved to Task 22). The soundness proof is inherently bimodal (interaction axiom MF). Dependencies: Tasks 3, 4. Scope drops from ~2,500 to ~2,370 lines. Minor change.
  - **Task 7** (Bimodal MCS/Deduction): Remove DeductionTheorem extraction (~500 lines, moved to Task 20). Keep: MCS theory (~2,000 lines, uses the full bimodal proof system). Dependencies: Tasks 4, 5. Scope drops from ~2,500 to ~2,000 lines.
  - **Tasks 8, 9, 10, 11**: Unchanged in scope -- all inherently bimodal. Update dependency references to note that upstream tasks (4, 5, 7) have reduced scope but same task numbers.
- [ ] Define the revised dependency DAG:
  ```
  Wave 1: Tasks 2, 15, 16, 17, 18, 20
  Wave 2: Tasks 3, 21, 22   (3 depends on 2; 21 depends on 16, 20; 22 depends on 20)
  Wave 3: Tasks 4, 11        (4 depends on 2, 20, 22; 11 depends on 4)
  Wave 4: Tasks 5, 6          (5 depends on 4, 21, 22; 6 depends on 3, 4)
  Wave 5: Tasks 7              (depends on 4, 5)
  Wave 6: Tasks 8, 9, 10      (8 depends on 6, 7; 9 depends on 4, 7; 10 depends on 4, 5, 7)
  Task 12: Updated for new PR structure
  ```

**Timing**: 1 hour

**Depends on**: none

**Files to modify**: None (design only, documented here in the plan)

**Verification**:
- All ~5,000 extractable lines are accounted for in new tasks (20, 21, 22)
- No component appears in both an extraction task and a bimodal task
- Dependency graph has no cycles
- Every existing task (2-11) either has a clear revision or is confirmed unchanged

---

### Phase 2: Create New Tasks (20, 21, 22) [NOT STARTED]

**Goal**: Create the three new tasks in state.json and TODO.md with full descriptions, dependencies, and effort estimates.

**Tasks**:
- [ ] Create Task 20 (Propositional Hilbert Theorems) in state.json:
  - `project_number`: 20
  - `project_name`: "propositional_hilbert_theorems"
  - `status`: "not_started"
  - `task_type`: "lean4"
  - `dependencies`: [] (none -- typeclass infrastructure exists from task 14)
  - Full description covering: Combinators (I, B, C, S), Propositional/{Core,Connectives,Reasoning}, ContextualProofs, BigConj (generic), DeductionTheorem. All as `[PropositionalHilbert S]` lemmas. Target: `Cslib/Foundations/Logic/Theorems/`. ~2,900 lines.
- [ ] Create Task 21 (Modal Proof System and Theorems) in state.json:
  - `project_number`: 21
  - `project_name`: "modal_proof_system_theorems"
  - `status`: "not_started"
  - `task_type`: "lean4"
  - `dependencies`: [16, 20]
  - Description covering: (a) `Modal.DerivationTree` with `ModalHilbert`/`ModalS5Hilbert` instances, (b) S4/S5 derived theorems + GenNec as `[ModalS5Hilbert S]` lemmas, (c) substitution. Target: `Cslib/Logics/Modal/ProofSystem/` + `Cslib/Logics/Modal/Theorems/`. ~1,600 lines.
- [ ] Create Task 22 (Temporal Infrastructure and Theorems) in state.json:
  - `project_number`: 22
  - `project_name`: "temporal_infrastructure_theorems"
  - `status`: "not_started"
  - `task_type`: "lean4"
  - `dependencies`: [20]
  - Description covering: (a) temporal axiom `abbrev`s + `HasAxiom*` typeclasses, (b) `Temporal.DerivationTree` + `TemporalBXHilbert` instance, (c) TemporalDerived theorems, (d) frame condition typeclasses. Target: `Cslib/Foundations/Logic/Axioms.lean` (additions), `Cslib/Logics/Temporal/ProofSystem/`, `Cslib/Logics/Temporal/Theorems/`, `Cslib/Logics/Temporal/FrameConditions/`. ~1,350 lines.
- [ ] Update `next_project_number` to 23 in state.json
- [ ] Add all three tasks to TODO.md with proper formatting (prepend to Tasks section)
- [ ] Verify state.json and TODO.md are synchronized

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:
- `specs/state.json` -- add 3 new active_projects entries, update next_project_number
- `specs/TODO.md` -- add 3 new task entries, update Task Order section

**Verification**:
- `jq '.active_projects | length' specs/state.json` shows correct count
- Each new task has dependencies that reference only existing tasks
- TODO.md Task Order reflects new dependency waves

---

### Phase 3: Revise Existing Tasks (2-7, 12) [NOT STARTED]

**Goal**: Update task descriptions and dependencies for existing tasks to reflect the modular factoring.

**Tasks**:
- [ ] Revise Task 4 in state.json and TODO.md:
  - Update dependencies from `[2]` to `[2, 20, 22]`
  - Remove sub-task about completing temporal axiom `abbrev`s (now in Task 22)
  - Add note: imports propositional theorems from Task 20 and temporal axioms from Task 22
  - Clarify scope: concrete 42-axiom `Axiom` inductive, `DerivationTree`, `Derivable`, `Substitution`, `BimodalTMHilbert` instance
- [ ] Revise Task 5 in state.json and TODO.md:
  - Update dependencies from `[4]` to `[4, 21, 22]`
  - Revise scope: remove Combinators, Propositional/, ContextualProofs, GenNec, ModalS4/S5, TemporalDerived
  - Keep only: Perpetuity/ (~800 lines)
  - Update effort from "Large (10-14 hours)" to "Small (3-5 hours)"
  - Remove external dependency on BimodalLogic:294 (ModalS5/Perpetuity sorry elimination) -- the modal S5 theorems now live in Task 21 and Perpetuity may still need BimodalLogic:294
- [ ] Revise Task 6 in state.json and TODO.md:
  - Remove temporal frame condition extraction (~130 lines, moved to Task 22)
  - Scope drops from ~2,500 to ~2,370 lines
  - Dependencies unchanged: Tasks 3, 4
- [ ] Revise Task 7 in state.json and TODO.md:
  - Remove DeductionTheorem (~500 lines, moved to Task 20)
  - Keep: MCS theory (~2,000 lines)
  - Scope drops from ~2,500 to ~2,000 lines
  - Dependencies unchanged: Tasks 4, 5
- [ ] Revise Task 2 in state.json and TODO.md:
  - Add note clarifying that generic BigConj/Context live in Task 20; Task 2 ports the bimodal-specific versions that use all 6 formula constructors
  - Dependencies unchanged
- [ ] Revise Task 12 (PR coordination) in TODO.md:
  - Update PR structure to include new standalone module PRs:
    - PR-PL (Task 20): Propositional Hilbert theorems -- submit first wave
    - PR-Modal (Task 21): Modal proof system + theorems -- after PR-PL
    - PR-Temporal (Task 22): Temporal infrastructure -- after PR-PL
    - Existing bimodal PRs (Tasks 2-11): after standalone module PRs
  - Update dependency graph in coordination description

**Timing**: 1 hour

**Depends on**: 1, 2

**Files to modify**:
- `specs/state.json` -- update dependencies and descriptions for tasks 2, 4, 5, 6, 7
- `specs/TODO.md` -- update task entries for tasks 2, 4, 5, 6, 7, 12

**Verification**:
- No task has a circular dependency
- Total lines across all tasks accounts for the full BimodalLogic source
- Task 5 effort reflects reduced scope
- Task 12 PR ordering is consistent with new dependency graph

---

### Phase 4: Update Task Order and Verify Consistency [NOT STARTED]

**Goal**: Regenerate the Task Order section of TODO.md and perform final consistency checks.

**Tasks**:
- [ ] Regenerate the Task Order section in TODO.md from the dependency graph:
  - Wave 1: 2, 12, 15, 16, 17, 18, 20 (no dependencies or only external)
  - Wave 2: 3, 4 (depend on 2), 21 (depends on 16, 20), 22 (depends on 20)
  - Wave 3: 5 (depends on 4, 21, 22), 6 (depends on 3, 4), 11 (depends on 4)
  - Wave 4: 7 (depends on 4, 5)
  - Wave 5: 8 (depends on 6, 7), 9 (depends on 4, 7), 10 (depends on 4, 5, 7)
- [ ] Verify consistency between state.json and TODO.md:
  - All tasks present in both files
  - Dependencies match between files
  - Status markers consistent
- [ ] Verify the import hierarchy is enforced by dependencies:
  - Task 20 (Foundations/Propositional) has no logic task dependencies
  - Tasks 21 (Modal) and 22 (Temporal) depend on Task 20
  - Task 4 (Bimodal proof system) depends on Tasks 2, 20, 22
  - Task 5 (Bimodal derived theorems) depends on Tasks 4, 21, 22
  - This enforces: Foundations -> Modal/Temporal -> Bimodal
- [ ] Verify no component is claimed by two tasks (no double-counting):
  - Combinators: Task 20 only
  - Propositional/{Core,Connectives,Reasoning}: Task 20 only
  - ContextualProofs: Task 20 only
  - BigConj (generic): Task 20 only
  - DeductionTheorem: Task 20 only
  - S4/S5 derived theorems: Task 21 only
  - GeneralizedNecessitation: Task 21 only
  - TemporalDerived: Task 22 only
  - Temporal frame conditions: Task 22 only
  - Perpetuity/: Task 5 only

**Timing**: 1 hour

**Depends on**: 2, 3

**Files to modify**:
- `specs/TODO.md` -- regenerate Task Order section

**Verification**:
- `grep -c "NOT STARTED" specs/TODO.md` matches expected task count
- Dependency wave table has no cycles (topological sort succeeds)
- Every extractable component from the research synthesis maps to exactly one task

---

## Testing & Validation

- [ ] All tasks in state.json have valid `project_number`, `status`, `task_type`, and `dependencies`
- [ ] state.json `next_project_number` equals 23
- [ ] TODO.md Task Order section reflects the correct dependency waves
- [ ] No circular dependencies in the task graph
- [ ] The ~5,000 extractable lines (2,900 propositional + 1,200 modal + 920 temporal) are fully accounted for across Tasks 20, 21, 22
- [ ] No component appears in both a new task (20-22) and a revised bimodal task (2-11)
- [ ] Task 5 effort estimate reflects reduced scope (~800 lines vs ~7,300 lines)
- [ ] `lake build` still passes (no code changes, only task metadata changes)

## Artifacts & Outputs

- `specs/019_explore_modular_logic_factoring/plans/01_modular-factoring.md` (this plan)
- `specs/state.json` (updated with 3 new tasks + revised existing tasks)
- `specs/TODO.md` (updated with 3 new task entries + revised descriptions + new Task Order)

## Rollback/Contingency

All changes are to `specs/state.json` and `specs/TODO.md` only (no code changes). If the restructuring proves problematic:
1. Revert to the pre-implementation commit using `git checkout HEAD -- specs/state.json specs/TODO.md`
2. The original task descriptions from the current commit are fully recoverable via git history
3. No Lean source files are modified by this task, so `lake build` is unaffected
