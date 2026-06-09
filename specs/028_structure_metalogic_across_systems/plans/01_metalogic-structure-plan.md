# Implementation Plan: Structure Metalogic Across Systems

- **Task**: 28 - Structure metalogic across Propositional, Modal, Temporal, and Bimodal systems
- **Status**: [NOT STARTED]
- **Effort**: 2 hours
- **Dependencies**: None (meta/planning task; does not depend on implementation tasks)
- **Research Inputs**: specs/028_structure_metalogic_across_systems/reports/01_team-research.md
- **Artifacts**: plans/01_metalogic-structure-plan.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: formal
- **Lean Intent**: false

## Overview

This task structures the metalogic layer across CSLib's four logic systems (Propositional, Modal, Temporal, Bimodal) by creating new tasks and setting correct inter-task dependencies. Team research (4 teammates, HIGH confidence) established that the deduction theorem is per-logic, MCS theory is ~60% generic (definitions shareable, proofs per-logic), and soundness/completeness are 100% per-semantics. The implementation creates 3-4 new tasks to fill identified gaps: generic MCS foundations in `Foundations/Logic/Metalogic/`, standalone modal metalogic, standalone temporal metalogic, and a BimodalTMHilbert compatibility instance. The task is done when state.json and TODO.md contain all new tasks with correct dependencies and the ROADMAP.md reflects the expanded metalogic structure.

### Research Integration

Key findings integrated from the team research report (01_team-research.md):

1. **Deduction theorem is per-logic**: Structural induction on concrete DerivationTree inductives means no generic abstraction. Each logic (modal ~5 constructors, temporal ~6, bimodal 7) needs its own deduction theorem.

2. **MCS theory ~60% generic**: Definitions (Consistent, SetMaximalConsistent, Lindenbaum skeleton) can live in `Foundations/Logic/Metalogic/`. But negation_complete and witness conditions depend on the per-logic deduction theorem.

3. **Soundness/completeness 100% per-semantics**: Modal=Kripke, Temporal=LinearOrder, Bimodal=TaskFrame. No shared infrastructure possible.

4. **Existing tasks 3-11 correctly scoped**: No revisions needed for bimodal porting tasks.

5. **Gaps identified**: No tasks for generic MCS foundations, standalone modal metalogic (deduction theorem + MCS + soundness + completeness over Kripke), standalone temporal metalogic (same over linear orders), or BimodalTMHilbert-to-TemporalBXHilbert compatibility instance.

6. **Validated pattern**: FormalizedFormalLogic/Foundation uses the same "share definitions, not proofs" approach CSLib should follow.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This plan advances the following ROADMAP.md items:
- Temporal soundness theorem: `TemporalBXHilbert S -> S |- phi -> Temporal.Valid phi` (new temporal metalogic task enables this)
- All standalone modules self-contained: Modal/ and Temporal/ import only Foundations (modal/temporal metalogic tasks reinforce this)
- The expanded metalogic structure adds Phase 5 (Standalone Metalogic) to the roadmap between the current Phase 3 (Temporal Semantics) and Phase 4 (Bimodal Porting)

## Goals & Non-Goals

**Goals**:
- Confirm existing tasks 3-11 and 20-23 need no revision
- Create new tasks for identified metalogic gaps with correct numbering and dependencies
- Update state.json and TODO.md atomically with the new tasks
- Update ROADMAP.md to reflect the new metalogic layer structure
- Ensure the import hierarchy is correct: Foundations -> Modal/Temporal -> Bimodal (no cross-imports between Modal and Temporal metalogic)

**Non-Goals**:
- Writing any Lean code (this task produces task management artifacts only)
- Revising existing task descriptions (research confirmed they are correctly scoped)
- Creating tasks for embedding-based metalogic transfer theorems (future work, post tasks 10-11)
- Over-abstracting metalogic with typeclasses like `HasDeductionTheorem` (research explicitly discourages this)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Dependency graph becomes too complex with new tasks | M | L | Keep new tasks at the right granularity; use wave analysis to verify parallelism |
| Modal/temporal metalogic scope uncertainty (full standalone vs lighter-weight) | H | M | Phase 1 includes user consultation via AskUserQuestion before creating tasks |
| New task numbers conflict with future task creation | L | L | Use next_project_number from state.json; increment atomically |
| BimodalTMHilbert compatibility instance too small for standalone task | L | M | Fold into task 22 description update if user prefers; otherwise create standalone |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases are fully sequential because each depends on the prior phase's output.

---

### Phase 1: Audit Existing Tasks and Consult User on Scope [NOT STARTED]

**Goal**: Confirm that existing tasks 3-11 and 20-23 need no revision, and determine user preference for modal/temporal metalogic scope.

**Tasks**:
- [ ] Read each existing task description (3-11, 20-23) in TODO.md and verify alignment with research findings
- [ ] Confirm task 7 (bimodal deduction theorem + MCS) scope is unchanged (research finding #1 validates this)
- [ ] Confirm task 22 description already includes BimodalTMHilbert compatibility instance (research found it in task 22 description item (e))
- [ ] Ask user (via AskUserQuestion) whether they want: (A) full standalone metalogic for Modal and Temporal (deduction theorem + MCS + soundness + completeness, ~1,500 lines each, new development), or (B) lighter-weight modal/temporal metalogic (deduction theorem + MCS only, soundness/completeness deferred to future tasks)
- [ ] Record user decision for Phase 2

**Timing**: 30 minutes

**Depends on**: none

**Files to modify**:
- None (audit phase, read-only)

**Verification**:
- User has responded to scope question
- Audit confirms no existing task revisions needed

---

### Phase 2: Design New Tasks with Dependencies [NOT STARTED]

**Goal**: Define the exact new tasks, their descriptions, dependencies, effort estimates, and numbering based on user scope decision from Phase 1.

**Tasks**:
- [ ] Assign task numbers using next_project_number from state.json (currently 29, so new tasks will be 29, 30, 31, ...)
- [ ] Design Task 29: Generic MCS Foundations
  - Scope: `Cslib/Foundations/Logic/Metalogic/Consistency.lean` (~200-300 lines)
  - Content: SetConsistent, SetMaximalConsistent definitions, Lindenbaum skeleton (Zorn-based), consistent_chain_union, closed_under_derivation, implication_property
  - Dependencies: None (builds on existing Foundations infrastructure)
  - Task type: lean4
  - Effort: Small (2-4 hours)
- [ ] Design Task 30: Modal Metalogic (scope per user decision)
  - Full scope: DeductionTheorem, MCS (importing generic from 29), Soundness over Kripke, Completeness via canonical Kripke model (~1,500 lines)
  - Light scope: DeductionTheorem, MCS only (~500-700 lines)
  - Dependencies: Task 21 (modal proof system), Task 29 (generic MCS foundations)
  - Task type: lean4
  - Effort: Large (full) or Medium (light)
- [ ] Design Task 31: Temporal Metalogic (scope per user decision)
  - Full scope: DeductionTheorem, MCS (importing generic from 29), Soundness over LinearOrder, Completeness (~1,500 lines)
  - Light scope: DeductionTheorem, MCS only (~500-700 lines)
  - Dependencies: Tasks 22+23 (temporal proof system + semantics), Task 29 (generic MCS foundations)
  - Task type: lean4
  - Effort: Large (full) or Medium (light)
- [ ] Verify BimodalTMHilbert compatibility instance is already scoped in task 22 (item (e) in description: "BimodalTMHilbert compatibility instance (diamond-avoidance pattern)") -- if so, no new task needed for this gap
- [ ] Map new tasks into the dependency wave structure:
  - Task 29 goes into Wave 1 (no dependencies beyond existing Foundations)
  - Task 30 goes after Task 21 + 29 (Wave 2-3 depending on 21's wave)
  - Task 31 goes after Tasks 22+23+29 (Wave 3-4 depending on 22/23 waves)
  - Bimodal task 7 (MCS) should add dependency on Task 29 (imports generic definitions)
- [ ] Determine whether task 7 needs a dependency update to include Task 29

**Timing**: 30 minutes

**Depends on**: 1

**Files to modify**:
- None (design phase, planning only)

**Verification**:
- All new tasks have complete descriptions, dependencies, effort estimates
- Dependency graph is acyclic and consistent
- Wave analysis confirms no circular dependencies

---

### Phase 3: Create Tasks in state.json and TODO.md [NOT STARTED]

**Goal**: Atomically create the new tasks in state.json and TODO.md, updating next_project_number and dependency structures.

**Tasks**:
- [ ] Update state.json: increment next_project_number to account for new tasks
- [ ] Add new task entries to state.json active_projects array with status "not_started", correct dependencies, task_type "lean4", topic assignments
- [ ] If task 7 needs a new dependency on Task 29, update task 7's dependencies array in state.json
- [ ] Prepend new task descriptions to TODO.md (new tasks at top of ## Tasks section)
- [ ] Update the Task Order dependency wave table in TODO.md header to include new tasks
- [ ] Update the Grouped by Topic section to place new tasks under appropriate headers (Foundations for task 29, Modal Logic for task 30, Temporal Logic for task 31)
- [ ] Create task directories: `mkdir -p specs/029_generic_mcs_foundations`, etc.
- [ ] Verify state.json and TODO.md are consistent (task counts, dependency references)

**Timing**: 45 minutes

**Depends on**: 2

**Files to modify**:
- `specs/state.json` - Add new task entries, update next_project_number, optionally update task 7 dependencies
- `specs/TODO.md` - Add new task descriptions, update dependency wave table

**Verification**:
- `jq '.next_project_number' specs/state.json` returns correct value
- All new tasks appear in both state.json and TODO.md
- Dependency references point to valid task numbers
- No task number collisions

---

### Phase 4: Update ROADMAP.md [NOT STARTED]

**Goal**: Update ROADMAP.md to reflect the expanded metalogic layer, adding a new section for standalone metalogic and updating the dependency structure and success metrics.

**Tasks**:
- [ ] Add a new subsection under "Porting Phases" for metalogic (between current Phase 3 Temporal Semantics and Phase 4 Bimodal Porting, or as Phase 5)
- [ ] Document the generic MCS foundations task in the Foundations section
- [ ] Add modal metalogic (task 30) to the Modal module section
- [ ] Add temporal metalogic (task 31) to the Temporal module section
- [ ] Update the Import Hierarchy diagram to show Metalogic/ directories
- [ ] Update the Task Dependency Structure wave table to include new tasks
- [ ] Update Component Accounting table with new metalogic line counts
- [ ] Add success metrics for metalogic:
  - Generic MCS definitions in `Foundations/Logic/Metalogic/`
  - Modal deduction theorem + MCS in `Logics/Modal/Metalogic/`
  - Temporal deduction theorem + MCS in `Logics/Temporal/Metalogic/`
  - (If full scope) Modal soundness/completeness over Kripke frames
  - (If full scope) Temporal soundness/completeness over linear orders
- [ ] Update the "What Does Not Yet Exist" table to include metalogic components

**Timing**: 30 minutes

**Depends on**: 3

**Files to modify**:
- `specs/ROADMAP.md` - Add metalogic sections, update dependency structure, update metrics

**Verification**:
- ROADMAP.md references all new tasks by number
- Import hierarchy diagram is accurate
- Success metrics are measurable and specific
- Component accounting adds up (no double-counting with existing tasks)

## Testing & Validation

- [ ] All new task numbers are unique and sequential from next_project_number
- [ ] state.json parses as valid JSON after modifications
- [ ] Every new task in state.json has a corresponding entry in TODO.md
- [ ] Every dependency reference in new tasks points to an existing task number
- [ ] Dependency graph is acyclic (no circular dependencies)
- [ ] Task 7 dependency update (if needed) does not break existing wave structure
- [ ] ROADMAP.md component accounting sums correctly
- [ ] No existing task descriptions were modified (research confirmed they are correctly scoped)

## Artifacts & Outputs

- `specs/028_structure_metalogic_across_systems/plans/01_metalogic-structure-plan.md` (this file)
- Updated `specs/state.json` with new task entries
- Updated `specs/TODO.md` with new task descriptions and dependency wave table
- Updated `specs/ROADMAP.md` with metalogic sections
- New task directories: `specs/029_*/`, `specs/030_*/`, `specs/031_*/` (names depend on Phase 2 design)

## Rollback/Contingency

If the implementation needs to be reverted:
1. Use `git checkout -- specs/state.json specs/TODO.md specs/ROADMAP.md` to restore the original files
2. Remove any created task directories with `rm -rf specs/029_* specs/030_* specs/031_*`
3. Task 28 returns to [PLANNED] status for re-execution
