# Implementation Plan: Clean stale task 14 references and verify Task Order consistency

- **Task**: 17 - Clean stale task 14 references and verify Task Order consistency
- **Status**: [COMPLETED]
- **Effort**: <1 hour
- **Dependencies**: None
- **Research Inputs**: specs/017_project_management_roadmap_taskorder/reports/01_stale-refs-audit.md
- **Artifacts**: plans/01_stale-refs-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: meta
- **Lean Intent**: false

## Overview

Remove all stale references to completed task 14 from TODO.md formal dependency fields and prose descriptions, fix the wave table placement error for task 11, and verify that TODO.md and state.json are consistent. All changes are confined to TODO.md; state.json is already clean per the research audit.

### Research Integration

The research report (01_stale-refs-audit.md) identified:
- 5 formal `**Dependencies**:` lines citing task 14 (tasks 3, 8, 9, 10, 11) -- must be updated
- 12 prose references to "task 14" across tasks 2, 3, 8, 9, 10, 11 -- should be updated for accuracy
- 1 wave table error: task 11 is placed in Wave 3 alongside task 4 (its dependency) -- must move to Wave 4
- state.json is already clean -- no changes needed

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consultation needed for this meta cleanup task.

## Goals & Non-Goals

**Goals**:
- Remove task 14 from all 5 formal `**Dependencies**:` fields in TODO.md
- Fix the Task Order wave table so task 11 is in Wave 4 (not Wave 3)
- Update 12 prose references to replace "from task 14" with references to existing Lean files
- Verify TODO.md task dependencies match state.json dependency arrays

**Non-Goals**:
- Modifying state.json (already clean per research audit)
- Updating ROADMAP.md (handled by task 19)
- Changing any task descriptions beyond task 14 reference cleanup

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Incorrect dependency removal breaks task ordering | M | L | Research report provides exact line numbers and replacement text; verify against state.json |
| Prose edits introduce factual errors about file locations | L | L | Use exact file paths from codebase (e.g., `Cslib/Logics/Bimodal/Syntax/Basic.lean`) |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel.

### Phase 1: Fix formal dependencies and wave table [COMPLETED]

**Goal**: Remove task 14 from all 5 formal `**Dependencies**:` fields and correct the Task Order wave table.

**Tasks**:
- [x] Update task 11 Dependencies line: `Tasks 4, 14 (ProofSystem and modular architecture must be complete)` -> `Task 4 (ProofSystem)` *(completed)*
- [x] Update task 10 Dependencies line: `Tasks 4, 5, 7, 14 (ProofSystem, Theorems, MCS/Deduction, and modular architecture)` -> `Tasks 4, 5, 7 (ProofSystem, Perpetuity Theorems, MCS/Deduction)` *(completed)*
- [x] Update task 9 Dependencies line: `Tasks 4, 7, 14 (ProofSystem, MCS/Deduction, and modular architecture)` -> `Tasks 4, 7 (ProofSystem, MCS/Deduction)` *(completed)*
- [x] Update task 8 Dependencies line: `Tasks 6, 7, 14 (FrameConditions+Soundness, MCS/Deduction, and modular architecture)` -> `Tasks 6, 7 (FrameConditions+Soundness, MCS/Deduction)` *(completed)*
- [x] Update task 3 Dependencies line: `Tasks 2, 14 (Syntax and modular architecture)` -> `Task 2 (Bimodal Syntax)` *(completed)*
- [x] Fix Task Order wave table *(deviation: skipped — wave table already correct; task 11 was already in Wave 4, not Wave 3 as the research report described)*

**Timing**: 15 minutes

**Depends on**: none

**Files to modify**:
- `specs/TODO.md` - 5 dependency field edits + 2 wave table line edits

**Verification**:
- `grep -n "Dependencies.*14" specs/TODO.md` returns no results
- Wave 3 line contains only `4 (dep 2,20,22)` (no task 11)
- Wave 4 line contains `11 (dep 4)` alongside existing entries

---

### Phase 2: Clean prose references [COMPLETED]

**Goal**: Update 12 prose references to task 14 in task descriptions and adaptation notes for accuracy.

**Tasks**:
- [x] Task 11 description (line ~200): replace "typeclass infrastructure from task 14" with reference to existing typeclass infrastructure *(completed)*
- [x] Task 11 adaptation notes (line ~210): replace "Bimodal.Formula already exists from task 14" with "Bimodal.Formula already exists in Cslib/Logics/Bimodal/Syntax/Basic.lean" *(completed)*
- [x] Task 10 description (line ~230): replace "embedding functions from task 14" with reference to the embedding files *(completed)*
- [x] Task 10 adaptation notes (line ~241): replace "must reference Bimodal.Formula from task 14" with direct file reference *(completed)*
- [x] Task 9 adaptation notes (line ~269): replace "Bimodal.Formula from task 14" with direct file reference *(completed)*
- [x] Task 8 adaptation notes (line ~293): replace "Port to use Bimodal.Formula from task 14" with direct file reference *(completed)*
- [x] Task 3 dependencies prose (line ~400): already fixed in Phase 1, verify no remaining "task 14" text *(completed: no stale references remain)*
- [x] Task 3 adaptation notes (line ~413): replace "Cslib.Logic.Bimodal.Formula from task 14" with "Cslib.Logics.Bimodal.Syntax.Formula" *(completed)*
- [x] Task 2 description (line ~425): replace "Task 14 already created Bimodal.Formula" with "Bimodal.Formula already exists" *(completed)*
- [x] Task 2 note on Formula.lean (line ~429): replace "already exists from task 14" with "already exists in Cslib/Logics/Bimodal/Syntax/Basic.lean" *(completed)*
- [x] Task 2 source files note (line ~432): replace "already done in task 14" with "already present" *(completed)*
- [x] Task 2 adaptation notes (line ~441): replace "from task 14" with direct file reference *(completed)*

**Timing**: 15 minutes

**Depends on**: 1

**Files to modify**:
- `specs/TODO.md` - 12 prose edits across tasks 2, 3, 8, 9, 10, 11

**Verification**:
- `grep -in "task 14" specs/TODO.md` returns only the task 14 archive entry (if any) or zero results
- All replacement text references valid file paths in the codebase

---

### Phase 3: Verify consistency [COMPLETED]

**Goal**: Confirm TODO.md and state.json are synchronized after edits.

**Tasks**:
- [x] For each task with modified dependencies (3, 8, 9, 10, 11): verify the TODO.md Dependencies field matches the state.json dependencies array *(completed: all match)*
- [x] Verify the Task Order wave table is consistent with all task dependency fields *(completed: wave table already correct — task 11 was already in Wave 4)*
- [x] Run a final `grep -in "task 14" specs/TODO.md` to confirm no stale references remain *(completed: only task 17 self-description references remain, which are expected)*

**Timing**: 10 minutes

**Depends on**: 2

**Files to modify**:
- None (read-only verification)

**Verification**:
- All 5 tasks' TODO.md dependency fields match their state.json dependency arrays
- Wave table correctly places all tasks in waves consistent with their dependencies
- Zero stale "task 14" references in TODO.md

## Testing & Validation

- [x] `grep -n "Dependencies.*14" specs/TODO.md` returns zero matches *(verified)*
- [x] `grep -in "task 14" specs/TODO.md` returns zero matches (or only archive references) *(verified: only task 17 self-description)*
- [x] Wave 3 contains `4,23`; Wave 4 contains tasks 5, 6, 11 *(verified: task 23 belongs in Wave 3 alongside task 4, both blocked by Wave 2; plan note "Wave 4 contains 23" was stale)*
- [x] state.json has no task 14 in any dependencies array (already verified by research) *(confirmed)*
- [x] All tasks' TODO.md dependency fields are consistent with state.json *(verified: tasks 3, 8, 9, 10, 11 all match state.json)*

## Artifacts & Outputs

- specs/017_project_management_roadmap_taskorder/plans/01_stale-refs-plan.md (this plan)
- specs/TODO.md (modified in place)

## Rollback/Contingency

All changes are to TODO.md only. If edits introduce errors, revert with `git checkout specs/TODO.md` to restore the pre-edit version. state.json is not modified.
