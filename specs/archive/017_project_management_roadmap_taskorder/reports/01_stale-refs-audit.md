# Research Report: Task #17

**Task**: 17 - Clean stale task 14 references and verify Task Order consistency
**Started**: 2026-06-08T00:00:00Z
**Completed**: 2026-06-08T00:00:00Z
**Effort**: <1 hour
**Dependencies**: None
**Sources/Inputs**: specs/TODO.md, specs/state.json
**Artifacts**: specs/017_project_management_roadmap_taskorder/reports/01_stale-refs-audit.md
**Standards**: report-format.md

## Executive Summary

- Task 14 is completed and archived; its work (creating `Bimodal.Formula`) has been absorbed into the codebase. All 5 formal `**Dependencies**:` fields that cite task 14 are stale and must be updated.
- All prose references to "task 14" in `**Description**` and `**Adaptation notes**` sections are contextual history, not live dependency declarations — they can be updated to reference the relevant Lean files/types directly.
- One Task Order wave placement is incorrect: task 11 (deps [4]) is listed in Wave 3 alongside task 4 (which task 11 depends on). Task 11 must move to Wave 4.
- State.json does NOT list task 14 in any dependency array — it is already clean.

## Context & Scope

Task 14 created `Bimodal.Formula` with constructors `{atom, bot, imp, box, untl, snce}` and established the modular typeclass infrastructure. It has been completed and archived. All references to "task 14" in TODO.md task descriptions and dependency fields are now stale.

The audit covers:
1. Formal `**Dependencies**:` fields in TODO.md task entries (actionable — these drive workflow gating)
2. Prose references in `**Description**` and `**Adaptation notes**` sections (informational — can be updated to be more precise)
3. The Task Order dependency wave table (structural — must correctly reflect the dependency graph)
4. `state.json` dependency arrays (already clean — no task 14 references)

## Findings

### Stale Formal Dependency Lines in TODO.md

These five `**Dependencies**:` lines explicitly list task 14 and must be updated:

| Line | Task | Current Dependencies | Correct Dependencies |
|------|------|----------------------|----------------------|
| 198 | Task 11 (Conservative Extension) | `Tasks 4, 14` | `Task 4` |
| 228 | Task 10 (Separation Theorem) | `Tasks 4, 5, 7, 14` | `Tasks 4, 5, 7` |
| 251 | Task 9 (Decidability/Tableau) | `Tasks 4, 7, 14` | `Tasks 4, 7` |
| 281 | Task 8 (Completeness) | `Tasks 6, 7, 14` | `Tasks 6, 7` |
| 400 | Task 3 (Task Frame Semantics) | `Tasks 2, 14` | `Task 2` |

Note: `state.json` dependency arrays for these tasks are already correct — they do not include 14. Only the TODO.md `**Dependencies**:` lines need updating.

### Stale Prose References in TODO.md

These lines reference task 14 in prose (not in formal Dependencies fields). They describe the origin of `Bimodal.Formula` and should be updated to reference the existing type directly:

| Line | Task | Reference Type | Current Text (excerpt) |
|------|------|----------------|------------------------|
| 200 | Task 11 | Description | "...typeclass infrastructure from task 14" |
| 210 | Task 11 | Adaptation notes | "...`Bimodal.Formula` already exists from task 14..." |
| 230 | Task 10 | Description | "...embedding functions from task 14 (`Modal.Formula.toBimodal`...)" |
| 241 | Task 10 | Adaptation notes | "...must reference `Bimodal.Formula` from task 14..." |
| 269 | Task 9 | Adaptation notes | "...`Bimodal.Formula` from task 14 instead of BimodalLogic's original Formula..." |
| 293 | Task 8 | Adaptation notes | "...Port to use `Bimodal.Formula` from task 14..." |
| 400 | Task 3 | Dependencies | "Tasks 2, 14 (Syntax and modular architecture)" |
| 413 | Task 3 | Adaptation notes | "...Port to use `Cslib.Logic.Bimodal.Formula` from task 14..." |
| 425 | Task 2 | Description | "Task 14 already created `Bimodal.Formula` with..." |
| 429 | Task 2 | Note on Formula.lean | "...The inductive type already exists from task 14..." |
| 432 | Task 2 | Source files | "...inductive type portion already done in task 14..." |
| 441 | Task 2 | Adaptation notes | "...matches `Bimodal.Formula` from task 14..." |

**Recommended prose fix**: Replace "from task 14" / "from task 14's work" with "already exists in `Cslib/Logics/Bimodal/Syntax/Basic.lean`" where it refers to the formula type. For embedding function references in tasks 10, update to reference task 15 (which provides `PL.toBimodal`, `Modal.Formula.toBimodal`, etc.).

### Task Order Wave Table Inconsistency

**Wave 3** in the Task Order table reads:
```
| 3 | 4 (dep 2,20,22), 11 (dep 4) | Wave 2 |
```

Task 11 depends on task 4. Task 4 is also in Wave 3. A task cannot be in the same wave as its dependency — it must be in a later wave. Task 11 should be in **Wave 4**.

Corrected wave assignment:
- Wave 3: `4 (dep 2,20,22)` only
- Wave 4: `5 (dep 4,21,22), 6 (dep 3,4), 11 (dep 4), 23 (dep 22)`

All other wave assignments match the state.json dependency graph:
- Wave 1: 2, 12, 15, 16, 17, 18, 20 — correct (all have no internal task dependencies, or only external like BimodalLogic:291)
- Wave 2: 3 (dep 2), 21 (dep 16,20), 22 (dep 20) — correct
- Wave 3: 4 (dep 2,20,22) — correct (after removing 11)
- Wave 4: 5 (dep 4,21,22), 6 (dep 3,4), 11 (dep 4), 23 (dep 22) — correct after adding 11
- Wave 5: 7 (dep 4,5) — correct
- Wave 6: 8 (dep 6,7), 9 (dep 4,7), 10 (dep 4,5,7) — correct

### State.json Status

State.json is clean. No active project has 14 in its `dependencies` array. The tasks that reference task 14 in TODO.md prose (3, 8, 9, 10, 11) have correct dependencies in state.json already.

## Decisions

1. **Formal Dependencies fields**: Must be updated — these 5 fields actively misrepresent task dependencies
2. **Prose references**: Should be updated for accuracy but are lower priority (informational only)
3. **Task Order Wave 3 → Wave 4 for task 11**: Must be fixed — wave table is structurally incorrect
4. **State.json**: No changes needed — already clean

## Risks & Mitigations

- **Risk**: Leaving stale dependency fields could cause confusion when implementing tasks 3, 8, 9, 10, 11 — an implementer may wait for task 14 which will never appear
  - **Mitigation**: Fix the 5 formal dependency lines in this task
- **Risk**: Wave table error for task 11 is minor but could mislead scheduling
  - **Mitigation**: Fix wave table in same operation as dependency cleanup

## Context Extension Recommendations

None for this meta task.

## Appendix

### Search Queries Used
- `grep -n -i "task 14\|task14\|\b14\b" specs/TODO.md`
- `grep -n "Dependencies.*14\|14.*Dependencies" specs/TODO.md`
- `grep -n "dependencies.*14\|14.*dependencies" specs/state.json`
- Python jq equivalent to extract all dependency arrays from state.json

### Summary of Changes Required

**TODO.md — Formal Dependencies lines (5 changes)**:
1. Line 198: `Tasks 4, 14 (ProofSystem and modular architecture must be complete)` → `Task 4 (ProofSystem)`
2. Line 228: `Tasks 4, 5, 7, 14 (ProofSystem, Theorems, MCS/Deduction, and modular architecture)` → `Tasks 4, 5, 7 (ProofSystem, Perpetuity Theorems, MCS/Deduction)`
3. Line 251: `Tasks 4, 7, 14 (ProofSystem, MCS/Deduction, and modular architecture)` → `Tasks 4, 7 (ProofSystem, MCS/Deduction)`
4. Line 281: `Tasks 6, 7, 14 (FrameConditions+Soundness, MCS/Deduction, and modular architecture)` → `Tasks 6, 7 (FrameConditions+Soundness, MCS/Deduction)`
5. Line 400: `Tasks 2, 14 (Syntax and modular architecture)` → `Task 2 (Bimodal Syntax)`

**TODO.md — Task Order Wave Table (1 change)**:
- Move task 11 from Wave 3 to Wave 4

**TODO.md — Prose references**: Optional cleanup of 12 lines across tasks 2, 3, 8, 9, 10, 11

**State.json**: No changes needed
