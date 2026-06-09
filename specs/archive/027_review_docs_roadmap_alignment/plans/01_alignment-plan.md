# Implementation Plan: Task #27

- **Task**: 27 - Systematically review all documentation and standards, ensuring tasks and ROADMAP.md are in alignment
- **Status**: [COMPLETED]
- **Effort**: 1.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/027_review_docs_roadmap_alignment/reports/01_docs-roadmap-alignment.md
- **Artifacts**: plans/01_alignment-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: general
- **Lean Intent**: false

## Overview

This plan addresses 9 identified misalignments between state.json, TODO.md, and ROADMAP.md discovered during research. The fixes are grouped into three phases: (1) critical status synchronization in TODO.md, (2) stale description updates in state.json, and (3) ROADMAP.md wave table correction with TODO.md Task Order regeneration. All changes are conservative edits to documentation and machine state only -- no code changes.

### Research Integration

The research report (01_docs-roadmap-alignment.md) identified 5 critical status mismatches and 4 moderate documentation misalignments. All 9 issues are addressed in this plan. The critical fixes (Phase 1) resolve TODO.md status markers that diverge from state.json, which is the machine-readable source of truth. The moderate fixes (Phases 2-3) update stale descriptions and the ROADMAP.md wave table.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This plan directly fixes the ROADMAP.md wave table (Phase 3) to reflect current task completion status. It does not advance any porting work but ensures the documentation accurately represents project state.

## Goals & Non-Goals

**Goals**:
- Synchronize TODO.md status markers with state.json for tasks 12, 15, 17, 18, 20
- Update stale state.json descriptions for tasks 2, 3, 6-11 (Temporal -> Bimodal path fix) and task 12 (outdated PR strategy)
- Update ROADMAP.md wave table to remove completed tasks and add task 27
- Regenerate TODO.md Task Order section to reflect current statuses

**Non-Goals**:
- Modifying any Lean source code
- Changing task dependencies or wave structure
- Updating README.md, CONTRIBUTING.md, or other repository-level docs (research confirmed no misalignments)
- Changing state.json status fields (only descriptions are stale; statuses are the source of truth)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Editing TODO.md status markers incorrectly | H | L | Use state.json as source of truth; verify each change against state.json before writing |
| state.json JSON parse error from bad edit | H | L | Validate JSON after each edit with jq |
| ROADMAP.md wave table out of sync with TODO.md dependency waves | M | L | Copy exact wave table from TODO.md lines 12-19 as reference |
| generate-task-order.sh produces unexpected output | M | L | Inspect output before replacing TODO.md section |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 1 |

Phases within the same wave can execute in parallel.

### Phase 1: Fix Critical TODO.md Status Mismatches [COMPLETED]

**Goal**: Synchronize TODO.md status markers with state.json for all 5 mismatched tasks, and add the missing research artifact link for task 20.

**Tasks**:
- [ ] Change task 12 status in TODO.md from `[RESEARCHING]` to `[PARTIAL]`
- [ ] Change task 15 status in TODO.md from `[RESEARCHING]` to `[COMPLETED]`
- [ ] Change task 17 status in TODO.md from `[RESEARCHING]` to `[COMPLETED]`
- [ ] Change task 18 status in TODO.md from `[RESEARCHING]` to `[COMPLETED]`
- [ ] Change task 20 status in TODO.md from `[NOT STARTED]` to `[RESEARCHED]` -- NOTE: research report says this, but TODO.md already shows `[RESEARCHED]` for task 20 (line 135). Verify before editing; skip if already correct.
- [ ] Add research artifact link to task 20 if missing -- NOTE: TODO.md line 137 already has `**Research**: [020_propositional_hilbert_theorems/reports/01_hilbert-theorems-research.md]`. Verify before editing; skip if already present.
- [ ] Verify all 5 status changes match state.json values

**Timing**: 20 minutes

**Depends on**: none

**Files to modify**:
- `specs/TODO.md` - Fix status markers for tasks 12, 15, 17, 18 (task 20 may already be correct)

**Verification**:
- grep for `[RESEARCHING]` in TODO.md returns zero results
- Task 12 shows `[PARTIAL]`, tasks 15/17/18 show `[COMPLETED]`
- All TODO.md statuses match their state.json counterparts

---

### Phase 2: Fix Stale state.json Descriptions [COMPLETED]

**Goal**: Update state.json description fields for tasks 2, 3, 6-11 to use `Cslib/Logics/Bimodal/` paths instead of `Cslib/Logics/Temporal/`, and update task 12 description to reflect the current PR strategy.

**Tasks**:
- [ ] In state.json task 2 description: replace `Cslib/Logics/Temporal/` with `Cslib/Logics/Bimodal/` and update PR titles/namespace references
- [ ] In state.json task 3 description: replace `Cslib/Logics/Temporal/` with `Cslib/Logics/Bimodal/`
- [ ] In state.json task 6 description: replace `Cslib/Logics/Temporal/` with `Cslib/Logics/Bimodal/`
- [ ] In state.json task 7 description: replace `Cslib/Logics/Temporal/` with `Cslib/Logics/Bimodal/`
- [ ] In state.json task 8 description: replace `Cslib/Logics/Temporal/` with `Cslib/Logics/Bimodal/`
- [ ] In state.json task 9 description: replace `Cslib/Logics/Temporal/` with `Cslib/Logics/Bimodal/`
- [ ] In state.json task 10 description: replace `Cslib/Logics/Temporal/` with `Cslib/Logics/Bimodal/`
- [ ] In state.json task 11 description: replace `Cslib/Logics/Temporal/` with `Cslib/Logics/Bimodal/`
- [ ] Update state.json task 12 description to match the current TODO.md task 12 description (4 standalone PRs + 10 bimodal PRs, `Cslib.Logics.Bimodal` namespace)
- [ ] Validate state.json is valid JSON after all edits (run `jq . specs/state.json`)

**Timing**: 30 minutes

**Depends on**: 1

**Files to modify**:
- `specs/state.json` - Update description fields for tasks 2, 3, 6-11, 12

**Verification**:
- `jq . specs/state.json` parses without error
- `grep -c "Cslib/Logics/Temporal/" specs/state.json` returns 0 for description fields of tasks 2, 3, 6-11 (note: tasks 22-23 legitimately reference Temporal paths)
- Task 12 description mentions "4 standalone PRs + 10 bimodal PRs" and `Cslib.Logics.Bimodal`

---

### Phase 3: Update ROADMAP.md Wave Table and Regenerate Task Order [COMPLETED]

**Goal**: Fix the stale ROADMAP.md wave table by removing completed tasks and adding task 27, then regenerate the TODO.md Task Order section to reflect current statuses.

**Tasks**:
- [ ] Replace ROADMAP.md wave table (lines ~277-284) with updated table that removes completed tasks (15, 17, 18, 24, 25) from Wave 1 and adds task 27
- [ ] Updated Wave 1 should read: `2, 12, 16, 20, 27` (matching TODO.md wave table)
- [ ] Waves 2-6 remain unchanged (their tasks are all still active)
- [ ] Run `bash .claude/scripts/generate-task-order.sh` to regenerate the TODO.md Task Order section
- [ ] Verify the regenerated Task Order section reflects correct statuses (task 27 as `[RESEARCHED]`, no stale `[IMPLEMENTING]` for task 25)
- [ ] If `generate-task-order.sh` is not available or fails, manually update the Task Order section status for task 27 from `[NOT STARTED]` to `[RESEARCHED]`

**Timing**: 20 minutes

**Depends on**: 1

**Files to modify**:
- `specs/ROADMAP.md` - Replace wave table with current version
- `specs/TODO.md` - Regenerate Task Order section (via script or manual edit)

**Verification**:
- ROADMAP.md Wave 1 lists exactly: `2, 12, 16, 20, 27`
- ROADMAP.md Wave 1 does NOT contain tasks 15, 17, 18, 24, or 25
- TODO.md Task Order wave table matches ROADMAP.md wave table structure
- Task 27 appears in Task Order section with `[RESEARCHED]` status
- No completed tasks (15, 17, 18, 19, 24, 25, 26) appear in the Task Order topic tree

## Testing & Validation

- [ ] `jq . specs/state.json` parses without error
- [ ] `grep -c "\[RESEARCHING\]" specs/TODO.md` returns 0
- [ ] All 5 status-mismatched tasks in TODO.md match state.json
- [ ] ROADMAP.md wave table contains only active tasks
- [ ] TODO.md Task Order section matches current state.json statuses
- [ ] No unintended changes to task descriptions in TODO.md (only status markers changed)

## Artifacts & Outputs

- `specs/027_review_docs_roadmap_alignment/plans/01_alignment-plan.md` (this file)
- `specs/027_review_docs_roadmap_alignment/summaries/01_alignment-summary.md` (created during implementation)
- Modified files: `specs/TODO.md`, `specs/state.json`, `specs/ROADMAP.md`

## Rollback/Contingency

All three files (`TODO.md`, `state.json`, `ROADMAP.md`) are tracked by git. If any change introduces errors:
1. Run `git diff specs/TODO.md specs/state.json specs/ROADMAP.md` to review changes
2. Run `git checkout -- specs/TODO.md specs/state.json specs/ROADMAP.md` to revert all changes
3. Re-apply changes incrementally with verification after each edit
