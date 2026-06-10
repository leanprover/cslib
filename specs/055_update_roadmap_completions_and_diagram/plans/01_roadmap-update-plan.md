# Implementation Plan: Task #55

- **Task**: 55 - Review and update ROADMAP.md with completions and mermaid diagram
- **Status**: [COMPLETED]
- **Effort**: 1.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/055_update_roadmap_completions_and_diagram/reports/01_roadmap-review.md
- **Artifacts**: plans/01_roadmap-update-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: markdown
- **Lean Intent**: false

## Overview

Update ROADMAP.md to reflect all work completed since the last revision (task 45), including the temporal chronicle completeness pipeline (tasks 46-49), temporal syntax infrastructure, and bimodal embedding module. Fix the mermaid dependency diagram by adding two missing edges (FC-->TS, FT-->TM), update the project structure tree to include the new Chronicle/ directory and support files, and correct TODO.md status inconsistencies for tasks 38, 39, and 41 which incorrectly show [COMPLETED] in their detail sections.

### Research Integration

The research report (01_roadmap-review.md) identified five categories of updates needed:
1. Three missing entries in the Completed table (temporal syntax infrastructure, chronicle pipeline, bimodal embedding)
2. Two missing edges in the mermaid diagram (FC-->TS, FT-->TM)
3. Project structure tree missing Chronicle/ directory, support files, and Embedding/ contents
4. TODO.md tasks 38, 39, 41 showing [COMPLETED] in detail sections but genuinely not_started per state.json and codebase verification
5. Remaining table is correct as-is (no changes needed)

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task directly maintains ROADMAP.md itself. It advances accuracy of the project's primary tracking document.

## Goals & Non-Goals

**Goals**:
- Add all missing completed items to the ROADMAP.md Completed table
- Fix mermaid diagram to accurately reflect module dependencies
- Update project structure tree to match current filesystem
- Correct TODO.md status inconsistencies for tasks 38, 39, 41

**Non-Goals**:
- Restructuring ROADMAP.md format or sections
- Adding new Remaining items beyond what already exists
- Modifying state.json entries for tasks 38, 39, 41 (they are already correct as not_started)
- Changing the Approach section text

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Incorrectly marking something as completed that is not | H | L | Verify against actual file existence in Cslib/ before adding to Completed table |
| Missing a completed item | M | L | Cross-reference archive/state.json completed tasks against Completed table |
| Mermaid diagram rendering issues after edits | M | L | Keep existing node/edge syntax style; only add new edges |
| TODO.md edit corrupts other task entries | M | L | Use targeted edits only on tasks 38, 39, 41 detail blocks |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 3 | -- |
| 2 | 4 | -- |

Phases within the same wave can execute in parallel.

### Phase 1: Update Completed Table [COMPLETED]

**Goal**: Add missing completed items to the ROADMAP.md Completed table.

**Tasks**:
- [ ] Add row: "Temporal syntax infrastructure (Context, BigConj, Subformulas)" with module `Logics/Temporal/Syntax/`
- [ ] Add row: "Chronicle-based temporal completeness pipeline (R-relation, canonical chain, point insertion, chronicle construction, truth lemma)" with module `Logics/Temporal/Metalogic/Chronicle/`
- [ ] Add row: "Bimodal embedding (PropositionalEmbedding, ModalEmbedding, TemporalEmbedding)" with module `Logics/Bimodal/Embedding/`
- [ ] Verify each entry corresponds to actual files in the codebase

**Timing**: 15 minutes

**Depends on**: none

**Files to modify**:
- `specs/ROADMAP.md` - Add 3 rows to Completed table

**Verification**:
- Completed table has 22 rows (19 original + 3 new)
- Each new row references a directory that exists in Cslib/

---

### Phase 2: Fix Mermaid Diagram [COMPLETED]

**Goal**: Add missing dependency edges to the mermaid flowchart so it accurately represents module imports.

**Tasks**:
- [ ] Add `FC --> TS` edge (Foundations Connectives/ProofSystem feeds Temporal Syntax, mirroring FC --> BS)
- [ ] Add `FT --> TM` edge (Temporal metalogic uses Foundations theorems, mirroring FT --> MM)
- [ ] Verify all existing edges remain correct
- [ ] Verify the diagram description paragraph below the diagram mentions the new edges if needed

**Timing**: 15 minutes

**Depends on**: none

**Files to modify**:
- `specs/ROADMAP.md` - Add 2 edges to mermaid flowchart block

**Verification**:
- Diagram contains `FC --> TS` and `FT --> TM` edges
- Existing edges are unchanged
- Mermaid syntax is valid (matching existing style)

---

### Phase 3: Update Project Structure Tree [COMPLETED]

**Goal**: Update the directory tree in ROADMAP.md to reflect the current filesystem, adding the Chronicle/ directory, temporal metalogic support files, and bimodal embedding contents.

**Tasks**:
- [ ] Add `Chronicle/` subdirectory under `Metalogic/` in the Temporal section with its 10 files
- [ ] Add temporal metalogic support files: TemporalContent.lean, WitnessSeed.lean, PropositionalHelpers.lean, GeneralizedNecessitation.lean, CompletenessHelpers.lean
- [ ] Add Embedding/ contents under Bimodal: ModalEmbedding.lean, PropositionalEmbedding.lean, TemporalEmbedding.lean
- [ ] Verify tree matches actual filesystem structure

**Timing**: 20 minutes

**Depends on**: none

**Files to modify**:
- `specs/ROADMAP.md` - Expand project structure tree

**Verification**:
- Tree shows Chronicle/ with all 10 .lean files
- Tree shows 5 temporal metalogic support files
- Tree shows Embedding/ with 3 .lean files
- Tree structure matches `find Cslib/ -type f` output

---

### Phase 4: Fix TODO.md Status Inconsistencies [COMPLETED]

**Goal**: Correct tasks 38, 39, and 41 in TODO.md which incorrectly show [COMPLETED] in their detail sections. These tasks are genuinely not_started per state.json and codebase verification.

**Tasks**:
- [ ] Change task 38 detail section status from `[COMPLETED]` to `[NOT STARTED]`
- [ ] Change task 39 detail section status from `[COMPLETED]` to `[NOT STARTED]`
- [ ] Change task 41 detail section status from `[COMPLETED]` to `[NOT STARTED]`
- [ ] Verify the wave table at top of TODO.md already shows these as [NOT STARTED] (no change needed there)
- [ ] Verify state.json already shows these as "not_started" (no change needed there)

**Timing**: 10 minutes

**Depends on**: none

**Files to modify**:
- `specs/TODO.md` - Fix 3 status markers in task detail blocks

**Verification**:
- Tasks 38, 39, 41 show [NOT STARTED] in both the wave table and detail sections
- state.json remains consistent (already shows not_started)
- No other task entries are affected

## Testing & Validation

- [ ] ROADMAP.md Completed table has 22 rows with no duplicates
- [ ] ROADMAP.md Remaining table is unchanged (6 items)
- [ ] Mermaid diagram has FC-->TS and FT-->TM edges alongside all original edges
- [ ] Project structure tree matches actual `Cslib/` filesystem for all listed paths
- [ ] TODO.md tasks 38, 39, 41 show [NOT STARTED] consistently
- [ ] state.json is unchanged (already correct)

## Artifacts & Outputs

- `specs/ROADMAP.md` - Updated roadmap with completed items, fixed diagram, expanded tree
- `specs/TODO.md` - Fixed status inconsistencies for tasks 38, 39, 41
- `specs/055_update_roadmap_completions_and_diagram/plans/01_roadmap-update-plan.md` - This plan

## Rollback/Contingency

All changes are to markdown files tracked in git. If any update introduces errors, revert with `git checkout -- specs/ROADMAP.md specs/TODO.md`. No code files are modified.
