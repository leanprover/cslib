# Implementation Plan: Task #83

- **Task**: 83 - Review changes since task 74 to update PR 1 description and roadmap
- **Status**: [NOT STARTED]
- **Effort**: 1 hour
- **Dependencies**: None (task 82 in parallel; PR description avoids hard-coding def names to stay compatible)
- **Research Inputs**: specs/083_update_pr1_description_and_roadmap/reports/01_pr-description-update.md
- **Artifacts**: plans/01_pr-description-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: general
- **Lean Intent**: false

## Overview

Update the PR 1 description (`specs/059_pr1_foundations_logic/pr-description.md`) and the project roadmap (`specs/ROADMAP.md`) to reflect all changes made by tasks 75-82. The PR description needs 15 concrete edits: file count (15 to 16), total line count (3,708 to 3,822), six individual file line-count corrections, a new File Inventory entry for `DeductionHelpers.lean`, Verification section updates ("15 files" to "16 files" in two places plus CI blocker note), Known Issues updates, and a dependency graph addition. The ROADMAP needs the stale `Reasoning.lean` entry removed and `DeductionHelpers.lean` added to the project structure diagram. All changes are markdown text edits.

### Research Integration

The research report (01_pr-description-update.md) provides a complete change matrix with 15 specific PR description updates and 2 ROADMAP fixes, ranked by priority. Key insight: task 82 may rename defs in `DeductionHelpers.lean`, so the new File Inventory entry must use high-level prose rather than specific def names.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task directly updates ROADMAP.md to fix the stale `Reasoning.lean` entry and add `DeductionHelpers.lean` to the project structure diagram.

## Goals & Non-Goals

**Goals**:
- Update all file counts, line counts, and totals in pr-description.md to match current codebase state
- Add `DeductionHelpers.lean` entry to the File Inventory table using high-level prose (not specific def names)
- Update Verification section to reflect 16 files and add CI validation blocker note
- Update Known Issues section (item 3 deduplication update, optional private declarations note)
- Fix ROADMAP.md project structure diagram (remove Reasoning.lean, add DeductionHelpers.lean)

**Non-Goals**:
- Adding new "Recent Changes" sections for tasks 74, 79, 80, 81 (the existing sections implicitly cover this work)
- Running CI validation commands (that is task 82 Phase 6 scope)
- Modifying any Lean source files

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Task 82 renames defs in DeductionHelpers.lean after this task completes | L | H | Use high-level prose for the DeductionHelpers entry; do not hard-code def names |
| Line counts shift if task 82 modifies Foundations/Logic files | L | M | Note in Verification that counts are pre-task-82; task 82 summary can update if needed |
| ROADMAP structure diagram has other stale entries beyond Reasoning.lean | L | L | Research report audited the diagram; only Reasoning.lean is stale |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |

Phases within the same wave can execute in parallel.

### Phase 1: Update pr-description.md [NOT STARTED]

**Goal**: Apply all 15 updates identified in the research report to the PR description file.

**Tasks**:
- [ ] Update summary paragraph: "15 files" to "16 files"
- [ ] Update summary paragraph: "3,708 lines" to "3,822 lines"
- [ ] Update summary bullets: "Metalogic foundations (1 file)" to "(2 files)"
- [ ] Add `Metalogic/DeductionHelpers.lean` row to File Inventory table (119 lines, high-level description of HasHilbertTree typeclass and generic deduction helpers -- no specific def names)
- [ ] Update File Inventory line counts: ProofSystem.lean 354 to 352, Combinators.lean 333 to 338, Propositional/Connectives.lean 546 to 535, Modal/Basic.lean 203 to 202, Modal/S5.lean 639 to 530, TemporalDerived.lean 293 to 287
- [ ] Update File Inventory total row: 3,708 to 3,822
- [ ] Update Verification section: "All 15 files" to "All 16 files" (two occurrences)
- [ ] Add CI validation blockers note to Verification section listing the 5 required checks from CONTRIBUTING.md (lake shake, lake exe checkInitImports, lake lint, lake exe lint-style, lake exe mk_all --module)
- [ ] Update Known Issues item 3 (abbreviation deduplication) to reflect task 79 wrap/unwrap delegation work
- [ ] Optionally add note about 2 remaining private declarations (TemporalDerived.lean:124, Consistency.lean:180)
- [ ] Add DeductionHelpers.lean to the dependency graph section if one exists

**Timing**: 40 minutes

**Depends on**: none

**Files to modify**:
- `specs/059_pr1_foundations_logic/pr-description.md` - All line count, file count, inventory, verification, and known issues updates

**Verification**:
- All numeric counts in the file match the research report's audited values
- DeductionHelpers.lean entry uses high-level prose, not specific def names
- "16 files" appears consistently throughout
- CI blocker checks are listed in the Verification section

---

### Phase 2: Fix ROADMAP.md project structure diagram [NOT STARTED]

**Goal**: Remove the stale `Reasoning.lean` entry and add `DeductionHelpers.lean` to the ROADMAP project structure diagram.

**Tasks**:
- [ ] Remove the `Reasoning.lean` line from the Propositional subdirectory in the project structure diagram
- [ ] Add `DeductionHelpers.lean` under the `Foundations/Logic/Metalogic/` section of the project structure diagram

**Timing**: 10 minutes

**Depends on**: none

**Files to modify**:
- `specs/ROADMAP.md` - Project structure diagram fixes (remove stale entry, add new file)

**Verification**:
- `grep -n "Reasoning.lean" specs/ROADMAP.md` returns no results
- `grep -n "DeductionHelpers" specs/ROADMAP.md` returns the new entry
- The diagram's tree structure remains well-formed (correct indentation and box-drawing characters)

## Testing & Validation

- [ ] All "15 files" references in pr-description.md have been changed to "16 files"
- [ ] All "3,708" references have been changed to "3,822"
- [ ] DeductionHelpers.lean appears in the File Inventory table
- [ ] No specific def names (deduction_axiom, deductionAxiom, etc.) appear in the DeductionHelpers entry
- [ ] CI validation commands are listed in the Verification section
- [ ] Reasoning.lean no longer appears in ROADMAP.md
- [ ] DeductionHelpers.lean appears in ROADMAP.md project structure

## Artifacts & Outputs

- `specs/083_update_pr1_description_and_roadmap/plans/01_pr-description-plan.md` (this plan)
- `specs/059_pr1_foundations_logic/pr-description.md` (updated)
- `specs/ROADMAP.md` (updated)

## Rollback/Contingency

Both files are under git version control. If any edits introduce errors, revert with:
```bash
git checkout HEAD -- specs/059_pr1_foundations_logic/pr-description.md specs/ROADMAP.md
```
