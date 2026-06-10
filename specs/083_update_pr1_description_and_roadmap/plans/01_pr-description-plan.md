# Implementation Plan: Task #83

- **Task**: 83 - Review changes since task 74 to update PR 1 description and roadmap
- **Status**: [COMPLETED]
- **Effort**: 1 hour
- **Dependencies**: Task 81 (completed), Task 82 (completed)
- **Research Inputs**: specs/083_update_pr1_description_and_roadmap/reports/01_pr-description-update.md
- **Artifacts**: plans/01_pr-description-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: general
- **Lean Intent**: false

## Overview

Update `specs/059_pr1_foundations_logic/pr-description.md` and `specs/ROADMAP.md` to reflect all changes from tasks 75-82. Task 82 is now complete (renamed ~385 defs to camelCase, named 7 bare sections, passed all CI validation tools, added docstrings/copyright headers). The research report's total line count of 3,822 was a math error — the correct total is **3,704** (16 files).

### Research Integration

The research report identified 15 PR description updates and 2 ROADMAP fixes. Post-task-82 revisions:
- DeductionHelpers.lean defs are now camelCase (`deductionAxiom`, `deductionImpSelf`, etc.) — can use actual names
- CI validation suite has passed — Verification section can claim CI compliance
- Unnamed sections are now named — no longer a known issue
- Line count corrected: research said 3,822 (double-counted DeductionHelpers), actual is 3,704
- FrameConditions.lean is 90 lines (not 89)
- `public import Cslib.Init` was trimmed from ProofSystem.lean and Axioms.lean by task 81; only Connectives.lean retains it — Known Issues item 2 needs updating

### Prior Plan Reference

v1 plan assumed task 82 was still pending. This v2 incorporates task 82's completed results.

## Goals & Non-Goals

**Goals**:
- Update all file counts, line counts, and totals to match current codebase (16 files, 3,704 lines)
- Add `DeductionHelpers.lean` entry with actual camelCase def names
- Update Verification section with CI compliance (task 82 passed all checks)
- Update Known Issues to reflect current state
- Fix ROADMAP.md project structure diagram
- Update File Inventory table entries that changed (6 files + 1 new + total)

**Non-Goals**:
- Modifying any Lean source files
- Re-running CI validation (task 82 already did this)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Line counts shift from future work before PR submission | L | M | Note counts are as of task 82 completion; easy to re-count |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |

### Phase 1: Update pr-description.md [COMPLETED]

**Goal**: Apply all updates to reflect tasks 75-82 changes.

**Tasks**:

Summary section (line 7):
- [ ] "15 files" → "16 files"
- [ ] "3,708 lines" → "3,704 lines"

Summary bullets (line 12):
- [ ] "Metalogic foundations (1 file)" → "(2 files): `DerivationSystem` typeclass with Lindenbaum's lemma via Zorn's lemma, MCS construction; `HasHilbertTree` typeclass with generic deduction theorem helpers"

File Inventory table (lines 72-89):
- [ ] Update `ProofSystem.lean`: 354 → 352
- [ ] Update `Theorems/Combinators.lean`: 333 → 338 (and update role: `theorem_flip`→`flip`, `theorem_app1`→`app1`, `theorem_app2`→`app2` — these were renamed by task 81)
- [ ] Update `Theorems/Propositional/Connectives.lean`: 546 → 535
- [ ] Update `Theorems/Modal/Basic.lean`: 203 → 202
- [ ] Update `Theorems/Modal/S5.lean`: 639 → 530 (and note abbreviation refactoring)
- [ ] Update `Theorems/Temporal/TemporalDerived.lean`: 293 → 287
- [ ] Update `Theorems/Temporal/FrameConditions.lean`: 89 → 90
- [ ] Add new row for `Metalogic/DeductionHelpers.lean`: 119 lines, "`HasHilbertTree` typeclass; `deductionAxiom`, `deductionImpSelf`, `deductionAssumptionOther`, `deductionMpUnderImp` generic helpers"
- [ ] Update Total: 3,708 → 3,704

Dependency Graph (lines 93-109):
- [ ] Add `Metalogic/DeductionHelpers.lean` — imports Connectives only, imported by DeductionTheorem files

Verification section (lines 112-116):
- [ ] "All 15 files" → "All 16 files" (two occurrences)
- [ ] Add CI validation note: "CI validation suite passed: `lake shake`, `lake exe checkInitImports`, `lake lint`, `lake exe lint-style`, `lake exe mk_all --module`"

Module Keyword Migration section (line 139):
- [ ] "All 15" → "All 16"

Known Issues section (lines 148-151):
- [ ] Update item 2 (Public imports): "`public import Cslib.Init` remains in `Connectives.lean` (the root importer). Task 81 trimmed it from `ProofSystem.lean` and `Axioms.lean` where it was transitively available."
- [ ] Update item 3 (Abbreviation deduplication): Reflect task 79's full deduplication work (shared helper extraction, wrap/unwrap delegation) and task 81's S5.lean abbreviation refactoring

**Timing**: 40 minutes

**Depends on**: none

**Files to modify**:
- `specs/059_pr1_foundations_logic/pr-description.md`

**Verification**:
- "16 files" appears consistently throughout
- "3,704" appears as total
- DeductionHelpers.lean has a row in the File Inventory
- CI validation note present in Verification section

---

### Phase 2: Fix ROADMAP.md project structure diagram [COMPLETED]

**Goal**: Remove stale `Reasoning.lean` entry and add `DeductionHelpers.lean`.

**Tasks**:
- [ ] Remove the `Reasoning.lean` line from the project structure diagram
- [ ] Add `DeductionHelpers.lean` under the `Foundations/Logic/Metalogic/` section
- [ ] Add `Foundations/Data/ListHelpers.lean` if the diagram covers Foundations/ broadly (check scope)

**Timing**: 10 minutes

**Depends on**: none

**Files to modify**:
- `specs/ROADMAP.md`

**Verification**:
- `grep -n "Reasoning.lean" specs/ROADMAP.md` returns no results
- `grep -n "DeductionHelpers" specs/ROADMAP.md` returns the new entry

## Testing & Validation

- [ ] All "15 files" references changed to "16 files"
- [ ] Total is "3,704" (not 3,708 or 3,822)
- [ ] DeductionHelpers.lean in File Inventory with camelCase def names
- [ ] CI validation compliance noted in Verification
- [ ] Reasoning.lean removed from ROADMAP.md
- [ ] DeductionHelpers.lean added to ROADMAP.md

## Artifacts & Outputs

- `specs/059_pr1_foundations_logic/pr-description.md` (updated)
- `specs/ROADMAP.md` (updated)

## Rollback/Contingency

Both files under git. Revert with: `git checkout HEAD -- specs/059_pr1_foundations_logic/pr-description.md specs/ROADMAP.md`
