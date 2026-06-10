# Implementation Plan: Task #74

- **Task**: 74 - Polish PR1 code quality and update pr-description.md for publication
- **Status**: [NOT STARTED]
- **Effort**: 2.5 hours
- **Dependencies**: 68, 69, 71
- **Research Inputs**: specs/074_polish_pr1_quality_and_description/reports/01_polish-pr1-research.md
- **Artifacts**: plans/01_polish-pr1-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

This plan addresses five sub-issues to polish the Foundations/Logic PR1 before publication: removing double blank lines from 3 files, scoping `set_option linter.style.longLine false` per-theorem in 2 files, deduplicating `top'/neg'` abbreviations, adding the `module` keyword to Compatibility.lean, and updating the PR description with correct line counts and new documentation sections. Phases are ordered by dependency: simple formatting fixes first, then semantic changes, then PR description last (since it depends on final line counts).

### Research Integration

The research report (01_polish-pr1-research.md) provided exact line numbers for all double blank lines, identified 12 affected theorems across S5.lean (6) and TemporalDerived.lean (6) needing per-theorem `set_option ... in`, confirmed the `top'/neg'` abbreviation duplication between Axioms.lean and TemporalDerived.lean, identified the missing `module` keyword in Compatibility.lean, and computed the 10 file line count deltas for the PR description update.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task advances the PR1 submission milestone. The ROADMAP.md lists Foundations/Logic as a completed component -- this task polishes the PR for actual publication.

## Goals & Non-Goals

**Goals**:
- Remove double blank lines from Combinators.lean, Core.lean, and Basic.lean
- Replace file-scoped `set_option linter.style.longLine false` with per-theorem scoping in S5.lean and TemporalDerived.lean
- Deduplicate `top'/neg'` abbreviations by importing from Axioms.lean
- Fix top-level `lake build` by adding `module` keyword to Compatibility.lean
- Update pr-description.md with correct line counts, Embedding relocation section, and module keyword migration documentation

**Non-Goals**:
- Adding `let` abbreviations to shorten long lines (deferred; would require proof rework)
- Modifying any theorem logic or proof structure
- Addressing files outside the 5 sub-issues

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `open Cslib.Logic.Axioms` causes namespace collision | M | L | Check that `top'/neg'` resolve unambiguously after dedup; fallback is qualified references |
| Per-theorem `set_option ... in` does not suppress linter for multi-line theorem bodies | M | L | Lean 4 documents `set_option X in theorem ...` as scoped to the entire declaration; verified in existing codebase (e.g., `s4_diamond_box_conj` pattern) |
| `module` keyword on Compatibility.lean breaks downstream imports | M | L | Run full `lake build` after change; the file already has no dependents within PR1 scope |
| Line counts change between phases, invalidating Phase 5 | L | M | Run Phase 5 last; recount with `wc -l` at that point |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 3 | -- |
| 2 | 4 | 1, 2, 3 |
| 3 | 5 | 4 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Fix double blank lines [COMPLETED]

**Goal**: Remove the extra blank line between namespace declaration and `open` block in 3 files.

**Tasks**:
- [x] In `Cslib/Foundations/Logic/Theorems/Combinators.lean`: delete line 43 (empty line between L41 namespace and L44 open)
- [x] In `Cslib/Foundations/Logic/Theorems/Propositional/Core.lean`: delete line 44 (empty line between L42 namespace and L45 open)
- [x] In `Cslib/Foundations/Logic/Theorems/Modal/Basic.lean`: delete line 45 (empty line between L43 namespace and L46 open)

**Timing**: 10 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/Theorems/Combinators.lean` - remove 1 blank line at L43
- `Cslib/Foundations/Logic/Theorems/Propositional/Core.lean` - remove 1 blank line at L44
- `Cslib/Foundations/Logic/Theorems/Modal/Basic.lean` - remove 1 blank line at L45

**Verification**:
- Each file has exactly one blank line between namespace and open block
- `lake build Cslib.Foundations.Logic.Theorems.Combinators` passes
- `lake build Cslib.Foundations.Logic.Theorems.Propositional.Core` passes
- `lake build Cslib.Foundations.Logic.Theorems.Modal.Basic` passes

---

### Phase 2: Deduplicate `top'/neg'` abbreviations [NOT STARTED]

**Goal**: Remove local `top'/neg'` definitions from TemporalDerived.lean and import them from Axioms.lean instead.

**Tasks**:
- [ ] Add `open Cslib.Logic.Axioms` to the open block in TemporalDerived.lean (after line 31, before the variable declarations)
- [ ] Remove the local `abbrev neg'` definition (line 40)
- [ ] Remove the local `abbrev top'` definition (line 41)
- [ ] Verify that `someFuture`, `allFuture`, `somePast`, `allPast` still resolve `top'` and `neg'` correctly from the Axioms namespace

**Timing**: 15 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/Theorems/Temporal/TemporalDerived.lean` - add open, remove 2 abbrev lines

**Verification**:
- `lake build Cslib.Foundations.Logic.Theorems.Temporal.TemporalDerived` passes
- `grep -n "abbrev neg'" Cslib/Foundations/Logic/Theorems/Temporal/TemporalDerived.lean` returns nothing
- `grep -n "abbrev top'" Cslib/Foundations/Logic/Theorems/Temporal/TemporalDerived.lean` returns nothing
- `grep -n "open Cslib.Logic.Axioms" Cslib/Foundations/Logic/Theorems/Temporal/TemporalDerived.lean` returns the new open line

---

### Phase 3: Scope `set_option linter.style.longLine false` per-theorem [NOT STARTED]

**Goal**: Replace file-scoped `set_option` with per-theorem `set_option ... in` in both S5.lean and TemporalDerived.lean.

**Tasks**:

**S5.lean** (6 theorems):
- [ ] Remove file-scoped `set_option linter.style.longLine false` at line 58
- [ ] Add `set_option linter.style.longLine false in` before `theorem t_box_to_diamond` (L173)
- [ ] Add `set_option linter.style.longLine false in` before `theorem box_disj_intro` (L234)
- [ ] Add `set_option linter.style.longLine false in` before `theorem box_conj_iff` (L259)
- [ ] Add `set_option linter.style.longLine false in` before `theorem diamond_disj_iff` (L312)
- [ ] Add `set_option linter.style.longLine false in` before `theorem s4_diamond_box_conj` (L400)
- [ ] Add `set_option linter.style.longLine false in` before `theorem s5_diamond_conj_diamond` (L499)

**TemporalDerived.lean** (6 theorems):
- [ ] Remove file-scoped `set_option linter.style.longLine false` at line 24
- [ ] Add `set_option linter.style.longLine false in` before `private theorem neg_contrapositive_imp_neg` (L127)
- [ ] Add `set_option linter.style.longLine false in` before `theorem G_and_intro` (L212)
- [ ] Add `set_option linter.style.longLine false in` before `theorem H_and_intro` (L220)
- [ ] Add `set_option linter.style.longLine false in` before `theorem G_imp_trans'` (L230)
- [ ] Add `set_option linter.style.longLine false in` before `theorem H_imp_trans'` (L245)
- [ ] Add `set_option linter.style.longLine false in` before `theorem connect_future_G` (L261)

**Timing**: 45 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/Theorems/Modal/S5.lean` - remove 1 file-scoped set_option, add 6 per-theorem set_option
- `Cslib/Foundations/Logic/Theorems/Temporal/TemporalDerived.lean` - remove 1 file-scoped set_option, add 6 per-theorem set_option

**Verification**:
- `lake build Cslib.Foundations.Logic.Theorems.Modal.S5` passes with zero long-line warnings
- `lake build Cslib.Foundations.Logic.Theorems.Temporal.TemporalDerived` passes with zero long-line warnings
- `grep -c "set_option linter.style.longLine false in" Cslib/Foundations/Logic/Theorems/Modal/S5.lean` returns 6
- `grep -c "set_option linter.style.longLine false in" Cslib/Foundations/Logic/Theorems/Temporal/TemporalDerived.lean` returns 6
- No file-scoped `set_option linter.style.longLine false` (without trailing `in`) remains in either file

---

### Phase 4: Add `module` keyword to Compatibility.lean [NOT STARTED]

**Goal**: Fix the top-level `lake build` error by adding `module` keyword and `@[expose] public section` to Compatibility.lean.

**Tasks**:
- [ ] Add `module` keyword after the copyright header comment block (between the header and the import lines)
- [ ] Convert `import Cslib.Logics.Bimodal.FrameConditions.Soundness` to `public import ...`
- [ ] Convert `import Cslib.Logics.Bimodal.ProofSystem.Axioms` to `public import ...`
- [ ] Add `@[expose] public section` before the namespace declaration (before line 18)
- [ ] Add `end` at end of file to close the section (if not already present)

**Timing**: 20 minutes

**Depends on**: 1, 2, 3

**Files to modify**:
- `Cslib/Logics/Bimodal/FrameConditions/Compatibility.lean` - add module keyword, public imports, section wrapper

**Verification**:
- `lake build` (full project) passes with zero errors
- `grep -n "^module" Cslib/Logics/Bimodal/FrameConditions/Compatibility.lean` shows the module keyword
- The error `cannot import non-module ... from module` no longer appears

---

### Phase 5: Update PR description [NOT STARTED]

**Goal**: Update pr-description.md with correct line counts, new Embedding relocation section, and module keyword migration documentation.

**Tasks**:

**Line count updates** (recount all files with `wc -l` at this point since phases 1-3 may change counts):
- [ ] Recount all 15 files with `wc -l` to get post-edit line counts
- [ ] Update the summary paragraph (line 7): change "3,621 lines total" to the actual total
- [ ] Update individual line counts in the File Inventory table for each file that changed

**Expected line count changes from prior tasks** (to be verified):
| File | Current PR Description | Current Actual | Post-Phase Delta |
|------|----------------------:|---------------:|-----------------:|
| `Combinators.lean` | 330 | 334 | -1 (Phase 1) |
| `Core.lean` | 285 | 289 | -1 (Phase 1) |
| `Basic.lean` | 200 | 204 | -1 (Phase 1) |
| `S5.lean` | 585 | 589 | +5 (Phase 3: -1 remove, +6 add) |
| `TemporalDerived.lean` | 270 | 274 | +3 (Phase 2: -2 remove abbrevs, Phase 3: -1 remove, +6 add) |
| `Connectives.lean` | 545 | 546 | 0 |
| `BigConj.lean` | 136 | 141 | 0 |
| `FrameConditions.lean` | 84 | 89 | 0 |
| `Consistency.lean` | 273 | 277 | 0 |

- [ ] Update each changed file's line count in the table
- [ ] Recalculate and update the total

**New sections to add**:
- [ ] Add "Embedding Relocation (Tasks 72-73)" section after the Verification section, documenting:
  - `Propositional/Embedding.lean` merged into `Bimodal/Embedding/PropositionalEmbedding.lean` (task 72)
  - `Modal/FromPropositional.lean` and `Temporal/FromPropositional.lean` created (task 73)
  - The clean import hierarchy: Propositional -> {Modal, Temporal} -> Bimodal
  - Note these files are outside Foundations/Logic/ scope but establish the dependency structure
- [ ] Add "Module Keyword Migration (Task 68)" section (or integrate into Verification), documenting:
  - All 15 files now have `module` keyword and `@[expose] public section`
  - All imports converted to `public import`
  - This was required for Lean 4 module system compliance

**Known Issues updates**:
- [ ] Update the long-line suppressions bullet: change "file-scoped ... Scoping to individual theorems is deferred" to "per-theorem scoped via `set_option ... in`"
- [ ] Remove or update any other bullets that are now resolved

**Timing**: 45 minutes

**Depends on**: 1, 2, 3, 4

**Files to modify**:
- `specs/059_pr1_foundations_logic/pr-description.md` - update line counts, add 2 new sections, update Known Issues

**Verification**:
- All line counts in the File Inventory table match `wc -l` output
- Summary paragraph total matches table total
- No references to "deferred" long-line scoping remain
- New Embedding and Module sections are present

---

## Testing & Validation

- [ ] `lake build` passes with zero errors after all phases
- [ ] No file-scoped `set_option linter.style.longLine false` remains in S5.lean or TemporalDerived.lean
- [ ] No duplicate `top'/neg'` abbreviations in TemporalDerived.lean
- [ ] No double blank lines in Combinators.lean, Core.lean, or Basic.lean
- [ ] All line counts in pr-description.md match `wc -l` output
- [ ] `grep -rn "sorry" Cslib/Foundations/Logic/` returns zero hits (unchanged)

## Artifacts & Outputs

- `specs/074_polish_pr1_quality_and_description/plans/01_polish-pr1-plan.md` (this file)
- Modified Lean source files (3 blank-line fixes + 2 set_option scoping + 1 dedup + 1 module keyword)
- Updated `specs/059_pr1_foundations_logic/pr-description.md`

## Rollback/Contingency

All changes are isolated edits to individual files. If any phase causes build failures:
- Phase 1: Restore blank lines (trivial, no semantic impact)
- Phase 2: Restore local `top'/neg'` and remove `open Cslib.Logic.Axioms`
- Phase 3: Restore file-scoped `set_option` and remove per-theorem directives
- Phase 4: Remove `module` keyword and revert to non-public imports
- Phase 5: Revert pr-description.md from git

Git provides file-level rollback via `git checkout -- <file>` for any phase.
