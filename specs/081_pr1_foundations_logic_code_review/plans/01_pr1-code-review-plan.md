# Implementation Plan: Task #81

- **Task**: 81 - Review PR 1 Foundations Logic code quality for infrastructure, organization, naming, and proof improvements
- **Status**: [NOT STARTED]
- **Effort**: 4 hours
- **Dependencies**: Task 79 (deduplication audit)
- **Research Inputs**: specs/081_pr1_foundations_logic_code_review/reports/01_pr1-code-review.md
- **Artifacts**: plans/01_pr1-code-review-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

Implement 13 resolved code quality improvements from the PR 1 Foundations Logic code review. Changes span formatting cleanup, import trimming, file relocation, coordinated renames, axiom variable reordering, abbreviation usage, and documentation additions across `Cslib/Foundations/Logic/` (16 files) with downstream impacts in `Cslib/Logics/` (Bimodal, Modal, Temporal, Propositional). All decisions are resolved in the research report -- this plan executes them directly.

### Research Integration

The research report at `specs/081_pr1_foundations_logic_code_review/reports/01_pr1-code-review.md` identified 13 action items and 5 "kept as-is" items. All ambiguities were resolved with specific file/line references and exact edit instructions. Items range from simple single-line edits (items 3, 4, 5, 6, 12) to coordinated multi-file renames (items 8, 10) and structural refactors (items 2, 9, 11).

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Implement all 13 code quality improvements from the review
- Maintain zero build errors (`lake build` passes after each phase)
- Improve naming consistency, readability, and code organization in Foundations/Logic

**Non-Goals**:
- Changing proof strategies or logic structure
- Modifying files outside the PR 1 scope (except downstream reference updates)
- Addressing the "kept as-is" items from the review

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Coordinated rename of theorem_flip/app1/app2 breaks downstream Bimodal/Logics files | H | M | Systematic grep-based rename with `lake build` verification |
| LeftMono/RightMono variable reordering breaks instance files | H | M | Update axiom defs, class defs, instance files, and theorem files atomically |
| diamond'/iff' abbreviation substitution changes proof behavior | M | L | Abbrevs are definitionally transparent; verify with `lake build` |
| ListHelpers move breaks import resolution | M | L | Update all 4 import paths and verify |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |
| 6 | 6 | 5 |

Phases are fully sequential because each rename/refactor may affect files touched by subsequent phases, and each phase requires a clean build before proceeding.

---

### Phase 1: Formatting and documentation cleanup (Items 3, 4, 5, 6, 12, 13) [NOT STARTED]

**Goal**: Fix all simple formatting issues, documentation, and comment cleanups that involve no name changes and no structural modifications.

**Tasks**:
- [ ] Item 3: Remove double blank lines in `Theorems/Modal/S5.lean` (6 locations) and `Theorems/Temporal/TemporalDerived.lean` (6 locations)
- [ ] Item 4: Remove `-- section` annotation from `end` lines in 7 files: `Combinators.lean`, `Propositional/Core.lean`, `Propositional/Connectives.lean`, `BigConj.lean`, `Modal/Basic.lean`, `Modal/S5.lean`, `Temporal/TemporalDerived.lean`
- [ ] Item 5: Replace empty docstring `/-! -/` in `InferenceSystem.lean` (line 11) with descriptive text: `/-! # Inference System Typeclass -/`
- [ ] Item 6: Replace draft docstring in `Theorems/Propositional/Connectives.lean` (lines 279-290) with one-line: `/-- De Morgan 1 backward: ⊢ (¬φ ∨ ¬ψ) → ¬(φ ∧ ψ). -/`
- [ ] Item 12: Add triviality note to `FUntilEquiv` docstring in `Axioms.lean` (line 269)
- [ ] Item 13: Add section comments within the `theorem_app2` proof in `Combinators.lean` (lines 139-265) marking major milestones
- [ ] Run `lake build` to verify

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/Theorems/Modal/S5.lean` - Remove double blank lines
- `Cslib/Foundations/Logic/Theorems/Temporal/TemporalDerived.lean` - Remove double blank lines, remove `-- section`
- `Cslib/Foundations/Logic/Theorems/Combinators.lean` - Remove `-- section`, add proof comments
- `Cslib/Foundations/Logic/Theorems/Propositional/Core.lean` - Remove `-- section`
- `Cslib/Foundations/Logic/Theorems/Propositional/Connectives.lean` - Remove `-- section`, fix docstring
- `Cslib/Foundations/Logic/Theorems/BigConj.lean` - Remove `-- section`
- `Cslib/Foundations/Logic/Theorems/Modal/Basic.lean` - Remove `-- section`
- `Cslib/Foundations/Logic/InferenceSystem.lean` - Fix empty docstring
- `Cslib/Foundations/Logic/Axioms.lean` - Add FUntilEquiv note

**Verification**:
- `lake build` passes with zero errors
- No double blank lines remain in S5.lean or TemporalDerived.lean
- No `end -- section` patterns remain

---

### Phase 2: Move ListHelpers to Foundations/Data/ (Item 2) [NOT STARTED]

**Goal**: Relocate the pure list utility file from Logic/Helpers/ to a more appropriate Data/ location.

**Tasks**:
- [ ] Create directory `Cslib/Foundations/Data/` if it does not exist
- [ ] Move `Cslib/Foundations/Logic/Helpers/ListHelpers.lean` to `Cslib/Foundations/Data/ListHelpers.lean`
- [ ] Update the `module` declaration in the file from `Cslib.Foundations.Logic.Helpers.ListHelpers` to `Cslib.Foundations.Data.ListHelpers`
- [ ] Update import in `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean`: change `Cslib.Foundations.Logic.Helpers.ListHelpers` to `Cslib.Foundations.Data.ListHelpers`
- [ ] Update import in `Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean`: same change
- [ ] Update import in `Cslib/Logics/Temporal/Metalogic/DeductionTheorem.lean`: same change
- [ ] Update import in `Cslib/Logics/Bimodal/Metalogic/Core/DeductionTheorem.lean`: same change
- [ ] Run `lake exe mk_all` to update `Cslib.lean`
- [ ] Remove the now-empty `Cslib/Foundations/Logic/Helpers/` directory
- [ ] Run `lake build` to verify

**Timing**: 0.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Foundations/Logic/Helpers/ListHelpers.lean` - Move to new location
- `Cslib/Foundations/Data/ListHelpers.lean` - New file (moved)
- `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean` - Update import path
- `Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean` - Update import path
- `Cslib/Logics/Temporal/Metalogic/DeductionTheorem.lean` - Update import path
- `Cslib/Logics/Bimodal/Metalogic/Core/DeductionTheorem.lean` - Update import path

**Verification**:
- `lake build` passes
- Old path no longer exists
- All 4 DeductionTheorem files import from new path

---

### Phase 3: Trim redundant imports (Item 1) [NOT STARTED]

**Goal**: Remove imports that are already transitively available through other imports.

**Tasks**:
- [ ] `ProofSystem.lean`: Remove `public import Cslib.Init` and `public import Cslib.Foundations.Logic.Connectives` (both available via Axioms)
- [ ] `Axioms.lean`: Remove `public import Cslib.Init` (available via Connectives)
- [ ] `Modal/Basic.lean`: Remove `public import Cslib.Foundations.Logic.ProofSystem` (available via Combinators)
- [ ] `Modal/S5.lean`: Remove `public import Cslib.Foundations.Logic.ProofSystem` (available via Combinators); test if `Combinators`, `Core`, and `Connectives` can also be trimmed (available via Modal.Basic)
- [ ] Run `lake build` to verify each removal does not break anything
- [ ] If any removal breaks the build, revert that specific removal

**Timing**: 0.5 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Foundations/Logic/ProofSystem.lean` - Remove 2 redundant imports
- `Cslib/Foundations/Logic/Axioms.lean` - Remove 1 redundant import
- `Cslib/Foundations/Logic/Theorems/Modal/Basic.lean` - Remove 1 redundant import
- `Cslib/Foundations/Logic/Theorems/Modal/S5.lean` - Remove 1+ redundant imports

**Verification**:
- `lake build` passes
- Each removed import was genuinely transitively available

---

### Phase 4: Coordinated rename theorem_flip/app1/app2 and G_imp_trans'/H_imp_trans' (Items 8, 10) [NOT STARTED]

**Goal**: Rename `theorem_flip` to `flip`, `theorem_app1` to `app1`, `theorem_app2` to `app2` in Foundations and propagate to all downstream references. Also rename `G_imp_trans'` to `G_imp_trans` and `H_imp_trans'` to `H_imp_trans`.

**Tasks**:
- [ ] In `Cslib/Foundations/Logic/Theorems/Combinators.lean`: rename definitions `theorem_flip` -> `flip`, `theorem_app1` -> `app1`, `theorem_app2` -> `app2`; update all internal references and docstring mentions
- [ ] In `Cslib/Foundations/Logic/Theorems/Propositional/Core.lean`: update 3 references to `theorem_flip`
- [ ] In `Cslib/Foundations/Logic/Theorems/Propositional/Connectives.lean`: update 5 references (including comment on line 362)
- [ ] In `Cslib/Foundations/Logic/Theorems/Modal/S5.lean`: update 3 references to `theorem_flip`
- [ ] In `Cslib/Foundations/Logic/Theorems/Temporal/TemporalDerived.lean`: update 2 references to `theorem_flip`; rename `G_imp_trans'` -> `G_imp_trans` (line 239) and `H_imp_trans'` -> `H_imp_trans` (line 258)
- [ ] In `Cslib/Logics/Bimodal/Theorems/Combinators.lean`: update 9 references (3 definition names + 6 `_root_` qualified references)
- [ ] In `Cslib/Logics/Bimodal/Theorems/Propositional/Core.lean`: update 3 references to `theorem_flip`
- [ ] In `Cslib/Logics/Bimodal/Theorems/TemporalDerived.lean`: update 1 reference to `theorem_flip`; update 2 `_root_` references to `G_imp_trans'`/`H_imp_trans'`
- [ ] In `Cslib/Logics/Bimodal/Metalogic/Algebraic/LindenbaumQuotient.lean`: update 2 references to `theorem_flip`
- [ ] In `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/PointInsertion.lean`: update 3 references to `theorem_flip`
- [ ] Run comprehensive grep to confirm zero remaining `theorem_flip`, `theorem_app1`, `theorem_app2`, `G_imp_trans'`, `H_imp_trans'` references
- [ ] Run `lake build` to verify

**Timing**: 1 hour

**Depends on**: 3

**Files to modify**:
- `Cslib/Foundations/Logic/Theorems/Combinators.lean` - Rename 3 definitions + internal refs
- `Cslib/Foundations/Logic/Theorems/Propositional/Core.lean` - Update refs
- `Cslib/Foundations/Logic/Theorems/Propositional/Connectives.lean` - Update refs
- `Cslib/Foundations/Logic/Theorems/Modal/S5.lean` - Update refs
- `Cslib/Foundations/Logic/Theorems/Temporal/TemporalDerived.lean` - Update refs + rename G/H_imp_trans'
- `Cslib/Logics/Bimodal/Theorems/Combinators.lean` - Update defs + _root_ refs
- `Cslib/Logics/Bimodal/Theorems/Propositional/Core.lean` - Update refs
- `Cslib/Logics/Bimodal/Theorems/TemporalDerived.lean` - Update refs
- `Cslib/Logics/Bimodal/Metalogic/Algebraic/LindenbaumQuotient.lean` - Update refs
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/PointInsertion.lean` - Update refs

**Verification**:
- `grep -rn "theorem_flip\|theorem_app1\|theorem_app2\|G_imp_trans'\|H_imp_trans'" Cslib/` returns zero results
- `lake build` passes

---

### Phase 5: Align LeftMono/RightMono variable ordering and standardize S5.lean variables (Items 9, 7) [NOT STARTED]

**Goal**: Align `LeftMonoUntilG` and `LeftMonoSinceH` variable ordering from `(φ χ ψ)` to `(φ ψ χ)` for consistency with `RightMonoUntil`/`RightMonoSince`. Also rename `A B` to `φ ψ` in 4 S5.lean theorem signatures.

**Tasks**:
- [ ] In `Cslib/Foundations/Logic/Axioms.lean`: reorder `LeftMonoUntilG (φ χ ψ : F)` to `LeftMonoUntilG (φ ψ χ : F)` and update the body (swap `χ` and `ψ` roles); same for `LeftMonoSinceH`
- [ ] In `Cslib/Foundations/Logic/ProofSystem.lean`: update `HasAxiomLeftMonoUntilG.leftMonoUntilG {φ χ ψ}` to `{φ ψ χ}` and the `Axioms.LeftMonoUntilG φ χ ψ` call to `Axioms.LeftMonoUntilG φ ψ χ`; same for `HasAxiomLeftMonoSinceH`
- [ ] In `Cslib/Foundations/Logic/Theorems/Temporal/TemporalDerived.lean`: update the LeftMono theorem references (lines 48-54) to match new variable ordering
- [ ] In `Cslib/Logics/Temporal/ProofSystem/Instances.lean`: update `HasAxiomLeftMonoUntilG` and `HasAxiomLeftMonoSinceH` instance definitions if they reference specific variable positions
- [ ] In `Cslib/Logics/Bimodal/ProofSystem/Instances.lean`: update same instances
- [ ] In `Cslib/Foundations/Logic/Theorems/Modal/S5.lean`: rename `{A B : F}` to `{φ ψ : F}` at lines 445, 503, 546; rename `{A : F}` to `{φ : F}` at line 513; update all `A`/`B` references in proof bodies to `φ`/`ψ`
- [ ] Run `lake build` to verify

**Timing**: 1 hour

**Depends on**: 4

**Files to modify**:
- `Cslib/Foundations/Logic/Axioms.lean` - Reorder 2 axiom variable lists
- `Cslib/Foundations/Logic/ProofSystem.lean` - Update 2 class definitions
- `Cslib/Foundations/Logic/Theorems/Temporal/TemporalDerived.lean` - Update LeftMono refs
- `Cslib/Logics/Temporal/ProofSystem/Instances.lean` - Update 2 instances
- `Cslib/Logics/Bimodal/ProofSystem/Instances.lean` - Update 2 instances
- `Cslib/Foundations/Logic/Theorems/Modal/S5.lean` - Rename A/B to phi/psi in 4 theorems

**Verification**:
- `lake build` passes
- All four LeftMono/RightMono axioms use consistent `(φ ψ χ)` ordering
- No `{A B : F}` or `{A : F}` patterns remain in S5.lean

---

### Phase 6: Refactor S5.lean to use diamond'/iff' abbreviations (Item 11) [NOT STARTED]

**Goal**: Replace expanded `HasImp.imp (HasBox.box (neg' φ)) HasBot.bot` patterns with the existing `diamond'` abbreviation, and `conj' (HasImp.imp a b) (HasImp.imp b a)` patterns with `iff'`, improving readability of theorem type signatures throughout S5.lean.

**Tasks**:
- [ ] Identify all theorem type signatures in S5.lean where `HasImp.imp (HasBox.box (neg' φ)) HasBot.bot` or `HasImp.imp (HasBox.box (HasImp.imp φ HasBot.bot)) HasBot.bot` appears; replace with `diamond' φ`
- [ ] Identify all theorem type signatures where the `iff'` pattern appears; replace with `iff' a b`
- [ ] Verify that `diamond'` and `iff'` abbreviations are definitionally equal to the expanded forms (they are `abbrev`, so this should be transparent)
- [ ] Run `lake build` to verify all proofs still work after substitution

**Timing**: 0.5 hours

**Depends on**: 5

**Files to modify**:
- `Cslib/Foundations/Logic/Theorems/Modal/S5.lean` - Replace expanded forms with abbreviations

**Verification**:
- `lake build` passes
- Theorem signatures are noticeably shorter and more readable
- `diamond'` and `iff'` abbreviations are used wherever the expanded pattern appeared

---

## Testing & Validation

- [ ] `lake build` passes after each phase (incremental verification)
- [ ] Final `lake build` passes with zero errors and zero warnings
- [ ] `grep -rn "theorem_flip\|theorem_app1\|theorem_app2" Cslib/` returns zero results
- [ ] `grep -rn "G_imp_trans'\|H_imp_trans'" Cslib/` returns zero results
- [ ] `grep -rn "end -- section" Cslib/Foundations/Logic/` returns zero results
- [ ] No double blank lines remain in S5.lean or TemporalDerived.lean
- [ ] `ListHelpers.lean` exists only at `Cslib/Foundations/Data/ListHelpers.lean`

## Artifacts & Outputs

- `specs/081_pr1_foundations_logic_code_review/plans/01_pr1-code-review-plan.md` (this file)
- `specs/081_pr1_foundations_logic_code_review/summaries/01_pr1-code-review-summary.md` (after implementation)

## Rollback/Contingency

All changes are additive edits to existing files (renames, formatting, import changes). Git provides full rollback capability via `git stash` or `git checkout` on any individual file. If a phase fails `lake build`, revert the specific edits from that phase and investigate. The sequential phase structure ensures each phase starts from a known-good build state.
