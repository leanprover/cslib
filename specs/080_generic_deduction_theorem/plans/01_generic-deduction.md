# Implementation Plan: Task #80

- **Task**: 80 - Generic DeductionTheorem interface
- **Status**: [COMPLETED]
- **Effort**: 5 hours
- **Dependencies**: Task 78 (completed), Task 79 (completed)
- **Research Inputs**: specs/080_generic_deduction_theorem/reports/01_team-research.md
- **Artifacts**: plans/01_generic-deduction.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

Currently each of the 4 DeductionTheorem files (PL, Modal, Temporal, Bimodal; 952 lines total) duplicates 4 purely-constructive helper lemmas that encode the K/S axiom manipulation at the heart of the deduction theorem. This plan creates a `HasHilbertTree` typeclass in `Foundations/Logic/Metalogic/DeductionHelpers.lean` with 6 fields (Tree, implyK, implyS, assumption, mp, weakening), implements the 4 generic helper lemmas once, then refactors each logic to instantiate the typeclass and call the generic helpers. Per-logic `deduction_with_mem` and `deduction_theorem` remain concrete (native `match`, native `termination_by`) since Lean 4 cannot pattern-match through typeclass abstraction. Definition of done: `lake build` passes, each logic's `*_has_deduction_theorem` still connects to the MCS framework, and the 4 helper lemmas are sourced from exactly one file.

### Research Integration

Key findings from the team research report (01_team-research.md):
- Full generic deduction theorem is infeasible (pattern matching and termination checker cannot operate through typeclass abstraction).
- The 4 helper lemmas are purely constructive (build trees, never pattern match), making them ideal for abstraction.
- Axiom naming is semantically swapped: PL/Modal use `.implyK`/`.implyS` while Temporal/Bimodal use `.imp_s`/`.imp_k` (where `.imp_s` is K and `.imp_k` is S). Task 79 did not harmonize this.
- Height lemma names differ: Bimodal uses `mp_height_gt_left`/`subderiv_height_lt` vs PL/Modal/Temporal `height_modus_ponens_left`/`height_weakening`.
- Bimodal uses `{fc : FrameClass}` polymorphism and extra `h_fc` parameter on `.axiom` constructor. Temporal hardcodes `FrameClass.Base`.
- Bimodal's `deduction_assumption_same` calls `identity` from Perpetuity/Helpers instead of building S/K/K inline.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task does not directly correspond to a specific ROADMAP.md remaining item, but it advances the "Abstract shared completeness infrastructure" goal by establishing the shared deduction helper pattern that future metalogic abstractions can build upon.

## Goals & Non-Goals

**Goals**:
- Create `HasHilbertTree` typeclass with 6 fields in `Foundations/Logic/Metalogic/DeductionHelpers.lean`
- Implement 4 generic helper lemmas (`deduction_axiom`, `deduction_imp_self`, `deduction_assumption_other`, `deduction_mp_under_imp`) once
- Add `HasHilbertTree` instances for all 4 logics
- Refactor each logic's `deduction_with_mem` and `deduction_theorem` to call generic helpers
- Remove per-logic duplicate helper definitions
- Maintain `lake build` passing at each phase

**Non-Goals**:
- Harmonize axiom naming across logics (`.implyK` vs `.imp_s` etc.) -- this is orthogonal and would be a separate task
- Harmonize height lemma naming across logics
- Abstract `deduction_with_mem` or `deduction_theorem` themselves (requires pattern matching on concrete types)
- Modify any `DerivationTree` inductive types
- Change the MCS framework connection (`*_has_deduction_theorem` instances)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Typeclass resolution issues with `HasImp` in generic context | M | M | Start with PL/Modal (simpler, no FrameClass) to validate design before tackling Temporal/Bimodal |
| `noncomputable` propagation through typeclass methods | L | M | Generic helpers are already `noncomputable`; per-logic code stays `noncomputable` too |
| Temporal/Bimodal FrameClass parameter incompatible with generic typeclass | H | M | The typeclass is parameterized by formula type F only; each instance fixes its own Tree type (e.g., `DerivationTree FrameClass.Base`). Bimodal may need universe-polymorphic treatment or FrameClass-specific instance. |
| Bimodal's `identity` call in `deduction_assumption_same` diverges from generic `deduction_imp_self` | L | L | The generic `deduction_imp_self` builds A->A from S/K/K; Bimodal can either use the generic version or keep its `identity` call as a minor local override |
| Build regression from import changes | M | L | Verify `lake build` after each phase |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Assess Prerequisites and Create HasHilbertTree Typeclass [COMPLETED]

**Goal**: Verify axiom naming status, then create the `HasHilbertTree` typeclass and 4 generic helper lemmas in a new file.

**Tasks**:
- [x] Audit axiom naming: confirm PL/Modal use `.implyK`/`.implyS` and Temporal/Bimodal use `.imp_s`/`.imp_k` with swapped semantics. Document the mapping for use in instances. *(completed)*
- [x] Audit subset notation: confirm PL/Modal use `fun x h => nomatch h` for empty subset and Temporal/Bimodal use `List.nil_subset _`. *(completed)*
- [x] Create `Cslib/Foundations/Logic/Metalogic/DeductionHelpers.lean` with:
  - `HasHilbertTree` typeclass: 6 fields (`Tree`, `implyK`, `implyS`, `assumption`, `mp`, `weakening`). The `Tree` field is parameterized by `List F -> F -> Type*`. The `weakening` field uses the forall-style subset proof `(forall x in Gamma, x in Delta)` which is compatible with both PL/Modal and Temporal/Bimodal (the latter use `List.Subset` which unfolds to this).
  - `deduction_axiom` generic helper *(deviation: altered — takes `d_empty : Tree [] φ` instead of `h_ax` parameter, so each logic builds the empty-context derivation before calling)*
  - `deduction_imp_self` generic helper
  - `deduction_assumption_other` generic helper
  - `deduction_mp_under_imp` generic helper
- [x] Verify the new file compiles with `lake build Cslib.Foundations.Logic.Metalogic.DeductionHelpers` *(completed)*

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/Metalogic/DeductionHelpers.lean` - NEW file

**Verification**:
- `lake build Cslib.Foundations.Logic.Metalogic.DeductionHelpers` passes
- File exports 4 generic lemmas and 1 typeclass

---

### Phase 2: Refactor PL and Modal DeductionTheorem [COMPLETED]

**Goal**: Add `HasHilbertTree` instances for PL and Modal, replace their per-logic helper defs with calls to generic helpers.

**Tasks**:
- [x] In `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean`: *(completed)*
  - Add import for `DeductionHelpers`
  - Add `HasHilbertTree (PL.Proposition Atom)` instance mapping `.implyK`/`.implyS` to typeclass fields
  - Replace 4 per-logic helper defs with generic calls, remove duplicates
  - `deduction_with_mem` and `deduction_theorem` retain native match/termination_by
- [x] In `Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean`: *(completed)*
  - Same refactoring as PL (Modal uses identical naming: `.implyK`, `.implyS`)
  - Add `HasHilbertTree (Proposition Atom)` instance
  - Replace helper defs with generic calls, remove duplicates
- [x] Run `lake build` for both modules *(completed, both pass)*

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean` - refactor helpers to generic
- `Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean` - refactor helpers to generic

**Verification**:
- Both files compile
- `prop_has_deduction_theorem` and `modal_has_deduction_theorem` still exist and compile
- Per-logic helper definitions are removed

---

### Phase 3: Refactor Temporal DeductionTheorem [COMPLETED]

**Goal**: Add `HasHilbertTree` instance for Temporal, replace helpers with generic calls. This is separate from Phase 2 because Temporal has different axiom naming (`.imp_s`/`.imp_k` swapped) and uses `FrameClass.Base` hardcoded.

**Tasks**:
- [x] In `Cslib/Logics/Temporal/Metalogic/DeductionTheorem.lean`: *(completed)*
  - Add import for `DeductionHelpers`
  - Add `HasHilbertTree (Formula Atom)` instance mapping `.imp_s` -> `implyK`, `.imp_k` -> `implyS`
  - Replace 4 per-logic helpers with generic calls
  - Axiom case bridges by building `.axiom [] ψ h_ax h_fc` inline as empty-context derivation *(deviation: altered — no separate bridge function needed, inline construction suffices)*
  - `deduction_with_mem` and `deduction_theorem` retain native match/termination_by
- [x] Run `lake build Cslib.Logics.Temporal.Metalogic.DeductionTheorem` *(completed, passes)*

**Timing**: 1 hour

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/DeductionTheorem.lean` - refactor helpers to generic

**Verification**:
- File compiles
- `temporal_has_deduction_theorem` still exists and compiles
- Per-logic helper definitions are removed (except any thin bridge for axiom case)

---

### Phase 4: Refactor Bimodal DeductionTheorem [COMPLETED]

**Goal**: Add `HasHilbertTree` instance for Bimodal, replace helpers with generic calls. Bimodal is most complex: uses `{fc : FrameClass}` polymorphism, has `weaken_under_imp`/`weaken_under_imp_ctx` extra helpers, and calls `identity` from Perpetuity/Helpers.

**Tasks**:
- [x] In `Cslib/Logics/Bimodal/Metalogic/Core/DeductionTheorem.lean`: *(completed)*
  - Add import for `DeductionHelpers`
  - Created `@[reducible] def bimodalHilbertTree (fc : FrameClass)` as a function rather than instance (option (a) adapted — uses `letI` in proofs for fc-polymorphic resolution)
  - Map axiom names: `.imp_s` -> implyK, `.imp_k` -> implyS
  - Replace 6 per-logic helpers (`weaken_under_imp`, `weaken_under_imp_ctx`, `deduction_axiom`, `deduction_assumption_same`, `deduction_assumption_other`, `deduction_mp`) with generic calls
  - `deduction_assumption_same` now uses generic `deduction_imp_self` instead of `identity` from Perpetuity *(deviation: altered — `identity` import removed, `deduction_imp_self` builds A->A from S/K/K)*
- [x] Run `lake build Cslib.Logics.Bimodal.Metalogic.Core.DeductionTheorem` *(completed, passes)*

**Timing**: 1 hour

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Core/DeductionTheorem.lean` - refactor helpers to generic

**Verification**:
- File compiles
- `bimodal_has_deduction_theorem` still exists and compiles
- `weaken_under_imp`, `weaken_under_imp_ctx`, per-logic helper definitions are removed
- No regressions in downstream Bimodal modules

---

### Phase 5: Full Build Verification and Cleanup [COMPLETED]

**Goal**: Run full `lake build`, fix any downstream breakage, verify the refactoring is complete and clean.

**Tasks**:
- [x] Run `lake build` for the entire project *(completed — 2915 jobs, passes)*
- [x] Fix any downstream compilation errors *(none needed, all downstream modules compile)*
- [x] Verify each `*_has_deduction_theorem` instance is still present and functional:
  - `prop_has_deduction_theorem` *(verified)*
  - `modal_has_deduction_theorem` *(verified)*
  - `temporal_has_deduction_theorem` *(verified)*
  - `bimodal_has_deduction_theorem` *(verified)*
- [x] Verify no `sorry` was introduced *(0 sorries in modified files)*
- [x] Count lines to confirm savings *(171 lines removed from 4 existing files, +119 in new shared file = net -52 lines. The 4 helper lemmas are now defined once instead of 4 times.)*
- [x] Ensure `DeductionHelpers.lean` is properly listed in any module root files if needed *(no separate module root needed — imported directly by each DeductionTheorem file)*

**Timing**: 0.5 hours

**Depends on**: 4

**Files to modify**:
- Any files with downstream compilation errors (if any)
- Module root files (if `DeductionHelpers.lean` needs to be added to imports)

**Verification**:
- `lake build` passes with zero errors
- No `sorry` in any modified file
- All 4 `*_has_deduction_theorem` instances compile
- Net line reduction is approximately 100-130 lines

## Testing & Validation

- [ ] `lake build` passes after each phase (scoped builds) and at end (full build)
- [ ] All 4 `*_has_deduction_theorem` instances still compile and connect to MCS framework
- [ ] No `sorry` introduced anywhere
- [ ] Generic helpers in `DeductionHelpers.lean` have no `sorry`
- [ ] Each logic's `deduction_with_mem` and `deduction_theorem` retain native `match` and `termination_by`
- [ ] Downstream modules (MCS, Soundness, Completeness) still compile

## Artifacts & Outputs

- `Cslib/Foundations/Logic/Metalogic/DeductionHelpers.lean` - NEW: HasHilbertTree typeclass + 4 generic helpers
- `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean` - MODIFIED: uses generic helpers
- `Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean` - MODIFIED: uses generic helpers
- `Cslib/Logics/Temporal/Metalogic/DeductionTheorem.lean` - MODIFIED: uses generic helpers
- `Cslib/Logics/Bimodal/Metalogic/Core/DeductionTheorem.lean` - MODIFIED: uses generic helpers

## Rollback/Contingency

All changes are additive (new file) plus modifications to existing files. If any phase fails:
- The new `DeductionHelpers.lean` is standalone and can be kept even if per-logic refactoring is reverted.
- Each phase modifies one or two files. Reverting a single phase means restoring the original file from git while keeping the generic file and earlier phases' work.
- Worst case: `git checkout -- Cslib/Logics/*/Metalogic/DeductionTheorem.lean Cslib/Logics/Bimodal/Metalogic/Core/DeductionTheorem.lean` to restore all originals.
