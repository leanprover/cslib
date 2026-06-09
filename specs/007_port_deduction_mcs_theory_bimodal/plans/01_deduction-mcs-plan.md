# Implementation Plan: Task #7 -- Port Deduction Infrastructure and MCS Theory

- **Task**: 7 - Port Deduction Infrastructure and MCS Theory to Bimodal Metalogic
- **Status**: [NOT STARTED]
- **Effort**: 5 hours
- **Dependencies**: Tasks 4 (ProofSystem), 5 (Theorems/Perpetuity), 29 (generic MCS)
- **Research Inputs**: specs/007_port_deduction_mcs_theory_bimodal/reports/01_deduction-mcs-research.md
- **Artifacts**: plans/01_deduction-mcs-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

Port the core metalogic infrastructure (DeductionTheorem, MaximalConsistent, MCSProperties) from BimodalLogic to `Cslib/Logics/Bimodal/Metalogic/Core/`. This establishes the deduction theorem and maximal consistent set theory needed by the completeness proof (task 8), decidability (task 9), and separation (task 10). The porting follows the temporal metalogic pattern (task 31): create a `bimodalDerivationSystem` instance connecting to the generic MCS framework from `Cslib/Foundations/Logic/Metalogic/Consistency.lean`, prove the bimodal deduction theorem by well-founded recursion on the 7-constructor `DerivationTree`, and derive MCS closure properties. RestrictedMCS is deferred (unmet dependencies on SubformulaClosure and Bundle modules).

### Research Integration

Key findings from the research report integrated into this plan:

1. **Three core files are portable**: DeductionTheorem (441 lines), MaximalConsistent (528 lines), and MCSProperties (366 lines) have all dependencies satisfied by completed tasks 4, 5, and 29.
2. **RestrictedMCS deferred**: Both Basic.lean (653 lines) and Deferral.lean (764 lines) depend on unported SubformulaClosure.NestingDepth, Bundle.CanonicalTaskRelation, and Bundle.SuccExistence modules. These belong to a later completeness infrastructure task.
3. **Generic MCS framework reuse**: Following the temporal pattern, instantiate `bimodalDerivationSystem` and delegate ~150 lines of generic lemmas (Lindenbaum, chain union, closure) to the foundations layer.
4. **Missing prerequisite**: `subderiv_height_lt` must be added to `Derivation.lean` (3 lines) for the weakening case termination proof.
5. **Axiom name translations**: `prop_s` -> `imp_s`, `prop_k` -> `imp_k`, `ex_falso` -> `efq`.
6. **Namespace**: cslib uses `Cslib.Logic.Bimodal` (not `Cslib.Logics.Bimodal` despite the file path under `Logics/`).

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This plan advances Phase 5 (Bimodal Porting) of the ROADMAP, specifically:
- "Bimodal Metalogic/Core/ -- Deduction theorem, MCS theory" (Task 7, Wave 4)
- Unblocks Tasks 8 (Strong Completeness), 9 (Decidability), and 10 (Separation)

## Goals & Non-Goals

**Goals**:
- Port DeductionTheorem.lean to cslib with bimodal 7-constructor DerivationTree
- Create `bimodalDerivationSystem` instance connecting to generic MCS framework
- Port MaximalConsistent.lean with both list-based and set-based consistency
- Port MCSProperties.lean including temporal 4 future/past properties
- Create barrel import `Core.lean` and verify `lake build` passes with zero errors

**Non-Goals**:
- Port RestrictedMCS (deferred; depends on unported SubformulaClosure and Bundle modules)
- Port DualMCS.lean (does not exist in source)
- Create new generic MCS infrastructure (already done in task 29)
- Modify the generic MCS framework in `Consistency.lean`

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Well-founded recursion termination proof fails for 7-constructor DerivationTree | H | L | Source proof structure is identical; `subderiv_height_lt` lemma (trivial 3-line proof) resolves weakening case |
| Atom parametricity `{Atom : Type u}` causes universe issues | M | L | Temporal metalogic (task 31) already solved this pattern; follow same `variable {Atom : Type*}` approach |
| `temp_4_derived` and `temp_4_past` already exist in `TemporalDerived.lean` but live in source namespace | M | L | These exist in the source BimodalLogic repo; they port directly since cslib already has the matching axiom infrastructure. The temporal duality approach used in the source for `temp_4_past` works identically. |
| Axiom name mismatches (`prop_s` vs `imp_s`) cause type errors | L | M | Systematic rename; research report provides complete mapping |
| `bimodalDerivationSystem` instance has trouble matching `Nonempty` wrapper pattern | M | L | Temporal metalogic (task 31) provides exact template; follow `Temporal.Deriv` pattern |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 2, 3, 4 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Prerequisites -- Height Lemma and DerivationTree Bridge [COMPLETED]

**Goal**: Add the missing `subderiv_height_lt` lemma to `Derivation.lean` and create the `Bimodal.Deriv` Prop-wrapper plus `bimodalDerivationSystem` instance, following the temporal metalogic pattern exactly.

**Tasks**:
- [ ] Add `subderiv_height_lt` theorem to `Cslib/Logics/Bimodal/ProofSystem/Derivation.lean` (3 lines: `theorem subderiv_height_lt ... := by simp [height]`)
- [ ] Create `Cslib/Logics/Bimodal/Metalogic/Core/DerivationTree.lean` containing:
  - `Bimodal.Deriv` (Prop-level wrapper: `Nonempty (DerivationTree FrameClass.Base Gamma phi)`)
  - `Bimodal.ThDerivable` (empty-context derivability)
  - Helper combinators: `mp_deriv`, `weakening_deriv`, `assumption_deriv`
  - `bimodalDerivationSystem : Metalogic.DerivationSystem (Formula Atom)` instance
- [ ] Run `lake build Cslib.Logics.Bimodal.Metalogic.Core.DerivationTree` -- verify zero errors

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Bimodal/ProofSystem/Derivation.lean` -- add `subderiv_height_lt` (3 lines)
- `Cslib/Logics/Bimodal/Metalogic/Core/DerivationTree.lean` -- NEW (~70 lines)

**Verification**:
- `subderiv_height_lt` compiles and can be used by termination proofs
- `bimodalDerivationSystem` type-checks against `Metalogic.DerivationSystem`
- Scoped build passes with zero errors

---

### Phase 2: DeductionTheorem [NOT STARTED]

**Goal**: Port the deduction theorem for the bimodal 7-constructor DerivationTree, providing `deduction_theorem` and `bimodal_has_deduction_theorem` for the generic MCS framework.

**Tasks**:
- [ ] Create `Cslib/Logics/Bimodal/Metalogic/Core/DeductionTheorem.lean`
- [ ] Port `removeAll` helper and its properties (`removeAll_sub_of_sub`, `mem_removeAll_of_mem_of_ne`, `removeAll_sub_removeAll`)
- [ ] Port `deduction_axiom`, `deduction_imp_self`, `deduction_assumption_other`, `deduction_mp` helper cases
- [ ] Port `deduction_with_mem` (key helper for weakening case with A in middle of context) with well-founded recursion on `height` and termination proof using `mp_height_gt_left`, `mp_height_gt_right`, `subderiv_height_lt`
- [ ] Port `deduction_theorem` (main result) with 7-constructor match including `necessitation` (bimodal-specific, requires empty context so `simp at hA` discharges), `temporal_necessitation`, `temporal_duality`
- [ ] Add `bimodal_has_deduction_theorem : Metalogic.HasDeductionTheorem bimodalDerivationSystem` (wraps deduction theorem in `Nonempty` for the generic framework)
- [ ] Adapt all axiom names: `prop_s` -> `imp_s`, `prop_k` -> `imp_k`
- [ ] Add `variable {Atom : Type*}` and parametrize all definitions
- [ ] Run `lake build Cslib.Logics.Bimodal.Metalogic.Core.DeductionTheorem` -- verify zero errors

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Core/DeductionTheorem.lean` -- NEW (~350 lines)

**Verification**:
- `deduction_theorem` compiles with termination proof
- `bimodal_has_deduction_theorem` type-checks against `Metalogic.HasDeductionTheorem`
- All 7 constructor cases handled (axiom, assumption, modus_ponens, necessitation, temporal_necessitation, temporal_duality, weakening)
- Zero sorry occurrences
- Scoped build passes

---

### Phase 3: MaximalConsistent [NOT STARTED]

**Goal**: Port list-based and set-based consistency definitions, Lindenbaum's lemma, and basic MCS closure properties. Delegate generic properties to the foundations layer via `bimodalDerivationSystem`.

**Tasks**:
- [ ] Create `Cslib/Logics/Bimodal/Metalogic/Core/MaximalConsistent.lean`
- [ ] Define bimodal-specific abbreviations:
  - `Bimodal.SetConsistent := Metalogic.SetConsistent bimodalDerivationSystem`
  - `Bimodal.SetMaximalConsistent := Metalogic.SetMaximalConsistent bimodalDerivationSystem`
- [ ] Port list-based `Consistent` and `MaximalConsistent` definitions (needed by deduction theorem proofs in the source; these wrap `Nonempty (DerivationTree fc Gamma Formula.bot)`)
- [ ] Port `inconsistent_derives_bot`, `derives_neg_from_inconsistent_extension`, `derives_bot_from_phi_neg_phi`
- [ ] Port `maximal_extends_inconsistent`
- [ ] Port `maximal_consistent_closed` and `maximal_negation_complete` (these use the deduction theorem directly on list-based MCS)
- [ ] Port `theorem_in_mcs` (set-based: theorems are in every MCS)
- [ ] Add delegation wrappers for generic framework properties:
  - `bimodal_lindenbaum` (delegates to `Metalogic.set_lindenbaum`)
  - `bimodal_closed_under_derivation` (delegates to `Metalogic.SetMaximalConsistent.closed_under_derivation`)
  - `bimodal_implication_property` (delegates to `Metalogic.SetMaximalConsistent.implication_property`)
  - `bimodal_negation_complete` (delegates to `Metalogic.SetMaximalConsistent.negation_complete`)
- [ ] Run `lake build Cslib.Logics.Bimodal.Metalogic.Core.MaximalConsistent` -- verify zero errors

**Timing**: 1.5 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Core/MaximalConsistent.lean` -- NEW (~350 lines)

**Verification**:
- `Bimodal.SetConsistent` and `Bimodal.SetMaximalConsistent` abbreviations type-check
- `bimodal_lindenbaum` correctly delegates to generic Lindenbaum lemma
- List-based MCS closure properties compile (using deduction theorem)
- Set-based delegation wrappers compile (passing `bimodal_has_deduction_theorem`)
- Zero sorry occurrences
- Scoped build passes

---

### Phase 4: MCSProperties [NOT STARTED]

**Goal**: Port set-based MCS closure properties, context exchange helpers, and temporal 4 future/past properties needed for completeness.

**Tasks**:
- [ ] Create `Cslib/Logics/Bimodal/Metalogic/Core/MCSProperties.lean`
- [ ] Port `cons_filter_neq_perm` and `derivation_exchange` helpers
- [ ] Port `SetMaximalConsistent.closed_under_derivation` (bimodal-specific version that works at any `fc`, or verify the delegation wrapper from Phase 3 suffices)
- [ ] Port `SetMaximalConsistent.implication_property` and `SetMaximalConsistent.negation_complete` (bimodal-specific versions or verify delegation wrappers suffice)
- [ ] Port `SetMaximalConsistent.all_future_all_future` (Gφ in S implies GGφ in S) using `temp_4_derived` from `Bimodal.Theorems.TemporalDerived`
- [ ] Port `temp_4_past` (Hφ -> HHφ derived via temporal duality on temp_4_derived)
- [ ] Port `SetMaximalConsistent.all_past_all_past` (Hφ in S implies HHφ in S) using `temp_4_past`
- [ ] Port `set_consistent_not_both` and `SetMaximalConsistent.neg_excludes`
- [ ] Run `lake build Cslib.Logics.Bimodal.Metalogic.Core.MCSProperties` -- verify zero errors

**Timing**: 1 hour

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Core/MCSProperties.lean` -- NEW (~300 lines)

**Verification**:
- `all_future_all_future` and `all_past_all_past` compile using `temp_4_derived` from the existing `TemporalDerived.lean`
- `temp_4_past` derived via temporal duality compiles
- `set_consistent_not_both` and `neg_excludes` compile
- Zero sorry occurrences
- Scoped build passes

---

### Phase 5: Barrel Import and Full Verification [NOT STARTED]

**Goal**: Create the barrel import file, verify the full project build, and confirm zero sorry occurrences across all new files.

**Tasks**:
- [ ] Create `Cslib/Logics/Bimodal/Metalogic/Core.lean` barrel file importing all Core modules:
  ```
  import Cslib.Logics.Bimodal.Metalogic.Core.DerivationTree
  import Cslib.Logics.Bimodal.Metalogic.Core.DeductionTheorem
  import Cslib.Logics.Bimodal.Metalogic.Core.MaximalConsistent
  import Cslib.Logics.Bimodal.Metalogic.Core.MCSProperties
  ```
- [ ] Run `lake build` -- full project build, verify zero errors
- [ ] Run `grep -rn 'sorry' Cslib/Logics/Bimodal/Metalogic/Core/` -- verify zero sorry
- [ ] Run `grep -rn 'sorry' Cslib/Logics/Bimodal/Metalogic/Core.lean` -- verify zero sorry
- [ ] Verify the Cslib.lean barrel (if it exists) or the main project file includes the new Core module

**Timing**: 0.5 hours

**Depends on**: 2, 3, 4

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Core.lean` -- NEW (~15 lines)
- Potentially `Cslib.lean` or equivalent root barrel file -- add import

**Verification**:
- Full `lake build` passes with zero errors
- Zero sorry occurrences in all new files
- All 4 Core modules are importable via the barrel file

---

## Testing & Validation

- [ ] `lake build Cslib.Logics.Bimodal.Metalogic.Core.DerivationTree` passes (Phase 1)
- [ ] `lake build Cslib.Logics.Bimodal.Metalogic.Core.DeductionTheorem` passes (Phase 2)
- [ ] `lake build Cslib.Logics.Bimodal.Metalogic.Core.MaximalConsistent` passes (Phase 3)
- [ ] `lake build Cslib.Logics.Bimodal.Metalogic.Core.MCSProperties` passes (Phase 4)
- [ ] Full `lake build` passes with zero errors (Phase 5)
- [ ] `grep -rn 'sorry' Cslib/Logics/Bimodal/Metalogic/Core/` returns no matches
- [ ] `deduction_theorem` handles all 7 DerivationTree constructors
- [ ] `bimodalDerivationSystem` is a valid `Metalogic.DerivationSystem` instance
- [ ] `bimodal_has_deduction_theorem` is a valid `HasDeductionTheorem` instance
- [ ] Generic MCS properties delegated correctly (Lindenbaum, closure, implication, negation complete)

## Artifacts & Outputs

- `Cslib/Logics/Bimodal/ProofSystem/Derivation.lean` -- modified (add `subderiv_height_lt`)
- `Cslib/Logics/Bimodal/Metalogic/Core/DerivationTree.lean` -- NEW (~70 lines)
- `Cslib/Logics/Bimodal/Metalogic/Core/DeductionTheorem.lean` -- NEW (~350 lines)
- `Cslib/Logics/Bimodal/Metalogic/Core/MaximalConsistent.lean` -- NEW (~350 lines)
- `Cslib/Logics/Bimodal/Metalogic/Core/MCSProperties.lean` -- NEW (~300 lines)
- `Cslib/Logics/Bimodal/Metalogic/Core.lean` -- NEW (~15 lines, barrel)
- Total: ~1,085 new lines + ~3 modified lines

## Rollback/Contingency

- All new files are in `Cslib/Logics/Bimodal/Metalogic/Core/` -- can be deleted entirely without affecting existing code
- The only modification to existing code is `subderiv_height_lt` (3 additive lines in `Derivation.lean`) which can be reverted with `git checkout`
- If the generic MCS framework delegation fails, fall back to direct re-proof of generic properties (adds ~150 lines but avoids cross-module dependency issues)
- If `temp_4_derived` import from TemporalDerived.lean causes issues, the proof can be inlined (~30 lines)
