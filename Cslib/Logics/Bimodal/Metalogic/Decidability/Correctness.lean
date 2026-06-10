/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.Decidability.DecisionProcedure
public import Cslib.Logics.Bimodal.Metalogic.Soundness.Soundness

/-!
# Correctness of the Decision Procedure

This module proves properties of the tableau decision procedure.

## Main Theorems

- `decide_sound`: Soundness -- if we have a derivation, then the formula is valid
- `decide_sound'`: Variant extracting proof from DecisionResult.valid
- `validity_decidable`: Validity is classically decidable
- `validity_has_decision_procedure`: Boolean decision characterization
- `decide_result_exclusive`: Decision results are mutually exclusive

## Implementation Notes

The `soundness` theorem in `Soundness.lean` proves that derivability from
context `Γ` at `FrameClass.Base` implies semantic consequence.
The `FrameClass.Base` parameter structurally excludes axioms with
`minFrameClass > Base` (density, Prior-UZ/SZ, z1) via the `h_fc` gate.

- `decide_sound`: If we have a `DerivationTree .Base [] φ`, then `⊨ φ`
- Frame-class specific soundness is available via `soundness_dense`, `soundness_discrete`

## FMP-Dependent Theorems (Deferred to Task 43)

The following theorems depend on the Finite Model Property and are NOT ported here:
- `fmp_completeness`: If φ is true in all closure MCS, then φ is provable
- `fmp_incompleteness_witness`: If φ is not provable, a finite countermodel exists
- `countermodel_size_bound`: The filtered model is finite

## References

* Wu, M. Verified Decision Procedures for Modal Logics
* Gore, R. (1999). Tableau Methods for Modal and Temporal Logics

Ported from BimodalLogic/Metalogic/Decidability/Correctness.lean with
adaptations for universe-polymorphic `Formula Atom`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.Decidability

open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Metalogic

/-!
## Soundness of the Decision Procedure

These theorems require `[DecidableEq Atom]` and `[Hashable Atom]` because they
reference the decision procedure (`decide`) and proof extraction functions that
require these instances. The `soundness` theorem itself does not require them,
but the types `DecisionResult` and `DerivationTree` that appear in these
statements come from modules that do.
-/

section Soundness

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/--
Soundness of the decision procedure: if a formula has a `FrameClass.Base`
derivation (as produced by `decide` returning `.valid proof`), then the
formula is semantically valid.

This follows immediately from the `soundness` theorem with empty context,
where the context hypothesis is vacuously satisfied.
-/
theorem decide_sound (φ : Formula Atom)
    (d : DerivationTree FrameClass.Base ([] : Context Atom) φ) : ⊨ φ := by
  intro D _ _ _ _ ℱ M Omega h_sc τ h_mem t
  exact soundness [] φ d D ℱ M Omega h_sc τ h_mem t (by simp)

/--
Variant of `decide_sound` that extracts the proof from a `DecisionResult.valid`.
-/
theorem decide_sound' (φ : Formula Atom) (searchDepth tableauFuel : Nat)
    (fc : FrameClass) (proof : DerivationTree FrameClass.Base ([] : Context Atom) φ)
    (_h : decide φ searchDepth tableauFuel fc = .valid proof) : ⊨ φ :=
  decide_sound φ proof

end Soundness

/-!
## Decidability Theorem
-/

/--
Validity is decidable for TM bimodal logic.

This uses classical logic (`Classical.em`) to establish that validity
is a decidable property. A constructive decision procedure would require
completeness (via the Finite Model Property, deferred to Task 43).
-/
theorem validity_decidable {Atom : Type*} (φ : Formula Atom) :
    (⊨ φ) ∨ ¬(⊨ φ) :=
  Classical.em (⊨ φ)

/--
Alternative formulation: there exists a decision procedure
that correctly determines validity (using classical logic
for timeout cases).
-/
theorem validity_has_decision_procedure {Atom : Type*} (φ : Formula Atom) :
    ∃ (decision : Bool), (decision = true ↔ ⊨ φ) := by
  by_cases h : (⊨ φ)
  · exact ⟨true, by simp [h]⟩
  · exact ⟨false, by simp [h]⟩

/-!
## Properties of Decision Results
-/

section DecisionProperties

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/--
Decision results are mutually exclusive: exactly one of
`isValid`, `isInvalid`, `isTimeout` holds for any result.
-/
theorem decide_result_exclusive (φ : Formula Atom) (searchDepth tableauFuel : Nat)
    (fc : FrameClass := .Base) :
    let r := decide φ searchDepth tableauFuel fc
    (r.isValid ∧ ¬r.isInvalid ∧ ¬r.isTimeout) ∨
    (¬r.isValid ∧ r.isInvalid ∧ ¬r.isTimeout) ∨
    (¬r.isValid ∧ ¬r.isInvalid ∧ r.isTimeout) := by
  simp only [DecisionResult.isValid, DecisionResult.isInvalid, DecisionResult.isTimeout]
  cases decide φ searchDepth tableauFuel fc <;> simp

end DecisionProperties

end Cslib.Logic.Bimodal.Metalogic.Decidability
