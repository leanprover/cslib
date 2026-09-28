/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.MachineLearning.PACLearning.VersionSpace
import Cslib.MachineLearning.PACLearning.VCDimension

namespace CslibTests.PACLearning

open Cslib.MachineLearning.PACLearning
open scoped NNReal ENNReal

/-- A learner on two samples over a singleton domain that predicts the first label. -/
def firstLabelLearner : Learner Unit Bool 2 :=
  fun S _ => (S 0).2

/-- Two different labels for the same point form an unrealizable sample. -/
def contradictorySample : LabeledSample Unit Bool 2 :=
  fun i => if i = 0 then ((), false) else ((), true)

theorem contradictorySample_not_realizable :
    ¬ Realizable (Set.univ : ConceptClass Unit Bool) contradictorySample := by
  rintro ⟨c, _, hc⟩
  simpa [contradictorySample] using
    (hc (0 : Fin 2)).trans (hc (1 : Fin 2)).symm

/-- Regression: consistency does not require a learner to fit an unrealizable
contradictory sample. -/
theorem firstLabelLearner_consistent :
    IsConsistent firstLabelLearner (Set.univ : ConceptClass Unit Bool) := by
  intro S hS
  obtain ⟨c, _, hc⟩ := hS
  rw [mem_versionSpace_iff]
  refine ⟨Set.mem_univ _, fun i => ?_⟩
  change (S 0).2 = (S i).2
  calc
    (S 0).2 = c (S 0).1 := hc 0
    _ = c (S i).1 := congrArg c (Subsingleton.elim _ _)
    _ = (S i).2 := (hc i).symm

example :
    firstLabelLearner contradictorySample (contradictorySample 1).1 ≠
      (contradictorySample 1).2 := by
  simp [firstLabelLearner, contradictorySample]

/-- A realizable sample used to guard the positive consistency guarantee. -/
def constantTrueSample : LabeledSample Unit Bool 2 :=
  fun _ => ((), true)

theorem constantTrueSample_realizable :
    Realizable (Set.univ : ConceptClass Unit Bool) constantTrueSample := by
  refine ⟨fun _ => true, Set.mem_univ _, ?_⟩
  intro i
  rfl

example (i : Fin 2) :
    firstLabelLearner constantTrueSample (constantTrueSample i).1 =
      (constantTrueSample i).2 :=
  firstLabelLearner_consistent.output_agrees
    constantTrueSample constantTrueSample_realizable i

section SampleComplexity

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable (C : ConceptClass α β) (ε δ : Set.Ioo (0 : ℝ≥0) 1)
variable (𝒟 : Set (MeasureTheory.Measure (α × β)))

-- Impossibility and zero-sample learning must have different complexities.
example : esampleComplexity (fun _ _ _ _ _ => False) C ε δ 𝒟 = ⊤ := by simp

example : esampleComplexity (fun _ _ _ _ _ => True) C ε δ 𝒟 = 0 := by
  simp

-- Admissible sizes need not be upward closed; the witness need not be the minimum.
example : sampleComplexity (fun m _ _ _ _ => m = 2 ∨ m = 5) C ε δ 𝒟
    ⟨5, Or.inr rfl⟩ = 2 := by
  have h : esampleComplexity (fun m _ _ _ _ => m = 2 ∨ m = 5) C ε δ 𝒟 = (2 : ℕ) := by
    rw [esampleComplexity_eq_natCast_iff (m := 2)]
    grind
  rw [← natCast_sampleComplexity ⟨5, Or.inr rfl⟩] at h
  exact_mod_cast h

end SampleComplexity

-- The new empirical-error statement accepts an empty sample without a positivity proof.
example (h : Unit → Bool) :
    empiricalError h (Fin.elim0 : LabeledSample Unit Bool 0) = 0 := by
  rw [empiricalError_eq_div]
  simp [empiricalMiscount]

-- A class that shatters nothing has dimension zero, not infinity.
example : evcDim (∅ : ConceptClass ℕ Bool) = 0 := by
  apply le_antisymm (evcDim_le_iff.mpr ?_) zero_le
  intro W hW
  obtain ⟨c, hc, _⟩ := hW ∅ (Set.empty_subset _)
  exact hc.elim

-- All Boolean classifiers on an infinite domain have infinite extended VC dimension.
example : evcDim (Set.univ : ConceptClass ℕ Bool) = ⊤ := by
  classical
  apply evcDim_eq_top_iff.mpr
  rw [hasFiniteVCDim_iff]
  rintro ⟨N, hN⟩
  have hW : SetShatters (Set.univ : ConceptClass ℕ Bool) ↑(Finset.range (N + 1)) := by
    intro V hV
    refine ⟨fun x => decide (x ∈ V), Set.mem_univ _, ?_⟩
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, decide_eq_true_eq]
    exact ⟨And.left, fun hx => ⟨hx, hV hx⟩⟩
  simpa using hN (Finset.range (N + 1)) hW

-- Bounds on the extended dimension also bound the natural-number view.
example {α : Type*} {C : ConceptClass α Bool} (hC : HasFiniteVCDim C)
    {W : Finset α} (hW : SetShatters C ↑W) : W.card ≤ vcDim C hC := by
  have h := hW.card_le_evcDim
  rw [← natCast_vcDim hC] at h
  exact_mod_cast h

end CslibTests.PACLearning
