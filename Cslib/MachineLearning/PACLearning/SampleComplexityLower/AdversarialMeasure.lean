/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.MachineLearning.PACLearning.SampleComplexityLower.Helpers

@[expose] public section

/-! # Adversarial Measure Construction

Given a shattered set `W` with `|W| ≥ 2`, we construct a discrete
probability measure `P` supported on `W`. We pick an arbitrary element
`w₀ ∈ W` as the "heavy" point and put:
- mass `1 - 8ε` on `w₀`
- mass `8ε / (|W| - 1)` on each remaining point in `W \ {w₀}`

## Main definitions

- `adversarialMeasure W w₀ ε'`: the adversarial probability measure

## Main statements

- `adversarialMeasure_isProbabilityMeasure`: it is a probability measure
- `adversarialMeasure_singleton`: point mass on each `W'` element
- `adversarialMeasure_support`: support contained in `W`
-/

open MeasureTheory Set Finset
open scoped ENNReal

noncomputable section

namespace Cslib.MachineLearning

section AdversarialMeasure

variable {α : Type*} [MeasurableSpace α]

open Classical in
/-- The adversarial probability measure for the EHKV lower bound.
Concentrated on a finite set `W`, with a heavy point `w₀` carrying
mass `1 - 8ε` and each of the remaining `d = |W| - 1` points
carrying mass `8ε/d`. -/
def adversarialMeasure (W : Finset α) (w₀ : α) (ε' : ℝ) :
    Measure α :=
  let W' := W.erase w₀
  ENNReal.ofReal (1 - 8 * ε') • Measure.dirac w₀ +
    ∑ w ∈ W', ENNReal.ofReal (8 * ε' / W'.card) • Measure.dirac w

open Classical in
/-- The adversarial measure is a probability measure when `0 < ε ≤ 1/8`
and `|W| ≥ 2`. -/
theorem adversarialMeasure_isProbabilityMeasure
    {W : Finset α} {w₀ : α}
    {ε' : ℝ} (hε'_pos : 0 < ε') (hε'_le : ε' ≤ 1 / 8)
    (hd : 1 ≤ (W.erase w₀).card) :
    IsProbabilityMeasure (adversarialMeasure W w₀ ε') := by
  set d := (W.erase w₀).card with hd_def
  constructor
  simp only [adversarialMeasure, Measure.coe_add, Pi.add_apply,
    Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ MeasurableSet.univ,
    Set.indicator_univ, Pi.one_apply, mul_one,
    Measure.finset_sum_apply, Finset.sum_const, nsmul_eq_mul]
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
  rw [← ENNReal.ofReal_natCast (n := d)]
  rw [← ENNReal.ofReal_mul (by exact_mod_cast hd_pos.le)]
  rw [mul_div_cancel₀ _ (ne_of_gt hd_pos)]
  rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
  simp [sub_add_cancel]

open Classical in
/-- The adversarial measure assigns mass `8ε'/d` to each point in `W'`. -/
theorem adversarialMeasure_singleton [MeasurableSingletonClass α]
    {W : Finset α} {w₀ : α} {ε' : ℝ}
    {w : α} (hw : w ∈ W.erase w₀) :
    (adversarialMeasure W w₀ ε') {w} = ENNReal.ofReal (8 * ε' / (W.erase w₀).card) := by
  have hw_ne : w₀ ≠ w := Ne.symm (ne_of_mem_erase hw)
  simp only [adversarialMeasure, Measure.coe_add, Pi.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.finset_sum_apply, Measure.dirac_apply, Set.indicator_apply, Set.mem_singleton_iff]
  rw [if_neg hw_ne, mul_zero, zero_add]
  simp_rw [Pi.one_apply]
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' _ _ _, if_pos hw]

open Classical in
/-- The adversarial measure is supported on `W`: all mass outside `W` is zero. -/
theorem adversarialMeasure_support [MeasurableSingletonClass α]
    {W : Finset α} {w₀ : α} (hw₀ : w₀ ∈ W) {ε' : ℝ} :
    (adversarialMeasure W w₀ ε') (↑W : Set α)ᶜ = 0 := by
  have hw₀_not_compl : w₀ ∉ (↑W : Set α)ᶜ := by simp [hw₀]
  have hw_not_compl : ∀ w ∈ W.erase w₀, w ∉ (↑W : Set α)ᶜ := by
    intro w hw; simp [Finset.erase_subset _ _ hw]
  simp only [adversarialMeasure, Measure.coe_add, Pi.add_apply, Measure.smul_apply,
    smul_eq_mul, Measure.finset_sum_apply, Measure.dirac_apply]
  rw [indicator_of_notMem hw₀_not_compl, mul_zero, zero_add]
  apply Finset.sum_eq_zero
  intro w hw
  rw [indicator_of_notMem (hw_not_compl w hw), mul_zero]

end AdversarialMeasure

end Cslib.MachineLearning
