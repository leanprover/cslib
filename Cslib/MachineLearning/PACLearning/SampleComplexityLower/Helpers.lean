/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.MachineLearning.PACLearning.VCDimension

@[expose] public section

/-! # Sample Complexity Lower Bound — Helper Lemmas

Generic reusable lemmas for product measures, sample functions, and
combinatorics used in the EHKV lower bound proof.

## Main definitions

- `seenElements W' xs`: the elements of a `Finset` that appear in a sample

## Main statements

- `one_sub_pow_le_mul`: Bernoulli's inequality `1 - (1-x)^n ≤ n·x`
- `sampleOf_eq_of_agree`: agreeing concepts yield the same labeled sample
- `hypothesisError_eq_of_inter_eq`: error invariance under same intersection
- `pi_measure_compl_zero`: product measure vanishes off `W^m`
- `nullMeasurableSet_pi_of_finite_support`: null-measurability from finite support
- `measurableSet_setOf_exists_pi_eq`: the set of samples containing a given point
  is measurable
- `measurable_seenElements_card`: `xs ↦ |seenElements W' xs|` is measurable
- `expected_seenElements_le`: Bernoulli integration bound on seen elements
-/

open MeasureTheory Set Finset
open scoped ENNReal

noncomputable section

namespace Cslib.MachineLearning

open Classical in
/-- The set of elements of a `Finset` that appear in a sample. -/
noncomputable def seenElements {α : Type*} (W' : Finset α) {m : ℕ} (xs : Fin m → α) : Finset α :=
  W'.filter (fun w => ∃ i, xs i = w)

/-- Bernoulli's inequality: `1 - (1 - x)^n ≤ n * x` for `0 ≤ x ≤ 1`. -/
theorem one_sub_pow_le_mul {x : ℝ} (_hx : 0 ≤ x) (hx1 : x ≤ 1) (n : ℕ) :
    1 - (1 - x) ^ n ≤ ↑n * x := by
  have h : -1 ≤ (1 - x) := by linarith
  linarith [one_add_mul_sub_le_pow h n]

/-- Two concepts that agree on all sample points produce the same labeled
sample. -/
theorem sampleOf_eq_of_agree {α : Type*} {m : ℕ} {c₁ c₂ : Set α}
    {xs : Fin m → α} (h : ∀ i, xs i ∈ c₁ ↔ xs i ∈ c₂) :
    sampleOf c₁ xs = sampleOf c₂ xs := by
  funext i
  unfold sampleOf
  congr 1
  have := h i
  aesop

/-- Two concepts with the same intersection with `W` have the same hypothesis
error when the measure `P` is supported on `W`. -/
theorem hypothesisError_eq_of_inter_eq {α : Type*} [MeasurableSpace α]
    {P : Measure α} {W : Set α} (hP_supp : P Wᶜ = 0)
    {h₀ c₁ c₂ : Set α} (hinter : c₁ ∩ W = c₂ ∩ W) :
    hypothesisError P h₀ c₁ = hypothesisError P h₀ c₂ := by
  simp only [hypothesisError]
  have hP_restrict : ∀ A : Set α, P A = P (A ∩ W) := by
    intro A
    have h1 : P A ≤ P (A ∩ W ∪ Wᶜ) :=
      measure_mono (fun x hx => by_cases (fun hxW : x ∈ W => Or.inl ⟨hx, hxW⟩)
        (fun hxW => Or.inr hxW))
    exact le_antisymm ((h1.trans (measure_union_le _ _)).trans (by rw [hP_supp, add_zero]))
      (measure_mono Set.inter_subset_left)
  rw [hP_restrict (symmDiff h₀ c₁), hP_restrict (symmDiff h₀ c₂)]
  have : symmDiff h₀ c₁ ∩ W = symmDiff h₀ c₂ ∩ W := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_symmDiff, and_congr_left_iff]
    intro hxW
    have hc_iff : x ∈ c₁ ↔ x ∈ c₂ :=
      ⟨fun h => ((Set.ext_iff.mp hinter x).mp ⟨h, hxW⟩).1,
       fun h => ((Set.ext_iff.mp hinter x).mpr ⟨h, hxW⟩).1⟩
    constructor <;> rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨h1, fun h => h2 (hc_iff.mpr h)⟩
    · exact Or.inr ⟨hc_iff.mp h1, h2⟩
    · exact Or.inl ⟨h1, fun h => h2 (hc_iff.mp h)⟩
    · exact Or.inr ⟨hc_iff.mpr h1, h2⟩
  rw [this]

/-- If a measure `P` on `α` gives zero mass to the complement of a finite set `W`, then
the product measure `P^m` gives zero mass to the complement of `W^m`. -/
theorem pi_measure_compl_zero
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    {W : Finset α} {P : Measure α} [SigmaFinite P]
    (hP_supp : P (↑W : Set α)ᶜ = 0)
    {m : ℕ} :
    (Measure.pi (fun _ : Fin m => P))
      {xs : Fin m → α | ∀ i, xs i ∈ (↑W : Set α)}ᶜ = 0 := by
  set μ := Measure.pi (fun _ : Fin m => P)
  set Wm := {xs : Fin m → α | ∀ i, xs i ∈ (↑W : Set α)}
  have hsub : Wmᶜ ⊆ ⋃ i : Fin m, Function.eval i ⁻¹' (↑W : Set α)ᶜ := by
    intro xs hxs; simp only [Wm, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall] at hxs
    exact Set.mem_iUnion.mpr hxs
  have hle : μ Wmᶜ ≤ 0 :=
    calc μ Wmᶜ ≤ μ (⋃ i, Function.eval i ⁻¹' (↑W : Set α)ᶜ) := measure_mono hsub
      _ ≤ ∑ i : Fin m, μ (Function.eval i ⁻¹' (↑W : Set α)ᶜ) :=
          measure_iUnion_fintype_le μ _
      _ = ∑ _i : Fin m, (0 : ℝ≥0∞) := by
          congr 1; ext i; exact Measure.pi_eval_preimage_null _ hP_supp
      _ = 0 := Finset.sum_const_zero
  exact le_antisymm hle (zero_le _)

/-- If a measure `P` on `α` gives zero mass to the complement of a finite set `W`, then
every set in the product space is `NullMeasurableSet`. -/
theorem nullMeasurableSet_pi_of_finite_support
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    {W : Finset α} {P : Measure α} [SigmaFinite P] (hP_supp : P (↑W : Set α)ᶜ = 0)
    {m : ℕ} (S : Set (Fin m → α)) :
    NullMeasurableSet S (Measure.pi (fun _ : Fin m => P)) := by
  set μ := Measure.pi (fun _ : Fin m => P)
  set Wm := {xs : Fin m → α | ∀ i, xs i ∈ (↑W : Set α)}
  have hμ_supp : μ Wmᶜ = 0 := pi_measure_compl_zero hP_supp
  have hWm_finite : Wm.Finite := Set.Finite.pi' (fun _ => W.finite_toSet)
  have hAWm_meas : MeasurableSet (S ∩ Wm) :=
    (hWm_finite.subset (show S ∩ Wm ⊆ Wm from fun _ h => h.2)).measurableSet
  have hAWm_diff_null : μ (S \ Wm) = 0 :=
    measure_mono_null (fun _ ⟨_, hx⟩ => hx) hμ_supp
  have hA_eq : S = (S ∩ Wm) ∪ (S \ Wm) := by ext x; simp
  rw [hA_eq]
  exact hAWm_meas.nullMeasurableSet.union (NullMeasurableSet.of_null hAWm_diff_null)

/-- The set of sample vectors in which point `w` appears equals the union of
coordinate preimages `{xs | xs i = w}`. -/
theorem setOf_exists_pi_eq_iUnion_preimage {α : Type*} {m : ℕ} (w : α) :
    {xs : Fin m → α | ∃ i, xs i = w} =
      ⋃ i : Fin m, (fun xs : Fin m → α => xs i) ⁻¹' {w} := by ext xs; simp

/-- The set of sample vectors containing a given point is measurable. -/
theorem measurableSet_setOf_exists_pi_eq
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] {m : ℕ} (w : α) :
    MeasurableSet {xs : Fin m → α | ∃ i, xs i = w} := by
  rw [setOf_exists_pi_eq_iUnion_preimage w]
  exact MeasurableSet.iUnion (fun i => measurable_pi_apply i (MeasurableSet.singleton w))

open Classical in
/-- The cardinality of `seenElements W' xs` as an extended non-negative real equals a finset sum
of indicator functions over `W'`. -/
theorem seenElements_card_eq_sum {α : Type*} {m : ℕ} (W' : Finset α) :
    (fun xs : Fin m → α => ((seenElements W' xs).card : ℝ≥0∞)) =
      (fun xs => ∑ w ∈ W', if (∃ i, xs i = w) then (1 : ℝ≥0∞) else 0) := by
  ext xs; simp only [seenElements, Finset.card_filter]; push_cast; rfl

/-- The function `xs ↦ |seenElements W' xs|` is measurable with respect to the
product σ-algebra. -/
theorem measurable_seenElements_card
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] {m : ℕ} (W' : Finset α) :
    Measurable (fun xs : Fin m → α => ((seenElements W' xs).card : ℝ≥0∞)) := by
  rw [seenElements_card_eq_sum W']
  exact Finset.measurable_sum W' (fun w _ =>
    Measurable.ite (measurableSet_setOf_exists_pi_eq w) measurable_const measurable_const)

open Classical in
/-- **Bernoulli integration bound**: the expected number of elements of `W'`
seen in a random sample of size `m` is at most `|W'| · m · p`, when each
element of `W'` has probability `p ≤ 1` under the base measure `P`.
Follows from summing Bernoulli's inequality `1 - (1-p)^m ≤ m·p` over `W'`. -/
theorem expected_seenElements_le
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    {W' : Finset α} {p : ℝ} (hp_nonneg : 0 ≤ p) (hp_le_one : p ≤ 1)
    {m : ℕ} (P : Measure α) [IsProbabilityMeasure P]
    (hP_w : ∀ w ∈ W', P {w} = ENNReal.ofReal p) :
    ∫⁻ xs, ((seenElements W' xs).card : ℝ≥0∞)
      ∂(Measure.pi (fun _ : Fin m => P))
      ≤ ENNReal.ofReal (↑W'.card * (↑m * p)) := by
  set μ := Measure.pi (fun _ : Fin m => P)
  have h1p_nonneg : (0 : ℝ) ≤ 1 - p := by linarith
  -- Rewrite lintegral as sum of measures
  have hstep1 : ∫⁻ xs, ((seenElements W' xs).card : ℝ≥0∞) ∂μ
      = ∑ w ∈ W', μ {xs : Fin m → α | ∃ i, xs i = w} := by
    rw [seenElements_card_eq_sum W',
      lintegral_finset_sum' W' (fun w _ =>
        (Measurable.ite (measurableSet_setOf_exists_pi_eq w) measurable_const
          measurable_const).aemeasurable)]
    congr 1; ext w
    rw [show (fun xs : Fin m → α => if (∃ i, xs i = w) then (1 : ℝ≥0∞) else 0) =
      ({xs : Fin m → α | ∃ i, xs i = w}).indicator 1 from by ext; simp [indicator]]
    exact lintegral_indicator_one (measurableSet_setOf_exists_pi_eq w)
  rw [hstep1]
  -- Bound each term using Bernoulli inequality
  calc ∑ w ∈ W', μ {xs | ∃ i, xs i = w}
      ≤ ∑ _w ∈ W', ENNReal.ofReal (↑m * p) := by
        apply Finset.sum_le_sum; intro w hw
        have hcompl_eq : μ {xs : Fin m → α | ∃ i, xs i = w}ᶜ = (P {w}ᶜ) ^ m := by
          have : {xs : Fin m → α | ∃ i, xs i = w}ᶜ =
              Set.pi Set.univ (fun _ : Fin m => ({w} : Set α)ᶜ) := by
            ext xs; simp [Set.mem_pi]
          rw [this, Measure.pi_pi]
          simp [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        have hseen : μ {xs | ∃ i, xs i = w} = 1 - (P {w}ᶜ) ^ m := by
          have h2 := prob_compl_eq_one_sub (μ := μ) (measurableSet_setOf_exists_pi_eq w).compl
          rw [compl_compl] at h2; rw [h2, hcompl_eq]
        have hPwc : P {w}ᶜ = ENNReal.ofReal (1 - p) := by
          rw [prob_compl_eq_one_sub (MeasurableSet.singleton w), hP_w w hw,
            show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
          exact (ENNReal.ofReal_sub 1 hp_nonneg).symm
        rw [hseen, hPwc, ← ENNReal.ofReal_pow h1p_nonneg,
          show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm,
          ← ENNReal.ofReal_sub 1 (pow_nonneg h1p_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (one_sub_pow_le_mul hp_nonneg hp_le_one m)
    _ = ENNReal.ofReal (↑W'.card * (↑m * p)) := by
        rw [Finset.sum_const, nsmul_eq_mul,
          show (W'.card : ℝ≥0∞) = ENNReal.ofReal (W'.card : ℝ) from
            by rw [ENNReal.ofReal_natCast],
          ← ENNReal.ofReal_mul (by exact_mod_cast Nat.zero_le W'.card)]

end Cslib.MachineLearning
