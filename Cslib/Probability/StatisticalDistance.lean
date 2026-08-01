/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Init
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Statistical Distance of Finite Probability Mass Functions

For PMFs `p` and `q` on a finite type, their statistical distance is

`(1 / 2) * ∑ a, |p a - q a|`.

This is [BonehShoup2023], Definition 3.5. The probabilities are converted from
`ℝ≥0∞`, Mathlib's codomain for a `PMF`, to `ℝ` before taking the finite sum.

Besides the basic metric properties, this file proves that applying the same
transformation — deterministic or randomized — to two PMFs cannot increase
their statistical distance; [BonehShoup2023], Theorem 3.13 is the
deterministic case.

## Main definitions

- `statisticalDistance`: statistical distance
- `StatisticallyClose`: an upper bound on statistical distance

## Main results

- `statisticalDistance_bind_le`: randomized postprocessing cannot increase
  statistical distance
- `StatisticallyClose.trans`: closeness bounds chain through an intermediate
  distribution, adding the errors
- `statisticallyClose_zero_iff`: zero error is equality

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023]
-/

@[expose] public section

namespace Cslib.Probability.PMF

open scoped NNReal

universe u v

variable {α : Type u} {β : Type v}

private theorem sum_toReal [Fintype α] (p : PMF α) :
    ∑ a, (p a).toReal = 1 := by
  rw [← ENNReal.toReal_one, ← p.tsum_coe, tsum_fintype,
    ENNReal.toReal_sum fun a _ => p.apply_ne_top a]

private theorem bind_apply_toReal [Fintype α] (p : PMF α)
    (kernel : α → PMF β) (b : β) :
    (p.bind kernel b).toReal =
      ∑ a, (p a).toReal * (kernel a b).toReal := by
  rw [PMF.bind_apply, tsum_fintype,
    ENNReal.toReal_sum fun a _ =>
      ENNReal.mul_ne_top (p.apply_ne_top a) ((kernel a).apply_ne_top b)]
  simp only [ENNReal.toReal_mul]

/-- The statistical distance between two PMFs on a finite type
([BonehShoup2023], Definition 3.5). -/
noncomputable def statisticalDistance [Fintype α] (p q : PMF α) : ℝ :=
  (∑ a, |(p a).toReal - (q a).toReal|) / 2

/-- Statistical distance is nonnegative. -/
theorem statisticalDistance_nonneg [Fintype α] (p q : PMF α) :
    0 ≤ statisticalDistance p q :=
  div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) zero_le_two

/-- Statistical distance is at most one. -/
theorem statisticalDistance_le_one [Fintype α] (p q : PMF α) :
    statisticalDistance p q ≤ 1 := by
  rw [statisticalDistance]
  have h := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) =>
    abs_sub_le (p a).toReal 0 (q a).toReal
  simp only [sub_zero, zero_sub, abs_neg, abs_of_nonneg ENNReal.toReal_nonneg,
    Finset.sum_add_distrib, sum_toReal] at h
  linarith

/-- A PMF has zero statistical distance from itself. -/
@[simp]
theorem statisticalDistance_self [Fintype α] (p : PMF α) :
    statisticalDistance p p = 0 := by
  simp [statisticalDistance]

/-- Statistical distance is symmetric. -/
theorem statisticalDistance_comm [Fintype α] (p q : PMF α) :
    statisticalDistance p q = statisticalDistance q p := by
  simp only [statisticalDistance, abs_sub_comm]

/-- Statistical distance satisfies the triangle inequality. -/
theorem statisticalDistance_triangle [Fintype α] (p q r : PMF α) :
    statisticalDistance p r ≤ statisticalDistance p q + statisticalDistance q r := by
  simp only [statisticalDistance, ← add_div, ← Finset.sum_add_distrib]
  gcongr with a
  exact abs_sub_le (p a).toReal (q a).toReal (r a).toReal

/-- Statistical distance is zero exactly when the PMFs are equal. -/
@[simp]
theorem statisticalDistance_eq_zero_iff [Fintype α] (p q : PMF α) :
    statisticalDistance p q = 0 ↔ p = q := by
  refine ⟨fun h => ?_, by rintro rfl; simp⟩
  have hsum : ∑ a, |(p a).toReal - (q a).toReal| = 0 := by
    simpa [statisticalDistance] using h
  ext a
  apply (ENNReal.toReal_eq_toReal_iff' (p.apply_ne_top a) (q.apply_ne_top a)).mp
  simpa [sub_eq_zero] using congr_fun
    ((Fintype.sum_eq_zero_iff_of_nonneg fun _ => abs_nonneg _).mp hsum) a

/-- Applying the same randomized kernel to two PMFs cannot increase their
statistical distance. -/
theorem statisticalDistance_bind_le [Fintype α] [Fintype β]
    (p q : PMF α) (kernel : α → PMF β) :
    statisticalDistance (p.bind kernel) (q.bind kernel) ≤ statisticalDistance p q := by
  simp only [statisticalDistance, bind_apply_toReal]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  calc
    (∑ b, |(∑ a, (p a).toReal * (kernel a b).toReal) -
        ∑ a, (q a).toReal * (kernel a b).toReal|)
        ≤ ∑ b, ∑ a, |(p a).toReal * (kernel a b).toReal -
          (q a).toReal * (kernel a b).toReal| :=
      Finset.sum_le_sum fun _ _ => by
        rw [← Finset.sum_sub_distrib]
        exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ b, ∑ a, (kernel a b).toReal *
        |(p a).toReal - (q a).toReal| := by
      congr 1 with b
      congr 1 with a
      rw [← sub_mul, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
      ring
    _ = ∑ a, |(p a).toReal - (q a).toReal| := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, sum_toReal, one_mul]

/-- Deterministic postprocessing cannot increase statistical distance
([BonehShoup2023], Theorem 3.13). -/
theorem statisticalDistance_map_le [Fintype α] [Fintype β]
    (p q : PMF α) (f : α → β) :
    statisticalDistance (p.map f) (q.map f) ≤ statisticalDistance p q := by
  simpa only [PMF.bind_pure_comp] using
    statisticalDistance_bind_le p q (PMF.pure ∘ f)

/-- Two PMFs are `ε`-statistically close when their statistical distance is at
most `ε`. The `ℝ≥0` parameter rules out meaningless negative bounds. -/
def StatisticallyClose [Fintype α] (p q : PMF α) (ε : ℝ≥0) : Prop :=
  statisticalDistance p q ≤ (ε : ℝ)

namespace StatisticallyClose

/-- Every PMF is statistically close to itself with zero error. -/
theorem refl [Fintype α] (p : PMF α) : StatisticallyClose p p 0 := by
  simp [StatisticallyClose]

/-- Statistical closeness is symmetric. -/
theorem symm [Fintype α] {p q : PMF α} {ε : ℝ≥0}
    (h : StatisticallyClose p q ε) : StatisticallyClose q p ε := by
  simpa only [StatisticallyClose, statisticalDistance_comm] using h

/-- A statistical-closeness bound remains valid when its error is enlarged. -/
theorem mono [Fintype α] {p q : PMF α} {ε δ : ℝ≥0}
    (h : StatisticallyClose p q ε) (hεδ : ε ≤ δ) :
    StatisticallyClose p q δ :=
  h.trans (by exact_mod_cast hεδ)

/-- Closeness bounds chain through an intermediate distribution, adding the
errors. -/
theorem trans [Fintype α] {p q r : PMF α} {ε δ : ℝ≥0}
    (hpq : StatisticallyClose p q ε) (hqr : StatisticallyClose q r δ) :
    StatisticallyClose p r (ε + δ) :=
  (statisticalDistance_triangle p q r).trans (by
    simpa only [NNReal.coe_add] using add_le_add hpq hqr)

/-- A shared randomized postprocessing kernel preserves statistical
closeness. -/
theorem bind [Fintype α] [Fintype β] {p q : PMF α} {ε : ℝ≥0}
    (h : StatisticallyClose p q ε) (kernel : α → PMF β) :
    StatisticallyClose (p.bind kernel) (q.bind kernel) ε :=
  (statisticalDistance_bind_le p q kernel).trans h

/-- Deterministic postprocessing preserves statistical closeness. -/
theorem map [Fintype α] [Fintype β] {p q : PMF α} {ε : ℝ≥0}
    (h : StatisticallyClose p q ε) (f : α → β) :
    StatisticallyClose (p.map f) (q.map f) ε :=
  (statisticalDistance_map_le p q f).trans h

end StatisticallyClose

/-- Statistical closeness with zero error is equality. -/
@[simp]
theorem statisticallyClose_zero_iff [Fintype α] (p q : PMF α) :
    StatisticallyClose p q 0 ↔ p = q := by
  rw [StatisticallyClose, ← statisticalDistance_eq_zero_iff]
  exact ⟨fun h => le_antisymm h (statisticalDistance_nonneg p q), Eq.le⟩

end Cslib.Probability.PMF
