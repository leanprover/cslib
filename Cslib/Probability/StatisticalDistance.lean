/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Init
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Topology.MetricSpace.Defs

/-!
# Statistical Distance of Finite Probability Mass Functions

For PMFs `p` and `q` on a finite type, their statistical distance is

`(1 / 2) * ∑ a, |p a - q a|`.

This is [BonehShoup2023], Definition 3.5. The probabilities are converted from
`ℝ≥0∞`, Mathlib's codomain for a `PMF`, to `ℝ` before taking the finite sum.

Statistical distance is packaged as a scoped `MetricSpace` instance on
`PMF α`, so it is spelled `dist p q` and the general metric API applies:
`dist_nonneg`, `dist_self`, `dist_comm`, `dist_triangle`, `dist_eq_zero`, and
so on. Open `Cslib.Probability.PMF` (or `open scoped Cslib.Probability.PMF`)
to activate the instance; it is scoped so that this library does not install a
global metric on Mathlib's `PMF` type.

Besides the metric structure, this file proves that applying the same
transformation — deterministic or randomized — to two PMFs cannot increase
their statistical distance; [BonehShoup2023], Theorem 3.13 is the
deterministic case.

## Main definitions

- `MetricSpace (PMF α)` (scoped instance): statistical distance as a metric
- `StatisticallyClose`: an upper bound on statistical distance

## Main results

- `dist_bind_le`: randomized postprocessing cannot increase statistical
  distance
- `dist_eq_one_of_disjoint_support`: PMFs with disjoint supports are at the
  maximum statistical distance
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

/-- Statistical distance makes the PMFs on a finite type a metric space
([BonehShoup2023], Definition 3.5). -/
noncomputable scoped instance instMetricSpace [Fintype α] :
    MetricSpace (PMF α) where
  dist p q := (∑ a, |(p a).toReal - (q a).toReal|) / 2
  dist_self p := by simp
  dist_comm p q := by simp [abs_sub_comm]
  dist_triangle p q r := by
    simp only [← add_div, ← Finset.sum_add_distrib]
    gcongr with a
    exact abs_sub_le (p a).toReal (q a).toReal (r a).toReal
  eq_of_dist_eq_zero {p q} h := by
    have hsum : ∑ a, |(p a).toReal - (q a).toReal| = 0 := by
      simpa [div_eq_zero_iff] using h
    ext a
    apply (ENNReal.toReal_eq_toReal_iff' (p.apply_ne_top a) (q.apply_ne_top a)).mp
    simpa [sub_eq_zero] using congr_fun
      ((Fintype.sum_eq_zero_iff_of_nonneg fun _ => abs_nonneg _).mp hsum) a

/-- The distance between two PMFs on a finite type is their statistical
distance ([BonehShoup2023], Definition 3.5). -/
theorem dist_eq [Fintype α] (p q : PMF α) :
    dist p q = (∑ a, |(p a).toReal - (q a).toReal|) / 2 :=
  rfl

/-- Statistical distance is at most one. -/
theorem dist_le_one [Fintype α] (p q : PMF α) : dist p q ≤ 1 := by
  rw [dist_eq]
  have h := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) =>
    abs_sub_le (p a).toReal 0 (q a).toReal
  simp only [sub_zero, zero_sub, abs_neg, abs_of_nonneg ENNReal.toReal_nonneg,
    Finset.sum_add_distrib, sum_toReal] at h
  linarith

/-- PMFs with disjoint supports are at the maximum statistical distance. -/
theorem dist_eq_one_of_disjoint_support [Fintype α] {p q : PMF α}
    (h : Disjoint p.support q.support) : dist p q = 1 := by
  have key : ∀ a, |(p a).toReal - (q a).toReal| = (p a).toReal + (q a).toReal := by
    intro a
    by_cases hp : p a = 0
    · simp [hp]
    · have hq : q a = 0 := by
        by_contra hq
        exact Set.disjoint_left.mp h ((p.mem_support_iff a).mpr hp)
          ((q.mem_support_iff a).mpr hq)
      simp [hq]
  simp [dist_eq, key, Finset.sum_add_distrib, sum_toReal]

/-- Applying the same randomized kernel to two PMFs cannot increase their
statistical distance. -/
theorem dist_bind_le [Fintype α] [Fintype β]
    (p q : PMF α) (kernel : α → PMF β) :
    dist (p.bind kernel) (q.bind kernel) ≤ dist p q := by
  simp only [dist_eq, bind_apply_toReal]
  gcongr
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
      simp_rw [← sub_mul, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg, mul_comm]
    _ = ∑ a, |(p a).toReal - (q a).toReal| := by
      rw [Finset.sum_comm]
      simp [← Finset.sum_mul, sum_toReal]

/-- Deterministic postprocessing cannot increase statistical distance
([BonehShoup2023], Theorem 3.13). -/
theorem dist_map_le [Fintype α] [Fintype β]
    (p q : PMF α) (f : α → β) :
    dist (p.map f) (q.map f) ≤ dist p q := by
  simpa [PMF.bind_pure_comp] using dist_bind_le p q (PMF.pure ∘ f)

/-- Two PMFs are `ε`-statistically close when their statistical distance is at
most `ε`. The `ℝ≥0` parameter rules out meaningless negative bounds. -/
def StatisticallyClose [Fintype α] (p q : PMF α) (ε : ℝ≥0) : Prop :=
  dist p q ≤ (ε : ℝ)

namespace StatisticallyClose

/-- Every PMF is statistically close to itself with zero error. -/
theorem refl [Fintype α] (p : PMF α) : StatisticallyClose p p 0 := by
  simp [StatisticallyClose]

/-- Statistical closeness is symmetric. -/
theorem symm [Fintype α] {p q : PMF α} {ε : ℝ≥0}
    (h : StatisticallyClose p q ε) : StatisticallyClose q p ε := by
  simpa [StatisticallyClose, dist_comm] using h

/-- A statistical-closeness bound remains valid when its error is enlarged. -/
theorem mono [Fintype α] {p q : PMF α} : Monotone (StatisticallyClose p q) :=
  fun _ _ hεδ h => le_trans h (by exact_mod_cast hεδ)

/-- Closeness bounds chain through an intermediate distribution, adding the
errors. -/
theorem trans [Fintype α] {p q r : PMF α} {ε δ : ℝ≥0}
    (hpq : StatisticallyClose p q ε) (hqr : StatisticallyClose q r δ) :
    StatisticallyClose p r (ε + δ) :=
  (dist_triangle p q r).trans (by simpa using add_le_add hpq hqr)

/-- A shared randomized postprocessing kernel preserves statistical
closeness. -/
theorem bind [Fintype α] [Fintype β] {p q : PMF α} {ε : ℝ≥0}
    (h : StatisticallyClose p q ε) (kernel : α → PMF β) :
    StatisticallyClose (p.bind kernel) (q.bind kernel) ε :=
  (dist_bind_le p q kernel).trans h

/-- Deterministic postprocessing preserves statistical closeness. -/
theorem map [Fintype α] [Fintype β] {p q : PMF α} {ε : ℝ≥0}
    (h : StatisticallyClose p q ε) (f : α → β) :
    StatisticallyClose (p.map f) (q.map f) ε :=
  (dist_map_le p q f).trans h

end StatisticallyClose

/-- Statistical closeness with zero error is equality. -/
@[simp]
theorem statisticallyClose_zero_iff [Fintype α] (p q : PMF α) :
    StatisticallyClose p q 0 ↔ p = q := by
  simp [StatisticallyClose]

end Cslib.Probability.PMF
