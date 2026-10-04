/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Probability.PMF
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.MetricSpace.Defs

/-!
# Statistical Distance of Probability Mass Functions

For PMFs `p` and `q`, their statistical distance is

`(1 / 2) * ∑' a, |p a - q a|`.

On finite types this is [BonehShoup2023], Definition 3.5. The probabilities are converted from
`ℝ≥0∞`, Mathlib's codomain for a `PMF`, to `ℝ` before summing. Absolute summability follows
from the unit mass of each distribution, so the same API applies to infinite types such as `ℕ`.

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
- `abs_sum_mul_sub_le`: the expectation of a bounded score changes by at most twice the bound
  times the statistical distance
- `dist_filter`: conditioning changes a finite distribution by exactly the discarded probability
- `dist_bind_pair`: with a shared revealed input, statistical distance is the average distance
  of the conditional outputs
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

private theorem summable_abs_sub (p q : PMF α) :
    Summable (fun a => |(p a).toReal - (q a).toReal|) :=
  ((summable_toReal p).sub (summable_toReal q)).abs

/-- Statistical distance makes discrete probability distributions a metric space. -/
noncomputable scoped instance instMetricSpace :
    MetricSpace (PMF α) where
  dist p q := (∑' a, |(p a).toReal - (q a).toReal|) / 2
  dist_self p := by simp
  dist_comm p q := by simp [abs_sub_comm]
  dist_triangle p q r := by
    rw [← add_div, ← (summable_abs_sub p q).tsum_add (summable_abs_sub q r)]
    gcongr ?_ / _
    exact (summable_abs_sub p r).tsum_le_tsum (fun a => abs_sub_le _ _ _)
      ((summable_abs_sub p q).add (summable_abs_sub q r))
  eq_of_dist_eq_zero {p q} h := by
    have hsum : ∑' a, |(p a).toReal - (q a).toReal| = 0 := by
      simpa [div_eq_zero_iff] using h
    ext a
    apply (ENNReal.toReal_eq_toReal_iff' (p.apply_ne_top a) (q.apply_ne_top a)).mp
    have ha := (summable_abs_sub p q).le_tsum a (fun _ _ => abs_nonneg _)
    simpa [hsum, sub_eq_zero] using ha

/-- Statistical distance is half the sum of the absolute differences of the masses. -/
theorem dist_eq_tsum (p q : PMF α) :
    dist p q = (∑' a, |(p a).toReal - (q a).toReal|) / 2 := rfl

/-- The distance between two PMFs on a finite type is their statistical
distance ([BonehShoup2023], Definition 3.5). -/
theorem dist_eq [Fintype α] (p q : PMF α) :
    dist p q = (∑ a, |(p a).toReal - (q a).toReal|) / 2 := by
  simp [dist_eq_tsum]

/-- Changing the distribution changes the expectation of a bounded real-valued score by at most
twice its absolute bound times the statistical distance. Scores with values in `[-1, 1]` use
`bound = 1`. -/
theorem abs_sum_mul_sub_le [Fintype α] (p q : PMF α) (score : α → ℝ)
    {bound : ℝ} (hscore : ∀ a, |score a| ≤ bound) :
    |(∑ a, (p a).toReal * score a) - ∑ a, (q a).toReal * score a| ≤
      2 * bound * dist p q := by
  rw [← Finset.sum_sub_distrib]
  simp only [← sub_mul]
  calc
    _ ≤ ∑ a, |((p a).toReal - (q a).toReal) * score a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, |(p a).toReal - (q a).toReal| * bound := by
      simp only [abs_mul]
      gcongr with a
      exact hscore a
    _ = _ := by rw [← Finset.sum_mul, dist_eq]; ring

/-- Statistical distance is at most one. -/
theorem dist_le_one (p q : PMF α) : dist p q ≤ 1 := by
  rw [dist_eq_tsum]
  have h := Summable.tsum_le_tsum
    (fun a => by simpa using abs_sub_le (p a).toReal 0 (q a).toReal)
    (summable_abs_sub p q) ((summable_toReal p).add (summable_toReal q))
  rw [(summable_toReal p).tsum_add (summable_toReal q), tsum_toReal, tsum_toReal] at h
  linarith

/-- Conditioning on a possible event changes the distribution by exactly the probability
discarded outside that event. -/
theorem dist_filter [Finite α] (p : PMF α) (event : Set α)
    (hevent : ∃ a ∈ event, a ∈ p.support) :
    dist p (p.filter event hevent) = (p.toOuterMeasure eventᶜ).toReal := by
  classical
  let := Fintype.ofFinite α
  have hpositive := (toOuterMeasure_toReal_pos_iff p event).mpr hevent
  have hprobability : (p.toOuterMeasure event).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (toOuterMeasure_le_one p event)
  have habsolute (a : α) : |(p a).toReal - ((p.filter event hevent) a).toReal| =
      ((p.filter event hevent) a).toReal - (p a).toReal +
        2 * (if a ∈ eventᶜ then (p a).toReal else 0) := by
    by_cases ha : a ∈ event
    · have hle : (p a).toReal ≤ ((p.filter event hevent) a).toReal := by
        rw [filter_apply_toReal, ite_eq_left ha]
        exact le_div_self ENNReal.toReal_nonneg hpositive hprobability
      rw [abs_of_nonpos (sub_nonpos.mpr hle)]
      simp [ha]
    · simp only [filter_apply_toReal, ha, Set.mem_compl_iff, not_false_eq_true, ↓reduceIte,
        sub_zero, ENNReal.abs_toReal]
      ring
  rw [dist_eq, toOuterMeasure_apply_toReal]
  simp only [habsolute, Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_toReal, sub_self,
    zero_add, ← Finset.mul_sum]
  ring_nf

/-- PMFs with disjoint supports are at the maximum statistical distance. -/
theorem dist_eq_one_of_disjoint_support {p q : PMF α}
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
  rw [dist_eq_tsum, tsum_congr key, (summable_toReal p).tsum_add (summable_toReal q),
    tsum_toReal, tsum_toReal]
  norm_num

private theorem summable_weighted_kernel {weight : α → ℝ} (hweight : Summable weight)
    (hnonneg : ∀ a, 0 ≤ weight a) (kernel : α → PMF β) :
    Summable (fun pair : α × β => weight pair.1 * (kernel pair.1 pair.2).toReal) := by
  rw [summable_prod_of_nonneg (fun pair => mul_nonneg (hnonneg pair.1) ENNReal.toReal_nonneg)]
  exact ⟨fun a => (summable_toReal (kernel a)).mul_left (weight a),
    by simpa [tsum_mul_left] using hweight⟩

/-- Weighting by the masses of a kernel at a fixed outcome preserves summability. -/
private theorem summable_mul_kernel {weight : α → ℝ} (hweight : Summable weight)
    (kernel : α → PMF β) (b : β) : Summable (fun a => weight a * (kernel a b).toReal) := by
  refine Summable.of_norm_bounded (g := fun a => |weight a|) hweight.abs fun a => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
  exact mul_le_of_le_one_right (abs_nonneg _)
    (ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using (kernel a).coe_le_one b))

/-- Applying the same randomized kernel to two PMFs cannot increase their
statistical distance. -/
theorem dist_bind_le (p q : PMF α) (kernel : α → PMF β) :
    dist (p.bind kernel) (q.bind kernel) ≤ dist p q := by
  have hd := summable_weighted_kernel (summable_abs_sub p q) (fun _ => abs_nonneg _) kernel
  have hbound (b : β) : |((p.bind kernel) b).toReal - ((q.bind kernel) b).toReal| ≤
      ∑' a, |(p a).toReal - (q a).toReal| * (kernel a b).toReal := by
    rw [bind_apply_toReal_tsum, bind_apply_toReal_tsum, ← (summable_mul_kernel
      (summable_toReal p) kernel b).tsum_sub (summable_mul_kernel (summable_toReal q) kernel b)]
    simp_rw [← sub_mul]
    have hs := summable_mul_kernel ((summable_toReal p).sub (summable_toReal q)) kernel b
    simpa using
      norm_tsum_le_tsum_norm (f := fun a => ((p a).toReal - (q a).toReal) * (kernel a b).toReal)
        (by simpa using hs.abs)
  rw [dist_eq_tsum, dist_eq_tsum]
  gcongr ?_ / _
  calc
    _ ≤ ∑' b, ∑' a, |(p a).toReal - (q a).toReal| * (kernel a b).toReal :=
      Summable.tsum_le_tsum hbound (summable_abs_sub _ _) hd.prod_symm.prod
    _ = _ := by
      rw [Summable.tsum_comm (f := fun a b =>
        |(p a).toReal - (q a).toReal| * (kernel a b).toReal) hd]
      simp [tsum_mul_left]

/-- Deterministic postprocessing cannot increase statistical distance
([BonehShoup2023], Theorem 3.13). -/
theorem dist_map_le (p q : PMF α) (f : α → β) :
    dist (p.map f) (q.map f) ≤ dist p q := by
  simpa [PMF.bind_pure_comp] using dist_bind_le p q (PMF.pure ∘ f)

/-- With a shared revealed input, distance is the average distance of the conditional outputs. -/
theorem dist_bind_pair [Fintype α] [Finite β] (p : PMF α) (f g : α → PMF β) :
    dist (p.bind (fun a => (f a).map (a, ·)))
        (p.bind (fun a => (g a).map (a, ·))) =
      ∑ a, (p a).toReal * dist (f a) (g a) := by
  let := Fintype.ofFinite β
  simp only [dist_eq, Fintype.sum_prod_type, PMF.map, Function.comp_def, bind_pair_apply]
  simp [← mul_sub, ← Finset.mul_sum, Finset.sum_div, mul_div_assoc]

/-- Squared distance with a shared revealed input is at most the average squared distance. -/
theorem dist_bind_pair_sq_le [Fintype α] [Finite β] (p : PMF α) (f g : α → PMF β) :
    dist (p.bind (fun a => (f a).map (a, ·)))
        (p.bind (fun a => (g a).map (a, ·))) ^ 2 ≤
      ∑ a, (p a).toReal * dist (f a) (g a) ^ 2 := by
  rw [dist_bind_pair]
  exact Real.pow_arith_mean_le_arith_mean_pow _ _ _ (fun _ _ => ENNReal.toReal_nonneg)
    (sum_toReal p) (fun _ _ => dist_nonneg) 2

/-- Two PMFs are `ε`-statistically close when their statistical distance is at
most `ε`. The `ℝ≥0` parameter rules out meaningless negative bounds. -/
def StatisticallyClose (p q : PMF α) (ε : ℝ≥0) : Prop :=
  dist p q ≤ (ε : ℝ)

namespace StatisticallyClose

/-- Every PMF is statistically close to itself with zero error. -/
theorem refl (p : PMF α) : StatisticallyClose p p 0 := by
  simp [StatisticallyClose]

/-- Statistical closeness is symmetric. -/
theorem symm {p q : PMF α} {ε : ℝ≥0}
    (h : StatisticallyClose p q ε) : StatisticallyClose q p ε := by
  simpa [StatisticallyClose, dist_comm] using h

/-- A statistical-closeness bound remains valid when its error is enlarged. -/
theorem mono {p q : PMF α} : Monotone (StatisticallyClose p q) :=
  fun _ _ hεδ h => le_trans h (by exact_mod_cast hεδ)

/-- Closeness bounds chain through an intermediate distribution, adding the
errors. -/
theorem trans {p q r : PMF α} {ε δ : ℝ≥0}
    (hpq : StatisticallyClose p q ε) (hqr : StatisticallyClose q r δ) :
    StatisticallyClose p r (ε + δ) :=
  (dist_triangle p q r).trans (by simpa using add_le_add hpq hqr)

/-- A shared randomized postprocessing kernel preserves statistical
closeness. -/
theorem bind {p q : PMF α} {ε : ℝ≥0}
    (h : StatisticallyClose p q ε) (kernel : α → PMF β) :
    StatisticallyClose (p.bind kernel) (q.bind kernel) ε :=
  (dist_bind_le p q kernel).trans h

/-- Deterministic postprocessing preserves statistical closeness. -/
theorem map {p q : PMF α} {ε : ℝ≥0}
    (h : StatisticallyClose p q ε) (f : α → β) :
    StatisticallyClose (p.map f) (q.map f) ε :=
  (dist_map_le p q f).trans h

end StatisticallyClose

/-- Statistical closeness with zero error is equality. -/
@[simp]
theorem statisticallyClose_zero_iff (p q : PMF α) :
    StatisticallyClose p q 0 ↔ p = q := by
  simp [StatisticallyClose]

end Cslib.Probability.PMF
