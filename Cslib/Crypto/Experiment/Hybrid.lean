/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Experiment

/-!
# Polynomially many game hops

The concrete hybrid inequality adds the advantages of adjacent games. The asymptotic theorem
requires one negligible function `ε : ℕ → ℝ≥0` bounding every adjacent-hop advantage:
for every security parameter `n` and index `i < hops n`, the advantage between games `i`
and `i + 1` is at most `ε n`. The function `ε` may depend on the distinguisher.
Negligibility separately for each fixed hop does not suffice when the number of hops
grows with `n`.

The averaging result `Experiment.advantage_hybrid_average` gives an exact identity:
`advantage (games 0) (games hops) = samplingRange * advantage left right`.
Here `left` and `right` are the experiments that uniformly select an adjacent pair,
run its left or right game respectively, and reject on unused indices. This interface takes
the prefix `0, …, hops` of a natural-number-indexed family, as used by staged algorithms.
The companion `Experiment.advantage_hybrid_average_fin` takes a finite chain containing
exactly `hops + 1` experiments. Both interfaces keep the sampling range independent of
the number of hops and use the same finite-chain telescoping argument.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Section 9.3.
-/

@[expose] public section

namespace Cslib.Crypto.Experiment

open Probability
open scoped NNReal

/-- A uniformly selected experiment succeeds with the average of its success probabilities. -/
theorem succProbability_uniform {α : Type*} [Fintype α] [Nonempty α] (games : α → Experiment) :
    succProbability ((PMF.uniformOfFintype α).bind games) =
      (∑ a, succProbability (games a)) / Fintype.card α := by
  apply NNReal.eq
  simp only [succProbability, ENNReal.coe_toNNReal_eq_toReal, Probability.PMF.bind_apply_toReal]
  simp [ENNReal.coe_toNNReal_eq_toReal, inv_mul_eq_div, Finset.sum_div]

private theorem sum_succProbability_sub {hops : ℕ}
    (games : Fin (hops + 1) → Experiment) :
    (∑ i : Fin hops,
      ((succProbability (games i.castSucc) : ℝ) - succProbability (games i.succ))) =
      (succProbability (games 0) : ℝ) - succProbability (games (Fin.last hops)) := by
  have hleft := Fin.sum_univ_succ (fun i => (succProbability (games i) : ℝ))
  have hright := Fin.sum_univ_castSucc (fun i => (succProbability (games i) : ℝ))
  rw [Finset.sum_sub_distrib]
  linarith

/-- Randomly choosing an adjacent hybrid telescopes signed gaps.

The finite chain contains `hops + 1` games, connecting `games 0` to `games (Fin.last hops)`.
Choose an index `i` uniformly from `Fin samplingRange`. If `i < hops`, the left experiment
runs the earlier game of this adjacent pair and the right experiment runs the later game.
Otherwise, both reject.

Allowing `samplingRange` to exceed `hops` lets applications choose a power-of-two range and
sample its index exactly using a fixed number of fair-coin flips. For example, three hops
can use two coin flips to choose among four indices: indices 0, 1 and 2 select the three
adjacent pairs, while index 3 makes both experiments reject. The reduction has loss four.

In general, the difference between the two mixtures' success probabilities is the endpoint
difference divided by `samplingRange`: the adjacent differences telescope, and unused indices
contribute zero. See `advantage_hybrid_average_fin` for the corresponding advantage identity.
This construction avoids choosing a best hop separately for each security parameter. -/
theorem succProbability_hybrid_average_fin {hops : ℕ}
    (games : Fin (hops + 1) → Experiment) (samplingRange : ℕ)
    [NeZero samplingRange] (hle : hops ≤ samplingRange) :
    (succProbability (games 0) : ℝ) - succProbability (games (Fin.last hops)) =
      (samplingRange : ℝ) *
        (succProbability ((PMF.uniformOfFintype (Fin samplingRange)).bind
          (fun i => if hi : i.val < hops then games (i.castLT hi).castSucc
            else PMF.pure false)) -
        succProbability ((PMF.uniformOfFintype (Fin samplingRange)).bind
          (fun i => if hi : i.val < hops then games (i.castLT hi).succ
            else PMF.pure false))) := by
  have hsum : (∑ i : Fin samplingRange, if hi : i.val < hops then
      (succProbability (games (i.castLT hi).castSucc) : ℝ) -
        succProbability (games (i.castLT hi).succ) else 0) =
      (succProbability (games 0) : ℝ) - succProbability (games (Fin.last hops)) := by
    rw [← sum_succProbability_sub games]
    refine (Fintype.sum_of_injective (Fin.castLE hle) (Fin.castLE_injective hle) _ _
      (fun i hi => ?_) (fun i => ?_)).symm
    · have hnot : ¬ i.val < hops := by
        intro h
        exact hi ⟨i.castLT h, Fin.ext rfl⟩
      exact dite_eq_right hnot
    · simp only [Fin.val_castLE, dite_eq_left i.isLt]
      rfl
  have hdiff (i : Fin samplingRange) :
      (succProbability (if hi : i.val < hops then games (i.castLT hi).castSucc
        else PMF.pure false) : ℝ) -
      succProbability (if hi : i.val < hops then games (i.castLT hi).succ
        else PMF.pure false) =
      if hi : i.val < hops then
        (succProbability (games (i.castLT hi).castSucc) : ℝ) -
          succProbability (games (i.castLT hi).succ) else 0 := by
    split_ifs <;> simp [succProbability]
  have hsamplingRange : (samplingRange : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne samplingRange
  rw [succProbability_uniform, succProbability_uniform]
  simp only [NNReal.coe_div, NNReal.coe_sum, NNReal.coe_natCast, Fintype.card_fin, ← sub_div,
    ← Finset.sum_sub_distrib, hdiff, hsum, mul_div_cancel₀ _ hsamplingRange]

/-- Averaging adjacent hybrids also preserves distinguishing advantage, with the
sampling-range loss and no parameter-dependent choice of the best hop. -/
theorem advantage_hybrid_average_fin {hops : ℕ}
    (games : Fin (hops + 1) → Experiment) (samplingRange : ℕ)
    [NeZero samplingRange] (hle : hops ≤ samplingRange) :
    advantage (games 0) (games (Fin.last hops)) = samplingRange *
      advantage
        ((PMF.uniformOfFintype (Fin samplingRange)).bind
          (fun i => if hi : i.val < hops then games (i.castLT hi).castSucc
            else PMF.pure false))
        ((PMF.uniformOfFintype (Fin samplingRange)).bind
          (fun i => if hi : i.val < hops then games (i.castLT hi).succ
            else PMF.pure false)) := by
  apply NNReal.eq
  rw [NNReal.coe_mul, coe_advantage, coe_advantage, NNReal.coe_natCast,
    succProbability_hybrid_average_fin games samplingRange hle, abs_mul, Nat.abs_cast]

/-- Local reductions with a common signed loss combine into one uniformly selected reduction.
The chain has exactly `hops + 1` experiments and the local tests have exactly `hops` entries.
Unused sampling indices reject in both mixtures. The proof needs no choice of a best hop
depending on the security parameter. -/
theorem succProbability_hybrid_reduction_fin {hops : ℕ}
    (games : Fin (hops + 1) → Experiment) (game1 game2 : Fin hops → Experiment)
    (samplingRange : ℕ) [NeZero samplingRange] (hle : hops ≤ samplingRange) (loss : ℝ)
    (hstep : ∀ i, (succProbability (games i.castSucc) : ℝ) - succProbability (games i.succ) =
      loss * (succProbability (game1 i) - succProbability (game2 i))) :
    (succProbability (games 0) : ℝ) - succProbability (games (Fin.last hops)) =
      (samplingRange : ℝ) * loss *
        (succProbability ((PMF.uniformOfFintype (Fin samplingRange)).bind
          (fun i => if hi : i.val < hops then game1 (i.castLT hi) else PMF.pure false)) -
        succProbability ((PMF.uniformOfFintype (Fin samplingRange)).bind
          (fun i => if hi : i.val < hops then game2 (i.castLT hi) else PMF.pure false))) := by
  have hterm (i : Fin samplingRange) :
      (succProbability (if hi : i.val < hops then games (i.castLT hi).castSucc
        else PMF.pure false) : ℝ) -
      succProbability (if hi : i.val < hops then games (i.castLT hi).succ
        else PMF.pure false) =
      loss *
        (succProbability (if hi : i.val < hops then game1 (i.castLT hi)
          else PMF.pure false) -
        succProbability (if hi : i.val < hops then game2 (i.castLT hi)
          else PMF.pure false)) := by
    split_ifs with hi
    · exact hstep (i.castLT hi)
    · simp [succProbability]
  rw [succProbability_hybrid_average_fin games samplingRange hle]
  simp only [succProbability_uniform, NNReal.coe_div, NNReal.coe_sum, NNReal.coe_natCast,
    Fintype.card_fin, ← sub_div, ← Finset.sum_sub_distrib, hterm, ← Finset.mul_sum]
  ring

/-- Uniformly select an adjacent pair in the prefix `0, …, hops` of an indexed family.
The signed endpoint gap is the mixture gap times `samplingRange`; unused indices reject
on both sides. This is the finite-chain identity applied to the family's prefix. -/
theorem succProbability_hybrid_average (games : ℕ → Experiment) (hops samplingRange : ℕ)
    [NeZero samplingRange] (hle : hops ≤ samplingRange) :
    (succProbability (games 0) : ℝ) - succProbability (games hops) = (samplingRange : ℝ) *
      (succProbability
        ((PMF.uniformOfFintype (Fin samplingRange)).bind
          (fun i => if i.val < hops then games i.val else PMF.pure false)) - succProbability
        ((PMF.uniformOfFintype (Fin samplingRange)).bind
          (fun i => if i.val < hops then games (i.val + 1) else PMF.pure false))) := by
  simpa only [Fin.val_zero, Fin.val_last, Fin.val_castSucc, Fin.val_castLT, Fin.val_succ,
    dite_eq_ite] using
    succProbability_hybrid_average_fin (fun i : Fin (hops + 1) => games i.val) samplingRange hle

/-- Averaging adjacent experiments in the prefix of an indexed family preserves endpoint
advantage, with the sampling-range loss and no parameter-dependent choice of the best hop. -/
theorem advantage_hybrid_average (games : ℕ → Experiment) (hops samplingRange : ℕ)
    [NeZero samplingRange] (hle : hops ≤ samplingRange) :
    advantage (games 0) (games hops) = samplingRange *
      advantage
        ((PMF.uniformOfFintype (Fin samplingRange)).bind
          (fun i => if i.val < hops then games i.val else PMF.pure false))
        ((PMF.uniformOfFintype (Fin samplingRange)).bind
          (fun i => if i.val < hops then games (i.val + 1) else PMF.pure false)) := by
  simpa only [Fin.val_zero, Fin.val_last, Fin.val_castSucc, Fin.val_castLT, Fin.val_succ,
    dite_eq_ite] using
    advantage_hybrid_average_fin (fun i : Fin (hops + 1) => games i.val) samplingRange hle

/-- Local signed reductions along the prefix of an indexed family combine into one uniformly
selected reduction. Restricting to the prefix applies the finite-chain reduction identity. -/
theorem succProbability_hybrid_reduction (games game1 game2 : ℕ → Experiment)
    (hops samplingRange : ℕ) [NeZero samplingRange] (hle : hops ≤ samplingRange) (loss : ℝ)
    (hstep : ∀ i < hops, (succProbability (games i) : ℝ) - succProbability (games (i + 1)) =
      loss * (succProbability (game1 i) - succProbability (game2 i))) :
    (succProbability (games 0) : ℝ) - succProbability (games hops) = (samplingRange : ℝ) * loss *
      (succProbability ((PMF.uniformOfFintype (Fin samplingRange)).bind
        (fun i => if i.val < hops then game1 i.val else PMF.pure false)) -
      succProbability ((PMF.uniformOfFintype (Fin samplingRange)).bind
        (fun i => if i.val < hops then game2 i.val else PMF.pure false))) := by
  simpa only [Fin.val_zero, Fin.val_last, Fin.val_castLT, dite_eq_ite] using
    succProbability_hybrid_reduction_fin (fun i : Fin (hops + 1) => games i.val)
      (fun i : Fin hops => game1 i.val) (fun i : Fin hops => game2 i.val)
      samplingRange hle loss (fun i => hstep i.val i.isLt)

/-- The advantage between the endpoints is at most the sum of all adjacent advantages. -/
theorem advantage_hybrid_le_sum (games : ℕ → Experiment) (hops : ℕ) :
    advantage (games 0) (games hops) ≤
      ∑ i ∈ Finset.range hops, advantage (games i) (games (i + 1)) := by
  rw [← NNReal.coe_le_coe, NNReal.coe_sum]
  simpa only [advantage, coe_nndist] using
    dist_le_range_sum_dist (fun i => succProbability (games i)) hops

/-- The endpoint advantage of a finite chain is bounded by the sum of its hop advantages.
Each `i : Fin hops` selects the adjacent games `i.castSucc` and `i.succ`. -/
theorem advantage_hybrid_le_sum_fin {hops : ℕ}
    (games : Fin (hops + 1) → Experiment) :
    advantage (games 0) (games (Fin.last hops)) ≤
      ∑ i : Fin hops, advantage (games i.castSucc) (games i.succ) := by
  rw [← NNReal.coe_le_coe, NNReal.coe_sum]
  simp only [advantage, coe_nndist, NNReal.dist_eq]
  rw [← sum_succProbability_sub games]
  exact Finset.abs_sum_le_sum_abs _ _

/-- A common bound on each hop gives the usual linear loss in the number of hops. -/
theorem advantage_hybrid_le (games : ℕ → Experiment) (hops : ℕ) (ε : ℝ≥0)
    (hstep : ∀ i < hops, advantage (games i) (games (i + 1)) ≤ ε) :
    advantage (games 0) (games hops) ≤ hops * ε :=
  (advantage_hybrid_le_sum games hops).trans <| by
    simpa using Finset.sum_le_sum fun i hi => hstep i (Finset.mem_range.mp hi)

/-- Polynomially many hops with a common negligible bound have negligible total advantage. -/
theorem negligible_hybrid {games : ℕ → ℕ → Experiment} {hops : ℕ → ℕ} {ε : ℕ → ℝ≥0}
    (hpoly : PolynomiallyBounded hops) (hε : Negligible ε)
    (hstep : ∀ n i, i < hops n → advantage (games n i) (games n (i + 1)) ≤ ε n) :
    Negligible (fun n => advantage (games n 0) (games n (hops n))) :=
  negligible_of_le (hε.polynomiallyBounded_mul hpoly) fun n =>
    advantage_hybrid_le _ _ _ (hstep n)

/-- A hybrid argument with a common hop bound for each admissible adversary. -/
theorem Indistinguishable.hybrid {Adversary : Type*} {games : Adversary → ℕ → ℕ → Experiment}
    {Admissible : Adversary → Prop} {hops : ℕ → ℕ} (hpoly : PolynomiallyBounded hops)
    (hstep : ∀ adversary, Admissible adversary →
      ∃ ε : ℕ → ℝ≥0, Negligible ε ∧ ∀ n i, i < hops n →
        advantage (games adversary n i) (games adversary n (i + 1)) ≤ ε n) :
    Indistinguishable (fun adversary n => games adversary n 0)
      (fun adversary n => games adversary n (hops n)) Admissible := by
  intro adversary ha
  obtain ⟨ε, hε, hstep⟩ := hstep adversary ha
  exact negligible_hybrid hpoly hε hstep

end Cslib.Crypto.Experiment
