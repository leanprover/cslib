/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Game

/-!
# Polynomially many semantic game hops

The concrete hybrid inequality adds the advantages of adjacent games. The asymptotic theorem
requires a single negligible bound that works for every hop at each security parameter. Merely
assuming negligibility separately for each fixed hop does not suffice when the number of hops
grows with the parameter. The common bound may depend on the distinguisher.

The signed telescoping identities are stated over the reals, where subtraction is exact; the
advantage bounds that follow from them are stated in the nonnegative reals.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Section 9.3.
-/

@[expose] public section

namespace Cslib.Crypto.Game

open Probability
open scoped NNReal

/-- A uniformly selected experiment succeeds with the average of its success probabilities. -/
theorem succProbability_uniform {α : Type*} [Fintype α] [Nonempty α] (games : α → Game) :
    succProbability ((PMF.uniformOfFintype α).bind games) =
      (∑ a, succProbability (games a)) / Fintype.card α := by
  apply NNReal.eq
  simp only [succProbability, ENNReal.coe_toNNReal_eq_toReal, Probability.PMF.bind_apply_toReal]
  simp [ENNReal.coe_toNNReal_eq_toReal, inv_mul_eq_div, Finset.sum_div]

/-- Randomly choosing an adjacent hybrid telescopes signed gaps.
Unused indices run the same rejecting game on both sides. This gives one reduction for every
security parameter, with loss `capacity`, without selecting a parameter-dependent best hop. -/
theorem succProbability_hybrid_average (games : ℕ → Game) (hops capacity : ℕ) [NeZero capacity]
    (hle : hops ≤ capacity) :
    (succProbability (games 0) : ℝ) - succProbability (games hops) = (capacity : ℝ) *
      (succProbability
        ((PMF.uniformOfFintype (Fin capacity)).bind
          (fun i => if i.val < hops then games i.val else PMF.pure false)) - succProbability
        ((PMF.uniformOfFintype (Fin capacity)).bind
          (fun i => if i.val < hops then games (i.val + 1) else PMF.pure false))) := by
  have hsum : (∑ i : Fin capacity, if i.val < hops then
      (succProbability (games i.val) : ℝ) - succProbability (games (i.val + 1)) else 0) =
      (succProbability (games 0) : ℝ) - succProbability (games hops) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => if i < hops then
      (succProbability (games i) : ℝ) - succProbability (games (i + 1)) else 0),
      ← Finset.sum_range_sub' (fun i => (succProbability (games i) : ℝ)),
      ← Finset.sum_range_add_sum_Ico _ hle]
    simp +contextual [Finset.sum_ite_of_true, Finset.sum_ite_of_false]
  have hdiff (i : Fin capacity) :
      (succProbability (if i.val < hops then games i.val else PMF.pure false) : ℝ) -
        succProbability (if i.val < hops then games (i.val + 1) else PMF.pure false) =
      if i.val < hops then
        (succProbability (games i.val) : ℝ) - succProbability (games (i.val + 1)) else 0 := by
    split_ifs <;> simp [succProbability]
  have hcapacity : (capacity : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne capacity
  rw [succProbability_uniform, succProbability_uniform]
  simp only [NNReal.coe_div, NNReal.coe_sum, NNReal.coe_natCast, Fintype.card_fin, ← sub_div,
    ← Finset.sum_sub_distrib, hdiff, hsum, mul_div_cancel₀ _ hcapacity]

/-- Averaging adjacent hybrids also preserves distinguishing advantage, with the
sampling-range loss and no parameter-dependent choice of the best hop. -/
theorem advantage_hybrid_average (games : ℕ → Game) (hops capacity : ℕ) [NeZero capacity]
    (hle : hops ≤ capacity) :
    advantage (games 0) (games hops) = capacity *
      advantage
        ((PMF.uniformOfFintype (Fin capacity)).bind
          (fun i => if i.val < hops then games i.val else PMF.pure false))
        ((PMF.uniformOfFintype (Fin capacity)).bind
          (fun i => if i.val < hops then games (i.val + 1) else PMF.pure false)) := by
  apply NNReal.eq
  rw [NNReal.coe_mul, coe_advantage, coe_advantage, NNReal.coe_natCast,
    succProbability_hybrid_average games hops capacity hle, abs_mul, Nat.abs_cast]

/-- Local reductions with a common signed loss combine into one uniformly selected reduction.
The proof needs no choice of a best hop depending on the security parameter. -/
theorem succProbability_hybrid_reduction (games game1 game2 : ℕ → Game)
    (hops capacity : ℕ) [NeZero capacity] (hle : hops ≤ capacity) (loss : ℝ)
    (hstep : ∀ i < hops, (succProbability (games i) : ℝ) - succProbability (games (i + 1)) =
      loss * (succProbability (game1 i) - succProbability (game2 i))) :
    (succProbability (games 0) : ℝ) - succProbability (games hops) = (capacity : ℝ) * loss *
      (succProbability ((PMF.uniformOfFintype (Fin capacity)).bind
        (fun i => if i.val < hops then game1 i.val else PMF.pure false)) -
      succProbability ((PMF.uniformOfFintype (Fin capacity)).bind
        (fun i => if i.val < hops then game2 i.val else PMF.pure false))) := by
  have hterm (i : Fin capacity) :
      (succProbability (if i.val < hops then games i.val else PMF.pure false) : ℝ) -
        succProbability (if i.val < hops then games (i.val + 1) else PMF.pure false) =
      loss * (succProbability (if i.val < hops then game1 i.val else PMF.pure false) -
        succProbability (if i.val < hops then game2 i.val else PMF.pure false)) := by
    split_ifs with hi
    · exact hstep i.val hi
    · simp [succProbability]
  rw [succProbability_hybrid_average games hops capacity hle]
  simp only [succProbability_uniform, NNReal.coe_div, NNReal.coe_sum, NNReal.coe_natCast,
    Fintype.card_fin, ← sub_div, ← Finset.sum_sub_distrib, hterm, ← Finset.mul_sum]
  ring

/-- The advantage between the endpoints is at most the sum of all adjacent advantages. -/
theorem advantage_hybrid_le_sum (games : ℕ → Game) (hops : ℕ) :
    advantage (games 0) (games hops) ≤
      ∑ i ∈ Finset.range hops, advantage (games i) (games (i + 1)) := by
  rw [← NNReal.coe_le_coe, NNReal.coe_sum]
  simpa only [advantage, coe_nndist] using
    dist_le_range_sum_dist (fun i => succProbability (games i)) hops

/-- A common bound on each hop gives the usual linear loss in the number of hops. -/
theorem advantage_hybrid_le (games : ℕ → Game) (hops : ℕ) (ε : ℝ≥0)
    (hstep : ∀ i < hops, advantage (games i) (games (i + 1)) ≤ ε) :
    advantage (games 0) (games hops) ≤ hops * ε :=
  (advantage_hybrid_le_sum games hops).trans <| by
    simpa using Finset.sum_le_sum fun i hi => hstep i (Finset.mem_range.mp hi)

/-- Polynomially many hops with a common negligible bound have negligible total advantage. -/
theorem negligible_hybrid {games : ℕ → ℕ → Game} {hops : ℕ → ℕ} {ε : ℕ → ℝ≥0}
    (hpoly : PolynomiallyBounded hops) (hε : Negligible ε)
    (hstep : ∀ n i, i < hops n → advantage (games n i) (games n (i + 1)) ≤ ε n) :
    Negligible (fun n => advantage (games n 0) (games n (hops n))) :=
  negligible_of_le (hε.polynomiallyBounded_mul hpoly) fun n =>
    advantage_hybrid_le _ _ _ (hstep n)

/-- A hybrid argument with a common hop bound for each admissible adversary. -/
theorem Indistinguishable.hybrid {Adversary : Type*} {games : Adversary → ℕ → ℕ → Game}
    {Admissible : Adversary → Prop} {hops : ℕ → ℕ} (hpoly : PolynomiallyBounded hops)
    (hstep : ∀ adversary, Admissible adversary →
      ∃ ε : ℕ → ℝ≥0, Negligible ε ∧ ∀ n i, i < hops n →
        advantage (games adversary n i) (games adversary n (i + 1)) ≤ ε n) :
    Indistinguishable (fun adversary n => games adversary n 0)
      (fun adversary n => games adversary n (hops n)) Admissible := by
  intro adversary ha
  obtain ⟨ε, hε, hstep⟩ := hstep adversary ha
  exact negligible_hybrid hpoly hε hstep

end Cslib.Crypto.Game
