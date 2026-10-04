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

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Section 9.3.
-/

@[expose] public section

namespace Cslib.Crypto.Game

/-- A uniformly selected experiment accepts with the average of its acceptance probabilities. -/
theorem winProbability_uniform {α : Type*} [Fintype α] [Nonempty α] (games : α → Game) :
    winProbability ((PMF.uniformOfFintype α).bind games) =
      (∑ a, winProbability (games a)) / Fintype.card α := by
  simp only [winProbability, Probability.PMF.bind_apply_toReal, PMF.uniformOfFintype_apply,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, inv_mul_eq_div, Finset.sum_div]

/-- Randomly choosing an adjacent hybrid telescopes signed gaps.
Unused indices run the same rejecting game on both sides. This gives one reduction for every
security parameter, with loss `capacity`, without selecting a length-dependent best hop. -/
theorem winProbability_hybrid_average (games : ℕ → Game) (hops capacity : ℕ) [NeZero capacity]
    (hle : hops ≤ capacity) :
    winProbability (games 0) - winProbability (games hops) = (capacity : ℝ) *
      (winProbability
        ((PMF.uniformOfFintype (Fin capacity)).bind
          (fun i => if i.val < hops then games i.val else PMF.pure false)) - winProbability
        ((PMF.uniformOfFintype (Fin capacity)).bind
          (fun i => if i.val < hops then games (i.val + 1) else PMF.pure false))) := by
  have hsum : (∑ i : Fin capacity, if i.val < hops then
      winProbability (games i.val) - winProbability (games (i.val + 1)) else 0) =
      winProbability (games 0) - winProbability (games hops) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => if i < hops then
      winProbability (games i) - winProbability (games (i + 1)) else 0),
      ← Finset.sum_range_sub' (fun i => winProbability (games i)),
      ← Finset.sum_range_add_sum_Ico _ hle]
    simp +contextual [Finset.sum_ite_of_true, Finset.sum_ite_of_false]
  rw [winProbability_uniform, winProbability_uniform]
  simp only [Fintype.card_fin, ← sub_div, ← Finset.sum_sub_distrib]
  have hdiff (i : Fin capacity) :
      winProbability (if i.val < hops then games i.val else PMF.pure false) -
        winProbability (if i.val < hops then games (i.val + 1) else PMF.pure false) =
      if i.val < hops then winProbability (games i.val) - winProbability (games (i.val + 1))
        else 0 := by split_ifs <;> simp
  have hcapacity : (capacity : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne capacity
  simp only [hdiff, hsum, mul_div_cancel₀ _ hcapacity]

/-- Averaging adjacent hybrids also preserves absolute distinguishing advantage, with the
sampling-range loss and no length-dependent choice of the best hop. -/
theorem advantage_hybrid_average (games : ℕ → Game) (hops capacity : ℕ) [NeZero capacity]
    (hle : hops ≤ capacity) :
    advantage (games 0) (games hops) = (capacity : ℝ) *
      advantage
        ((PMF.uniformOfFintype (Fin capacity)).bind
          (fun i => if i.val < hops then games i.val else PMF.pure false))
        ((PMF.uniformOfFintype (Fin capacity)).bind
          (fun i => if i.val < hops then games (i.val + 1) else PMF.pure false)) := by
  rw [advantage, advantage, winProbability_hybrid_average games hops capacity hle, abs_mul,
    Nat.abs_cast]

/-- Local reductions with a common signed loss combine into one uniformly selected reduction.
The proof needs no choice of a best hop or advice depending on the security parameter. -/
theorem winProbability_hybrid_reduction (games real ideal : ℕ → Game)
    (hops capacity : ℕ) [NeZero capacity] (hle : hops ≤ capacity) (loss : ℝ)
    (hstep : ∀ i < hops, winProbability (games i) - winProbability (games (i + 1)) =
      loss * (winProbability (real i) - winProbability (ideal i))) :
    winProbability (games 0) - winProbability (games hops) = (capacity : ℝ) * loss *
      (winProbability ((PMF.uniformOfFintype (Fin capacity)).bind
        (fun i => if i.val < hops then real i.val else PMF.pure false)) -
      winProbability ((PMF.uniformOfFintype (Fin capacity)).bind
        (fun i => if i.val < hops then ideal i.val else PMF.pure false))) := by
  have hterm (i : Fin capacity) :
      winProbability (if i.val < hops then games i.val else PMF.pure false) -
        winProbability (if i.val < hops then games (i.val + 1) else PMF.pure false) =
      loss * (winProbability (if i.val < hops then real i.val else PMF.pure false) -
        winProbability (if i.val < hops then ideal i.val else PMF.pure false)) := by
    split_ifs with hi
    · exact hstep i.val hi
    · simp
  rw [winProbability_hybrid_average games hops capacity hle]
  simp only [winProbability_uniform, Fintype.card_fin, ← sub_div, ← Finset.sum_sub_distrib,
    hterm, ← Finset.mul_sum]
  ring

/-- The advantage between the endpoints is at most the sum of all adjacent advantages. -/
theorem advantage_hybrid_le_sum (games : ℕ → Game) (hops : ℕ) :
    advantage (games 0) (games hops) ≤
      ∑ i ∈ Finset.range hops, advantage (games i) (games (i + 1)) :=
  dist_le_range_sum_dist (fun i => winProbability (games i)) hops

/-- A common bound on each hop gives the usual linear loss in the number of hops. -/
theorem advantage_hybrid_le (games : ℕ → Game) (hops : ℕ) (ε : ℝ)
    (hstep : ∀ i < hops, advantage (games i) (games (i + 1)) ≤ ε) :
    advantage (games 0) (games hops) ≤ (hops : ℝ) * ε :=
  (dist_le_range_sum_of_dist_le (f := fun i => winProbability (games i)) (d := fun _ => ε) hops
    fun hi => hstep _ hi).trans_eq (by simp)

/-- Polynomially many hops with a common negligible bound have negligible total advantage. -/
theorem negligible_hybrid {games : ℕ → ℕ → Game} {hops : ℕ → ℕ} {ε : ℕ → ℝ}
    (hpoly : PolynomiallyBounded hops) (hε : Negligible ε)
    (hstep : ∀ n i, i < hops n → advantage (games n i) (games n (i + 1)) ≤ ε n) :
    Negligible (fun n => advantage (games n 0) (games n (hops n))) :=
  negligible_of_le (hε.polynomiallyBounded_mul hpoly)
    (fun _ => advantage_nonneg _ _) (fun n => advantage_hybrid_le _ _ _ (hstep n))

/-- A hybrid argument with a common hop bound for each admissible adversary. -/
theorem Secure.hybrid {Adversary : Type*} {games : Adversary → ℕ → ℕ → Game}
    {Admissible : Adversary → Prop} {hops : ℕ → ℕ} (hpoly : PolynomiallyBounded hops)
    (hstep : ∀ adversary, Admissible adversary →
      ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n i, i < hops n →
        advantage (games adversary n i) (games adversary n (i + 1)) ≤ ε n) :
    Secure (fun adversary n => games adversary n 0)
      (fun adversary n => games adversary n (hops n)) Admissible := by
  intro adversary ha
  obtain ⟨ε, hε, hstep⟩ := hstep adversary ha
  exact negligible_hybrid hpoly hε hstep

/-- A reduction may lose a polynomial factor and incur a negligible error. The loss and the
error may depend on the whole adversary, while `reduce` maps whole adversaries and does not
depend on the security parameter. -/
theorem Secure.of_reduction_with_loss {Source Target : Type*}
    {sourceReal sourceIdeal : Source → ℕ → Game} {targetReal targetIdeal : Target → ℕ → Game}
    {SourceAdmissible : Source → Prop} {TargetAdmissible : Target → Prop}
    (h : Secure sourceReal sourceIdeal SourceAdmissible) (reduce : Target → Source)
    (hadmissible : ∀ adversary, TargetAdmissible adversary → SourceAdmissible (reduce adversary))
    (hbound : ∀ adversary, TargetAdmissible adversary →
      ∃ (loss : ℕ → ℕ) (error : ℕ → ℝ), PolynomiallyBounded loss ∧ Negligible error ∧ ∀ n,
        advantage (targetReal adversary n) (targetIdeal adversary n) ≤
          loss n * advantage (sourceReal (reduce adversary) n) (sourceIdeal (reduce adversary) n) +
            error n) : Secure targetReal targetIdeal TargetAdmissible := by
  intro adversary ha
  obtain ⟨loss, error, hloss, herror, hbound⟩ := hbound adversary ha
  exact negligible_of_le
    (((h _ (hadmissible adversary ha)).polynomiallyBounded_mul hloss).add herror)
    (fun _ => advantage_nonneg _ _) hbound

end Cslib.Crypto.Game
