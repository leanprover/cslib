/-
Copyright (c) 2026 Anthony Chang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Chang, Alex Chai, Erin Jaen
-/

module

public import Cslib.Init
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Set.Card
public import Mathlib.InformationTheory.Hamming
import all Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Hamming balls and their volume

We define Hamming balls and their volumes in this file.
Hamming balls are essential for combinatorial bounds in coding theory.

## References

* V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory* (draft, 2023),
  <https://cse.buffalo.edu/faculty/atri/courses/coding-theory/book/web-coding-book.pdf>
-/

@[expose] public section

namespace Cslib.CodingTheory

open Finset

/-- The volume `Vol_q(n, r) = ∑_{i = 0}^{r} C(n, i) (q - 1) ^ i` of a Hamming ball of radius
`r` in the space of words of length `n` over an alphabet of size `q`. -/
def hammingVolume (q n r : ℕ) : ℕ := ∑ i ∈ range (r + 1), n.choose i * (q - 1) ^ i

@[simp]
lemma hammingVolume_zero (q n : ℕ) : hammingVolume q n 0 = 1 := by simp [hammingVolume]

lemma hammingVolume_pos (q n r : ℕ) : 0 < hammingVolume q n r :=
  sum_pos' (fun _ _ => Nat.zero_le _) ⟨0, mem_range.mpr r.succ_pos, by simp⟩

/-- For `2 ≤ q` and `1 ≤ n`, the volume of a Hamming ball of radius `r ≤ (1 - 1 / q) n` is at
most `q ^ (n H_q(r / n))`, where `H_q` is the `q`-ary entropy function `Real.qaryEntropy` (which
is measured in nats, hence the division by `log q`). -/
lemma hammingVolume_le_pow_mul_entropy {q n r : ℕ} (hq : 2 ≤ q) (hn : 1 ≤ n)
    (hr : (r : ℝ) / n ≤ 1 - 1 / q) :
    (hammingVolume q n r : ℝ) ≤
      (q : ℝ) ^ ((n : ℝ) * Real.qaryEntropy q ((r : ℝ) / n) / Real.log q) := by
  -- if `r = 0` then the volume is `1` and the exponent vanishes
  obtain rfl | hr0 := Nat.eq_zero_or_pos r
  · simp
  -- write `l = r / n`; then `0 < l ≤ 1 - 1 / q < 1`
  set l : ℝ := (r : ℝ) / n with hl
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hq0 : (0 : ℝ) < q := by positivity
  have hl0 : 0 < l := div_pos (by exact_mod_cast hr0) hn0
  have hl1 : l < 1 := hr.trans_lt (sub_lt_self 1 (by positivity))
  have h1l : 0 < 1 - l := sub_pos.mpr hl1
  have hql : (0 : ℝ) < (q : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast hq)
  have hrn : r < n := by exact_mod_cast (div_lt_one hn0).mp hl1
  -- as `n l = r`, the definition of `H_q` gives
  -- `n H_q(l) = r log (q - 1) + r log l⁻¹ + (n - r) log (1 - l)⁻¹`
  have hnl : (n : ℝ) * l = r := by rw [hl, mul_comm, div_mul_cancel₀ _ hn0.ne']
  have hent : (n : ℝ) * Real.qaryEntropy q l
      = (r : ℝ) * Real.log ((q : ℝ) - 1)
        + ((r : ℝ) * Real.log l⁻¹ + ((n - r : ℕ) : ℝ) * Real.log (1 - l)⁻¹) := by
    simp only [Real.qaryEntropy, Real.binEntropy]
    push_cast [Nat.cast_sub hrn.le]
    rw [← hnl]
    ring
  -- as `1 < q`, `q ^ (x / log q) = exp x`
  have hexp : (q : ℝ) ^ ((n : ℝ) * Real.qaryEntropy q l / Real.log q)
      = Real.exp ((n : ℝ) * Real.qaryEntropy q l) := by
    rw [Real.rpow_def_of_pos hq0, mul_comm (Real.log _),
      div_mul_cancel₀ _ (Real.log_pos (by exact_mod_cast hq)).ne']
  -- so `q ^ (n H_q(l) / log q) = (q - 1) ^ r / (l ^ r (1 - l) ^ (n - r))`
  have hRHS : Real.exp ((n : ℝ) * Real.qaryEntropy q l)
      = ((q : ℝ) - 1) ^ r / (l ^ r * (1 - l) ^ (n - r)) := by
    rw [hent, Real.exp_add, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul,
      Real.exp_nat_mul, Real.exp_log hql, Real.exp_log (inv_pos.mpr hl0),
      Real.exp_log (inv_pos.mpr h1l), inv_pow, inv_pow, ← mul_inv, ← div_eq_mul_inv]
  -- hence it suffices to show `Vol_q(n, r) l ^ r (1 - l) ^ (n - r) ≤ (q - 1) ^ r`
  rw [hexp, hRHS, le_div_iff₀ (by positivity)]
  -- with `θ = l / ((q - 1) (1 - l))`, the hypothesis `l ≤ 1 - 1 / q` says exactly `θ ≤ 1`
  have htheta : l ≤ ((q : ℝ) - 1) * (1 - l) := by
    have h : l * q ≤ (q : ℝ) - 1 :=
      calc l * q ≤ (1 - 1 / (q : ℝ)) * q := mul_le_mul_of_nonneg_right hr hq0.le
        _ = q - 1 := by field_simp
    calc l = l * q - l * ((q : ℝ) - 1) := by ring
      _ ≤ ((q : ℝ) - 1) - l * ((q : ℝ) - 1) := sub_le_sub_right h _
      _ = ((q : ℝ) - 1) * (1 - l) := by ring
  -- the binomial theorem: `∑_{i ≤ n} C(n, i) l ^ i (1 - l) ^ (n - i) = (l + (1 - l)) ^ n = 1`
  have hbinom :
      ∑ i ∈ range (n + 1), l ^ i * (1 - l) ^ (n - i) * (n.choose i : ℝ) = 1 := by
    rw [← add_pow, add_sub_cancel, one_pow]
  calc (hammingVolume q n r : ℝ) * (l ^ r * (1 - l) ^ (n - r))
      = ∑ i ∈ range (r + 1),
          (n.choose i : ℝ) * ((q : ℝ) - 1) ^ i * (l ^ r * (1 - l) ^ (n - r)) := by
        rw [hammingVolume, Nat.cast_sum, sum_mul]
        refine sum_congr rfl fun i _ => ?_
        push_cast [Nat.cast_sub (show 1 ≤ q by omega)]
        ring
    -- for `i ≤ r`, the `i`-th term is `(q - 1) ^ r C(n, i) l ^ i (1 - l) ^ (n - i) θ ^ (r - i)`,
    -- and `θ ^ (r - i) ≤ 1`
    _ ≤ ∑ i ∈ range (r + 1),
          ((q : ℝ) - 1) ^ r * (l ^ i * (1 - l) ^ (n - i) * (n.choose i : ℝ)) := by
        refine sum_le_sum fun i hi => ?_
        have hir : i ≤ r := mem_range_succ_iff.mp hi
        have h1 : l ^ r = l ^ i * l ^ (r - i) := by rw [← pow_add]; congr 1; omega
        have h2 : (1 - l) ^ (n - i) = (1 - l) ^ (n - r) * (1 - l) ^ (r - i) := by
          rw [← pow_add]; congr 1; omega
        have h3 : ((q : ℝ) - 1) ^ r = ((q : ℝ) - 1) ^ i * ((q : ℝ) - 1) ^ (r - i) := by
          rw [← pow_add]; congr 1; omega
        calc (n.choose i : ℝ) * ((q : ℝ) - 1) ^ i * (l ^ r * (1 - l) ^ (n - r))
            = (n.choose i : ℝ) * ((q : ℝ) - 1) ^ i * (l ^ i * (1 - l) ^ (n - r))
                * l ^ (r - i) := by rw [h1]; ring
          _ ≤ (n.choose i : ℝ) * ((q : ℝ) - 1) ^ i * (l ^ i * (1 - l) ^ (n - r))
                * (((q : ℝ) - 1) * (1 - l)) ^ (r - i) := by gcongr
          _ = ((q : ℝ) - 1) ^ r * (l ^ i * (1 - l) ^ (n - i) * (n.choose i : ℝ)) := by
              rw [h2, h3, mul_pow]; ring
    -- extend the sum from `i ≤ r` to `i ≤ n`
    _ ≤ ∑ i ∈ range (n + 1),
          ((q : ℝ) - 1) ^ r * (l ^ i * (1 - l) ^ (n - i) * (n.choose i : ℝ)) :=
        sum_le_sum_of_subset_of_nonneg
          (range_subset_range.mpr (Nat.succ_le_succ hrn.le)) fun i _ _ => by positivity
    _ = ((q : ℝ) - 1) ^ r := by rw [← mul_sum, hbinom, mul_one]

variable {α : Type*} {n : ℕ} [DecidableEq α]

/-- The Hamming ball of radius `r` around the word `x`: all words at Hamming distance at most
`r` from `x`. -/
def hammingBall (x : Fin n → α) (r : ℕ) : Set (Fin n → α) := {y | hammingDist x y ≤ r}

@[simp]
lemma mem_hammingBall {x y : Fin n → α} {r : ℕ} : y ∈ hammingBall x r ↔ hammingDist x y ≤ r :=
  Iff.rfl

lemma mem_hammingBall_self (x : Fin n → α) (r : ℕ) : x ∈ hammingBall x r := by simp

/-- The set of coordinates on which the words `x` and `y` disagree; its cardinality is the Hamming
distance `hammingDist x y` (see `card_disagree`). -/
def disagree (x y : Fin n → α) : Finset (Fin n) := {j | x j ≠ y j}

@[simp]
lemma card_disagree (x y : Fin n → α) : (disagree x y).card = hammingDist x y := rfl

@[simp]
lemma mem_disagree {x y : Fin n → α} {j : Fin n} : j ∈ disagree x y ↔ x j ≠ y j := by
  simp [disagree]

variable [Fintype α]

/-- For a fixed set `S` of coordinates, there are exactly `(q - 1) ^ |S|` words that disagree with
`x` precisely on `S`, where `q = |α|`: they can take any of the `q - 1` values different from `x j`
at each `j ∈ S`, and must agree with `x` elsewhere. -/
lemma ncard_setOf_disagree_eq (x : Fin n → α) (S : Finset (Fin n)) :
    {y : Fin n → α | disagree x y = S}.ncard = (Fintype.card α - 1) ^ S.card := by
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
  -- the words disagreeing with `x` exactly on `S` are the elements of the product of the sets
  -- `{x j}ᶜ` for `j ∈ S` and `{x j}` for `j ∉ S`
  have hset : (univ.filter fun y : Fin n → α => disagree x y = S)
      = Fintype.piFinset fun j => if j ∈ S then {x j}ᶜ else {x j} := by
    ext y
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    have key : ∀ j : Fin n,
        (y j ∈ if j ∈ S then ({x j}ᶜ : Finset α) else {x j}) ↔ (x j ≠ y j ↔ j ∈ S) := by
      intro j
      by_cases hj : j ∈ S <;> simp [hj, eq_comm]
    rw [Finset.ext_iff]
    simp only [mem_disagree, key]
  rw [hset, Fintype.card_piFinset]
  simp only [apply_ite Finset.card, card_compl, card_singleton]
  rw [Fintype.prod_ite_mem, prod_const]

/-- There are exactly `C(n, i) (q - 1) ^ i` words at Hamming distance exactly `i` from `x`, where
`q = |α|`: partition them according to the set of coordinates on which they disagree with `x`. -/
lemma ncard_hammingSphere (x : Fin n → α) (i : ℕ) :
    {y : Fin n → α | hammingDist x y = i}.ncard = n.choose i * (Fintype.card α - 1) ^ i := by
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
  -- the disagreement set of a word at distance `i` from `x` is a subset of `Fin n` of size `i`
  have hmaps : ((univ.filter fun y : Fin n → α => hammingDist x y = i : Finset _) :
      Set (Fin n → α)).MapsTo (fun y => disagree x y) ((univ : Finset (Fin n)).powersetCard i) := by
    intro y hy
    rw [mem_coe, mem_filter] at hy
    rw [mem_coe, mem_powersetCard]
    exact ⟨filter_subset _ _, hy.2⟩
  rw [card_eq_sum_card_fiberwise hmaps]
  -- each fibre has `(q - 1) ^ i` elements and there are `C(n, i)` of them
  trans ∑ _S ∈ (univ : Finset (Fin n)).powersetCard i, (Fintype.card α - 1) ^ i
  · refine sum_congr rfl fun S hS => ?_
    obtain ⟨-, rfl⟩ := mem_powersetCard.mp hS
    -- on the fibre over `S` the condition `hammingDist x y = |S|` is automatic
    rw [filter_filter, filter_congr fun y _ =>
      and_iff_right_of_imp fun h => by rw [← card_disagree, h],
      ← Set.toFinset_ofPred, ← Set.ncard_eq_toFinset_card', ncard_setOf_disagree_eq]
  · rw [sum_const, card_powersetCard, card_fin, smul_eq_mul]

/-- A Hamming ball of radius `r` contains exactly `Vol_q(n, r)` words, where `q = |α|`: partition
it into the spheres of radius `0, …, r` and count them with `ncard_hammingSphere`. -/
lemma ncard_hammingBall (x : Fin n → α) (r : ℕ) :
    (hammingBall x r).ncard = hammingVolume (Fintype.card α) n r := by
  rw [hammingBall, hammingVolume, Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
  -- the distance to `x` of a word in the ball lies in `{0, …, r}`
  have hmaps : ((univ.filter fun y : Fin n → α => hammingDist x y ≤ r : Finset _) :
      Set (Fin n → α)).MapsTo (fun y => hammingDist x y) (range (r + 1)) := by
    intro y hy
    rw [mem_coe, mem_filter] at hy
    rw [mem_coe, mem_range]
    exact Nat.lt_succ_of_le hy.2
  rw [card_eq_sum_card_fiberwise hmaps]
  -- the fibre at distance `i ≤ r` is the sphere of radius `i`
  refine sum_congr rfl fun i hi => ?_
  have hir : i ≤ r := mem_range_succ_iff.mp hi
  have hfib : (univ.filter fun y : Fin n → α => hammingDist x y ≤ r).filter
      (fun y => hammingDist x y = i) = univ.filter fun y => hammingDist x y = i := by
    ext y
    simp only [mem_filter, mem_univ, true_and]
    exact and_iff_right_of_imp fun h => h.trans_le hir
  rw [hfib, ← Set.toFinset_ofPred, ← Set.ncard_eq_toFinset_card', ncard_hammingSphere]

end Cslib.CodingTheory
