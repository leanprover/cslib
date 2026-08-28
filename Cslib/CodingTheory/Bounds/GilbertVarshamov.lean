/-
Copyright (c) 2026 Anthony Chang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Chang, Alex Chai, Erin Jaen
-/

module

public import Cslib.CodingTheory.Code.Defs
public import Cslib.CodingTheory.HammingBall
public import Mathlib.Data.Set.Card.Arithmetic

/-!
# The Gilbert–Varshamov bound

This file proves the Gilbert–Varshamov bound for general (not necessarily linear) codes.

## References

* V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory* (draft, 2023),
  <https://cse.buffalo.edu/faculty/atri/courses/coding-theory/book/web-coding-book.pdf>
-/

@[expose] public section

namespace Cslib.CodingTheory.Code

open scoped ENNReal

variable {α : Type*} {n : ℕ} [DecidableEq α]

/-- If `C` is maximal with respect to inclusion among the codes of minimum distance at least `d`,
then the Hamming balls of radius `d - 1` around its codewords cover the whole space: a word `z`
outside all of them would be at distance at least `d` from every codeword, so that `insert z C`
would still have minimum distance at least `d`, contradicting maximality. -/
lemma iUnion_hammingBall_eq_univ_of_maximal {d : ℕ} {C : Code α n}
    (hC : Maximal (fun D : Code α n => (d : ℕ∞) ≤ D.minDist) C) :
    ⋃ c ∈ C, hammingBall c (d - 1) = Set.univ := by
  refine Set.eq_univ_of_forall fun z => ?_
  by_contra hz
  simp only [Set.mem_iUnion, mem_hammingBall, not_exists, not_le] at hz
  -- every codeword is at distance at least `d` from `z`
  have hdist : ∀ c ∈ C, (d : ℕ∞) ≤ (hammingDist c z : ℕ∞) := fun c hc => by
    have := hz c hc
    exact_mod_cast (by omega : d ≤ hammingDist c z)
  -- so `z` can be added to `C` without decreasing the minimum distance below `d`, hence `z ∈ C`
  have hsub : insert z C ⊆ C :=
    hC.le_of_ge (le_minDist_insert hC.prop hdist) (Set.subset_insert z C)
  simpa using hz z (hsub (Set.mem_insert z C))

/-- Over a finite alphabet, there is a code that is maximal with respect to inclusion among the
codes of minimum distance at least `d`: the family of such codes is finite and nonempty (it
contains the empty code). -/
lemma exists_maximal_le_minDist [Finite α] (d : ℕ∞) :
    ∃ C : Code α n, Maximal (fun D : Code α n => d ≤ D.minDist) C :=
  (Set.toFinite {D : Code α n | d ≤ D.minDist}).exists_maximal ⟨∅, by simp [minDist]⟩

variable [Fintype α]

/-- Packing bound: if `C` is maximal with respect to inclusion among the codes of minimum
distance at least `d`, then `q ^ n ≤ |C| · Vol_q(n, d - 1)` (where `q = |α|`), since the `|C|`
Hamming balls of radius `d - 1` around the codewords cover the `q ^ n` words. -/
lemma card_pow_le_ncard_mul_hammingVolume_of_maximal {d : ℕ} {C : Code α n}
    (hC : Maximal (fun D : Code α n => (d : ℕ∞) ≤ D.minDist) C) :
    Fintype.card α ^ n ≤ C.ncard * hammingVolume (Fintype.card α) n (d - 1) := by
  have hfin : C.Finite := Set.toFinite C
  calc Fintype.card α ^ n
      = (Set.univ : Set (Fin n → α)).ncard := by simp
    _ = (⋃ c ∈ hfin.toFinset, hammingBall c (d - 1)).ncard := by
        rw [← iUnion_hammingBall_eq_univ_of_maximal hC]
        simp only [Set.Finite.mem_toFinset]
    _ ≤ ∑ c ∈ hfin.toFinset, (hammingBall c (d - 1)).ncard :=
        hfin.toFinset.set_ncard_biUnion_le _
    _ = ∑ _c ∈ hfin.toFinset, hammingVolume (Fintype.card α) n (d - 1) :=
        Finset.sum_congr rfl fun c _ => ncard_hammingBall c (d - 1)
    _ = C.ncard * hammingVolume (Fintype.card α) n (d - 1) := by
        rw [Finset.sum_const, smul_eq_mul, Set.ncard_eq_toFinset_card C hfin]

/-- Gilbert–Varshamov bound, combinatorial form: for every `d` there is a code of minimum
distance at least `d` with `q ^ n ≤ |C| · Vol_q(n, d - 1)`, where `q = |α|`. -/
theorem gilbert_varshamov_ncard (d : ℕ) :
    ∃ C : Code α n, (d : ℕ∞) ≤ C.minDist ∧
      Fintype.card α ^ n ≤ C.ncard * hammingVolume (Fintype.card α) n (d - 1) := by
  obtain ⟨C, hC⟩ := exists_maximal_le_minDist (α := α) (n := n) d
  exact ⟨C, hC.prop, card_pow_le_ncard_mul_hammingVolume_of_maximal hC⟩

/-- Gilbert–Varshamov bound: over an alphabet of size `q ≥ 2`, for every `0 ≤ δ < 1 - 1 / q`
and every block length `n ≥ 1` there is a code of rate at least `1 - H_q(δ)` and relative minimum
distance at least `δ`. Here `H_q` is the `q`-ary entropy function `Real.qaryEntropy`, which is
measured in nats, hence the division by `log q`. -/
theorem gilbert_varshamov (hq : 2 ≤ Fintype.card α) (hn : 1 ≤ n) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1 - 1 / (Fintype.card α : ℝ)) :
    ∃ C : Code α n,
      1 - Real.qaryEntropy (Fintype.card α) δ / Real.log (Fintype.card α) ≤ C.rate ∧
      ENNReal.ofReal δ ≤ C.relMinDist := by
  set q : ℕ := Fintype.card α
  have hq1 : (1 : ℝ) < q := by exact_mod_cast Nat.lt_of_lt_of_le one_lt_two hq
  have hq0 : (0 : ℝ) < q := one_pos.trans hq1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  -- the designed distance `d = max ⌈δ n⌉ 1`
  set d : ℕ := max ⌈δ * n⌉₊ 1 with hd_def
  have hδnd : δ * n ≤ (d : ℝ) :=
    calc δ * n ≤ (⌈δ * n⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (d : ℝ) := by exact_mod_cast le_max_left _ _
  obtain ⟨C, hCd, hCcard⟩ := gilbert_varshamov_ncard (α := α) (n := n) d
  -- the packing radius `r = d - 1` satisfies `r ≤ δ n`, hence `r / n ≤ δ < 1 - 1 / q`
  set r : ℕ := d - 1 with hr_def
  have hrδn : (r : ℝ) ≤ δ * n := by
    rcases Nat.eq_zero_or_pos ⌈δ * n⌉₊ with h | h
    -- if `⌈δ n⌉ = 0` then `r = 0` and the claim is `0 ≤ δ n`
    · have hr0 : r = 0 := by omega
      rw [hr0, Nat.cast_zero]
      exact mul_nonneg hδ0 hn0.le
    -- otherwise `r = ⌈δ n⌉ - 1 < ⌈δ n⌉`, which means `r < δ n`
    · have hrlt : r < ⌈δ * n⌉₊ := by omega
      exact (Nat.lt_ceil.mp hrlt).le
  have hrn_le_δ : (r : ℝ) / n ≤ δ := by
    rw [div_le_iff₀ hn0]
    exact hrδn
  have hrange : (r : ℝ) / n ≤ 1 - 1 / (q : ℝ) := hrn_le_δ.trans hδ1.le
  set H : ℝ := Real.qaryEntropy q ((r : ℝ) / n)
  have hVol : (hammingVolume q n r : ℝ) ≤ (q : ℝ) ^ ((n : ℝ) * H / Real.log q) :=
    hammingVolume_le_pow_mul_entropy hq hn hrange
  -- the packing bound forces `C` to be nonempty, so its cardinality is positive
  have hncard : (0 : ℝ) < (C.ncard : ℝ) := by
    have : 0 < C.ncard := by
      rcases Nat.eq_zero_or_pos C.ncard with h0 | h0
      · rw [h0, zero_mul] at hCcard
        exact absurd hCcard (not_le.mpr (pow_pos (by omega) n))
      · exact h0
    exact_mod_cast this
  -- the packing bound in `ℝ`: `q ^ n ≤ |C| · Vol_q(n, r)`
  have hcardR : (q : ℝ) ^ (n : ℝ) ≤ (C.ncard : ℝ) * (hammingVolume q n r : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast hCcard
  -- hence `|C| ≥ q ^ (n - n H / log q)`
  have key : (q : ℝ) ^ ((n : ℝ) - (n : ℝ) * H / Real.log q) ≤ (C.ncard : ℝ) := by
    rw [Real.rpow_sub hq0, div_le_iff₀ (Real.rpow_pos_of_pos hq0 _)]
    calc (q : ℝ) ^ (n : ℝ)
        ≤ (C.ncard : ℝ) * (hammingVolume q n r : ℝ) := hcardR
      _ ≤ (C.ncard : ℝ) * (q : ℝ) ^ ((n : ℝ) * H / Real.log q) :=
          mul_le_mul_of_nonneg_left hVol hncard.le
  -- taking `logb q`, the dimension is at least `n - n H / log q`
  have hdim : (n : ℝ) - (n : ℝ) * H / Real.log q ≤ C.dim := by
    have hlog := Real.logb_le_logb_of_le hq1 (Real.rpow_pos_of_pos hq0 _) key
    rwa [Real.logb_rpow hq0 hq1.ne'] at hlog
  -- so the rate is at least `1 - H / log q`
  have hrate1 : 1 - H / Real.log q ≤ C.rate := by
    change 1 - H / Real.log q ≤ C.dim / n
    rw [le_div_iff₀ hn0]
    calc (1 - H / Real.log q) * n = n - n * H / Real.log q := by ring
      _ ≤ C.dim := hdim
  -- monotonicity of the entropy on `[0, 1 - 1 / q]` turns `H_q(r / n)` into `H_q(δ)`
  have hmono : H ≤ Real.qaryEntropy q δ :=
    (Real.qaryEntropy_strictMonoOn hq).monotoneOn
      (Set.mem_Icc.mpr ⟨by positivity, hrange⟩)
      (Set.mem_Icc.mpr ⟨hδ0, hδ1.le⟩) hrn_le_δ
  have hrate : 1 - Real.qaryEntropy q δ / Real.log q ≤ C.rate := by
    refine le_trans ?_ hrate1
    gcongr
  -- the relative minimum distance is at least `d / n ≥ δ`
  have hdist : ENNReal.ofReal δ ≤ C.relMinDist := by
    change ENNReal.ofReal δ ≤ (C.minDist : ℝ≥0∞) / (n : ℝ≥0∞)
    refine le_trans ?_ (ENNReal.div_le_div_right (ENat.toENNReal_le.mpr hCd) _)
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast (by omega : n ≠ 0)))
      (Or.inl (ENNReal.natCast_ne_top n))]
    calc ENNReal.ofReal δ * (n : ℝ≥0∞)
        = ENNReal.ofReal (δ * n) := by
          rw [← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_mul hδ0]
      _ ≤ ENNReal.ofReal (d : ℝ) := ENNReal.ofReal_le_ofReal hδnd
      _ = ((d : ℕ∞) : ℝ≥0∞) := by
          rw [ENNReal.ofReal_natCast d]
          exact_mod_cast rfl
  exact ⟨C, hrate, hdist⟩

end Cslib.CodingTheory.Code
