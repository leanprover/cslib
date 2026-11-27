/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CSLib Contributors
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Nat.Log

/-!
# Divide-and-Conquer Master Theorem

This module formalizes the discrete **Master Theorem** for divide-and-conquer recurrences over `ℕ`,
providing both explicit non-asymptotic closed-form inequalities (suitable for `ℕ → ℝ`, `ℕ → ℕ`,
and `TimeM` cost bounds) and asymptotic `Asymptotics.IsBigO` (`=O[atTop]`) and
`Asymptotics.IsTheta` (`=Θ[atTop]`) characterizations.

## Main Definitions

- `masterExpansion a b B f n`: Exact recursion-tree expansion
  `a ^ Nat.log b n * B + ∑ i ∈ Finset.range (Nat.log b n), a ^ i * f (n / b ^ i)` solving the
  discrete floor-division recurrence `E(n) = a * E(n / b) + f(n)` (`n ≥ b`) with base `B` (`n < b`).

## Main Results

- **Layer 1 (Exact Discrete Recurrence Expansions)**:
  - `rec_le_masterExpansion`, `rec_le_masterExpansion_of_pos`, `masterExpansion_le_rec`:
    Upper and lower recursion-tree bounds for `T(n) ≤ a * T(n / b) + f(n)` (and `≥`).
  - `rec_div_ceil_le_masterExpansion`: Upper bound for mixed floor-and-ceiling divide-and-conquer
    recurrences `T(n) ≤ a₁ * T(n / b) + a₂ * T((n + b - 1) / b) + f(n)` without assuming
    monotonicity of `T`.
- **Layer 2 (The Three Master Theorem Regimes)**:
  - **Case 1 (Leaf-dominated, `(b : ℝ) ^ d < a`)**: `master_case1_le`, `master_case1_isBigO`,
    `master_case1_isTheta`, `master_div_ceil_case1_le`, `master_div_ceil_case1_isBigO`.
  - **Case 2 (Balanced, `d = Real.logb b a`)**: `master_case2_natLog_le`, `master_case2_le`,
    `master_case2_isBigO`, `master_case2_isTheta`, `master_div_ceil_case2_le`,
    `master_div_ceil_case2_isBigO`.
  - **Case 3 (Root-dominated, regularity `a * f(n / b) ≤ c * f(n)` or polynomial `a < b ^ d`)**:
    `master_case3_reg_le`, `master_case3_reg_isBigO`, `master_case3_reg_isTheta`,
    `master_case3_poly_le`, `master_case3_poly_isBigO`, `master_case3_poly_isTheta`,
    `master_div_ceil_case3_poly_le`, `master_div_ceil_case3_poly_isBigO`.
- **Layer 3 (Concrete `ℕ` & `TimeM` Paradigm Specializations)**:
  - Ready-to-use `ℕ` bounds and `=O[atTop]` corollaries for binary search, geometric halving,
    merge-sort / balanced binary splitting, Karatsuba, and Strassen recurrences, as well as direct
    `TimeM` subproblem-list combinators.

## References

* [Cormen, Leiserson, Rivest, and Stein, *Introduction to Algorithms*][cormen2022]
-/

@[expose] public section

open Filter Asymptotics

namespace Cslib.Algorithms.Lean

/-! ## Layer 1: Discrete Recursion-Tree Expansion -/

/-- Exact discrete recursion-tree expansion at input `n` for branching factor `a`, division base
`b`, leaf bound `B`, and combine cost `f`:
`a ^ Nat.log b n * B + ∑ i ∈ Finset.range (Nat.log b n), a ^ i * f (n / b ^ i)`. -/
noncomputable def masterExpansion (a : ℝ) (b : ℕ) (B : ℝ) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  a ^ Nat.log b n * B + ∑ i ∈ Finset.range (Nat.log b n), a ^ i * f (n / b ^ i)

/-- Below the base threshold `b`, `masterExpansion` evaluates to the leaf constant `B`. -/
@[simp]
theorem masterExpansion_of_lt (a : ℝ) {b : ℕ} (B : ℝ) (f : ℕ → ℝ) {n : ℕ} (hn : n < b) :
    masterExpansion a b B f n = B := by
  simp [masterExpansion, Nat.log_of_lt hn]

/-- Above `b` (for `1 < b`), `masterExpansion` satisfies the exact floor-division recurrence
`E(n) = a * E(n / b) + f(n)`. -/
theorem masterExpansion_of_le (a : ℝ) {b : ℕ} (hb : 1 < b) (B : ℝ) (f : ℕ → ℝ) {n : ℕ}
    (hn : b ≤ n) :
    masterExpansion a b B f n = a * masterExpansion a b B f (n / b) + f n := by
  unfold masterExpansion
  rw [Nat.log_of_one_lt_of_le hb hn, Finset.sum_range_succ', pow_zero, Nat.pow_zero, Nat.div_one,
    one_mul, pow_succ', mul_add, Finset.mul_sum]
  have hsum : ∑ x ∈ Finset.range (Nat.log b (n / b)), a ^ (x + 1) * f (n / b ^ (x + 1)) =
      ∑ x ∈ Finset.range (Nat.log b (n / b)), a * (a ^ x * f (n / b / b ^ x)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pow_succ', Nat.pow_succ', ← Nat.div_div_eq_div_mul, mul_assoc]
  rw [hsum]
  ring

/-- On exact powers `b ^ (k + 1)`, `masterExpansion` unfolds one recursion level. -/
theorem masterExpansion_pow_succ (a : ℝ) {b : ℕ} (hb : 1 < b) (B : ℝ) (f : ℕ → ℝ) (k : ℕ) :
    masterExpansion a b B f (b ^ (k + 1)) =
      a * masterExpansion a b B f (b ^ k) + f (b ^ (k + 1)) := by
  have hb_le : b ≤ b ^ (k + 1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega) (Nat.succ_pos k)
  have hdiv : b ^ (k + 1) / b = b ^ k := by
    rw [Nat.pow_succ, Nat.mul_div_cancel _ (by omega)]
  rw [masterExpansion_of_le a hb B f hb_le, hdiv]

/-- When `1 ≤ a`, `0 ≤ B`, `f` is monotone, and `0 ≤ f m` for `b ≤ m`, `masterExpansion a b B f`
is monotone on all of `ℕ`. -/
theorem masterExpansion_mono {a : ℝ} {b : ℕ} {B : ℝ} {f : ℕ → ℝ} (ha : 1 ≤ a) (hb : 1 < b)
    (hB : 0 ≤ B) (hf_mono : Monotone f) (hf_nonneg : ∀ m, b ≤ m → 0 ≤ f m) :
    Monotone (masterExpansion a b B f) := by
  intro m n hmn
  induction n using Nat.strong_induction_on generalizing m with
  | ind n ih =>
    rcases lt_or_ge n b with hnb | hbn
    · rw [masterExpansion_of_lt a B f (hmn.trans_lt hnb), masterExpansion_of_lt a B f hnb]
    · have hdiv_lt : n / b < n := Nat.div_lt_self (by omega) hb
      rw [masterExpansion_of_le a hb B f hbn]
      rcases lt_or_ge m b with hmb | hbm
      · rw [masterExpansion_of_lt a B f hmb]
        have h0 : B ≤ masterExpansion a b B f (n / b) := by
          simpa only [masterExpansion_of_lt a B f (by omega : 0 < b)] using
            ih (n / b) hdiv_lt (Nat.zero_le _)
        have hfn : 0 ≤ f n := hf_nonneg n hbn
        nlinarith
      · rw [masterExpansion_of_le a hb B f hbm]
        have hsub : masterExpansion a b B f (m / b) ≤ masterExpansion a b B f (n / b) :=
          ih (n / b) hdiv_lt (Nat.div_le_div_right hmn)
        have hfm : f m ≤ f n := hf_mono hmn
        nlinarith

/-- Nonnegativity of `masterExpansion` when `0 ≤ a`, `0 ≤ B`, and `0 ≤ f m` for `b ≤ m`. -/
theorem masterExpansion_nonneg {a : ℝ} {b : ℕ} {B : ℝ} {f : ℕ → ℝ} (ha : 0 ≤ a) (hb : 1 < b)
    (hB : 0 ≤ B) (hf_nonneg : ∀ m, b ≤ m → 0 ≤ f m) (n : ℕ) :
    0 ≤ masterExpansion a b B f n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases lt_or_ge n b with hnb | hbn
    · rw [masterExpansion_of_lt a B f hnb]
      exact hB
    · rw [masterExpansion_of_le a hb B f hbn]
      have hsub : 0 ≤ masterExpansion a b B f (n / b) :=
        ih (n / b) (Nat.div_lt_self (by omega) hb)
      have hfn : 0 ≤ f n := hf_nonneg n hbn
      nlinarith

/-- **Exact Upper Expansion (All `n : ℕ`)**: Any function `T : ℕ → ℝ` satisfying `T m ≤ B` for
`m < b` and `T n ≤ a * T (n / b) + f n` for `b ≤ n` (with `0 ≤ a` and `1 < b`) is bounded above
by `masterExpansion a b B f n` for every `n : ℕ`. -/
theorem rec_le_masterExpansion {T f : ℕ → ℝ} {a : ℝ} {b : ℕ} {B : ℝ} (ha : 0 ≤ a) (hb : 1 < b)
    (hBase : ∀ m < b, T m ≤ B) (hStep : ∀ n, b ≤ n → T n ≤ a * T (n / b) + f n) (n : ℕ) :
    T n ≤ masterExpansion a b B f n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases lt_or_ge n b with hnb | hbn
    · rw [masterExpansion_of_lt a B f hnb]
      exact hBase n hnb
    · rw [masterExpansion_of_le a hb B f hbn]
      have hsub := ih (n / b) (Nat.div_lt_self (by omega) hb)
      have hst := hStep n hbn
      nlinarith

/-- **Exact Upper Expansion (`1 ≤ n`)**: Starting from `1 ≤ n`, repeated division by `b` never
visits `0`, so the base-case bound `T m ≤ B` is only needed for `1 ≤ m < b`. -/
theorem rec_le_masterExpansion_of_pos {T f : ℕ → ℝ} {a : ℝ} {b : ℕ} {B : ℝ} (ha : 0 ≤ a)
    (hb : 1 < b) (hBase : ∀ m, 1 ≤ m → m < b → T m ≤ B)
    (hStep : ∀ n, b ≤ n → T n ≤ a * T (n / b) + f n) {n : ℕ} (hn : 1 ≤ n) :
    T n ≤ masterExpansion a b B f n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases lt_or_ge n b with hnb | hbn
    · rw [masterExpansion_of_lt a B f hnb]
      exact hBase n hn hnb
    · rw [masterExpansion_of_le a hb B f hbn]
      have hdiv_pos : 1 ≤ n / b := Nat.div_pos hbn (by omega)
      have hsub := ih (n / b) (Nat.div_lt_self (by omega) hb) hdiv_pos
      have hst := hStep n hbn
      nlinarith

/-- **Exact Lower Expansion (`1 ≤ n`)**: Dual lower bound when `B ≤ T m` for `1 ≤ m < b` and
`a * T (n / b) + f n ≤ T n` for `b ≤ n`. -/
theorem masterExpansion_le_rec {T f : ℕ → ℝ} {a : ℝ} {b : ℕ} {B : ℝ} (ha : 0 ≤ a) (hb : 1 < b)
    (hBase : ∀ m, 1 ≤ m → m < b → B ≤ T m)
    (hStep : ∀ n, b ≤ n → a * T (n / b) + f n ≤ T n) {n : ℕ} (hn : 1 ≤ n) :
    masterExpansion a b B f n ≤ T n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases lt_or_ge n b with hnb | hbn
    · rw [masterExpansion_of_lt a B f hnb]
      exact hBase n hn hnb
    · rw [masterExpansion_of_le a hb B f hbn]
      have hdiv_pos : 1 ≤ n / b := Nat.div_pos hbn (by omega)
      have hsub := ih (n / b) (Nat.div_lt_self (by omega) hb) hdiv_pos
      have hst := hStep n hbn
      nlinarith

/-- **Mixed Floor-and-Ceiling Expansion**: If `T : ℕ → ℝ` satisfies
`T n ≤ a₁ * T (n / b) + a₂ * T ((n + b - 1) / b) + f n` for all `2 ≤ n` with `T 0 ≤ B` and
`T 1 ≤ B`, then `T n ≤ masterExpansion (a₁ + a₂) b B f (b ^ Nat.clog b n)` for all `n : ℕ`,
without requiring `T` to be monotone. -/
theorem rec_div_ceil_le_masterExpansion {T f : ℕ → ℝ} {a₁ a₂ : ℝ} {b : ℕ} {B : ℝ}
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (ha : 1 ≤ a₁ + a₂) (hb : 1 < b) (hB : 0 ≤ B)
    (hf_mono : Monotone f) (hf_nonneg : ∀ m, b ≤ m → 0 ≤ f m)
    (hBase0 : T 0 ≤ B) (hBase1 : T 1 ≤ B)
    (hStep : ∀ n, 2 ≤ n → T n ≤ a₁ * T (n / b) + a₂ * T ((n + b - 1) / b) + f n) (n : ℕ) :
    T n ≤ masterExpansion (a₁ + a₂) b B f (b ^ Nat.clog b n) := by
  have hmono := masterExpansion_mono ha hb hB hf_mono hf_nonneg
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases n with _ | _ | m
    · simpa [masterExpansion_of_lt _ B f hb] using hBase0
    · simpa [masterExpansion_of_lt _ B f hb] using hBase1
    · set N := m + 2
      have hN : 2 ≤ N := by omega
      have hlt_floor : N / b < N := Nat.div_lt_self (by omega) hb
      have hlt_ceil : (N + b - 1) / b < N := Nat.add_pred_div_lt hb hN
      set k := Nat.clog b ((N + b - 1) / b)
      have hclog_eq : Nat.clog b N = k + 1 := Nat.clog_of_two_le hb hN
      have hclog_floor : Nat.clog b (N / b) ≤ k :=
        Nat.clog_mono_right b (Nat.div_le_div_right (by omega))
      have ih_floor : T (N / b) ≤ masterExpansion (a₁ + a₂) b B f (b ^ k) :=
        (ih (N / b) hlt_floor).trans (hmono (Nat.pow_le_pow_right (by omega) hclog_floor))
      have ih_ceil : T ((N + b - 1) / b) ≤ masterExpansion (a₁ + a₂) b B f (b ^ k) :=
        ih ((N + b - 1) / b) hlt_ceil
      have hf_le : f N ≤ f (b ^ (k + 1)) := by
        apply hf_mono
        rw [← hclog_eq]
        exact Nat.le_pow_clog hb N
      rw [hclog_eq, masterExpansion_pow_succ (a₁ + a₂) hb B f k]
      have hst := hStep N hN
      nlinarith

/-! ## Helper Bridge Lemmas (`Nat.log`, `Nat.clog`, `Real.rpow`, `Real.logb`) -/

private theorem le_div_pow_of_lt_log {b n i : ℕ} (hb : 1 < b) (hi : i < Nat.log b n) :
    b ≤ n / b ^ i := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp only [Nat.log_zero_right] at hi
    omega
  have hpow : b ^ (i + 1) ≤ n := (Nat.le_log_iff_pow_le hb hn0).mp (Nat.succ_le_of_lt hi)
  rw [Nat.pow_succ'] at hpow
  exact (Nat.le_div_iff_mul_le (Nat.pow_pos (by omega))).mpr hpow

/-- Change-of-base identity `a ^ k = ((b : ℝ) ^ k) ^ Real.logb b a` for `0 < a` and `1 < b`. -/
theorem pow_eq_pow_rpow_logb {a : ℝ} {b : ℕ} (ha : 0 < a) (hb : 1 < b) (k : ℕ) :
    a ^ k = ((b : ℝ) ^ k) ^ Real.logb b a := by
  have hb1 : (1 : ℝ) < b := Nat.one_lt_cast.mpr hb
  have hb0 : (0 : ℝ) < b := zero_lt_one.trans hb1
  calc
    a ^ k = ((b : ℝ) ^ Real.logb b a) ^ k := by rw [Real.rpow_logb hb0 hb1.ne' ha]
    _ = ((b : ℝ) ^ Real.logb b a) ^ (k : ℝ) := (Real.rpow_natCast _ k).symm
    _ = (b : ℝ) ^ (Real.logb b a * k) := (Real.rpow_mul hb0.le _ _).symm
    _ = (b : ℝ) ^ ((k : ℝ) * Real.logb b a) := by rw [mul_comm]
    _ = ((b : ℝ) ^ (k : ℝ)) ^ Real.logb b a := Real.rpow_mul hb0.le _ _
    _ = ((b : ℝ) ^ k) ^ Real.logb b a := by rw [Real.rpow_natCast]

/-- Leaf-count upper bound: `a ^ Nat.log b n ≤ (n : ℝ) ^ Real.logb b a` for `1 ≤ a`, `1 < b`,
and `1 ≤ n`. -/
theorem pow_natLog_le_rpow_logb {a : ℝ} {b n : ℕ} (ha : 1 ≤ a) (hb : 1 < b) (hn : 1 ≤ n) :
    a ^ Nat.log b n ≤ (n : ℝ) ^ Real.logb b a := by
  have hb1 : (1 : ℝ) < b := Nat.one_lt_cast.mpr hb
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  rw [pow_eq_pow_rpow_logb ha0 hb]
  have hpow : (b : ℝ) ^ Nat.log b n ≤ (n : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self b (by omega : n ≠ 0)
  exact Real.rpow_le_rpow (by positivity) hpow (Real.logb_nonneg hb1 ha)

/-- Leaf-count lower bound: `(n : ℝ) ^ Real.logb b a / a ≤ a ^ Nat.log b n` for `1 ≤ a`, `1 < b`,
and `1 ≤ n`. -/
theorem rpow_logb_div_le_pow_natLog {a : ℝ} {b n : ℕ} (ha : 1 ≤ a) (hb : 1 < b) (hn : 1 ≤ n) :
    (n : ℝ) ^ Real.logb b a / a ≤ a ^ Nat.log b n := by
  have hb1 : (1 : ℝ) < b := Nat.one_lt_cast.mpr hb
  have hb0 : (0 : ℝ) < b := zero_lt_one.trans hb1
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hlt : (n : ℝ) ≤ (b : ℝ) ^ Nat.log b n * (b : ℝ) := by
    have hnat : n ≤ b ^ Nat.log b n * b := by
      rw [← Nat.pow_succ]
      exact (Nat.lt_pow_succ_log_self hb n).le
    exact_mod_cast hnat
  have hdiv : (n : ℝ) / b ≤ (b : ℝ) ^ Nat.log b n := (div_le_iff₀ hb0).mpr hlt
  calc
    (n : ℝ) ^ Real.logb b a / a
      = (n : ℝ) ^ Real.logb b a / (b : ℝ) ^ Real.logb b a := by
          rw [Real.rpow_logb hb0 hb1.ne' ha0]
    _ = ((n : ℝ) / b) ^ Real.logb b a := (Real.div_rpow (Nat.cast_nonneg n) hb0.le _).symm
    _ ≤ ((b : ℝ) ^ Nat.log b n) ^ Real.logb b a :=
          Real.rpow_le_rpow (by positivity) hdiv (Real.logb_nonneg hb1 ha)
    _ = a ^ Nat.log b n := (pow_eq_pow_rpow_logb ha0 hb _).symm

private theorem natCast_div_pow_rpow_le {b n : ℕ} (hb : 1 < b) {d : ℝ} (hd : 0 ≤ d) (i : ℕ) :
    ((n / b ^ i : ℕ) : ℝ) ^ d ≤ (n : ℝ) ^ d / ((b : ℝ) ^ d) ^ i := by
  have hb0 : (0 : ℝ) < b := by positivity
  have hbi0 : (0 : ℝ) < (b : ℝ) ^ i := pow_pos hb0 i
  have hdiv_le : ((n / b ^ i : ℕ) : ℝ) ≤ (n : ℝ) / (b : ℝ) ^ i := by
    rw [le_div_iff₀ hbi0]
    exact_mod_cast Nat.div_mul_le_self n (b ^ i)
  have hpow_comm : ((b : ℝ) ^ i) ^ d = ((b : ℝ) ^ d) ^ i := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb0.le, mul_comm,
      Real.rpow_mul hb0.le, Real.rpow_natCast]
  calc
    ((n / b ^ i : ℕ) : ℝ) ^ d ≤ ((n : ℝ) / (b : ℝ) ^ i) ^ d :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hdiv_le hd
    _ = (n : ℝ) ^ d / ((b : ℝ) ^ i) ^ d := Real.div_rpow (Nat.cast_nonneg n) hbi0.le d
    _ = (n : ℝ) ^ d / ((b : ℝ) ^ d) ^ i := by rw [hpow_comm]

private theorem pow_clog_le_mul {b n : ℕ} (hb : 1 < b) (hn : 1 ≤ n) :
    b ^ Nat.clog b n ≤ b * n := by
  rcases eq_or_lt_of_le hn with rfl | hn1
  · simp only [Nat.clog_one_right, pow_zero, mul_one]
    omega
  · have hpos : 0 < Nat.clog b n := Nat.clog_pos hb hn1
    have hpred : b ^ (Nat.clog b n - 1) < n := by
      simpa only [Nat.pred_eq_sub_one] using Nat.pow_pred_clog_lt_self b hn1
    have hstep : Nat.clog b n = (Nat.clog b n - 1) + 1 := by omega
    rw [hstep, Nat.pow_succ']
    exact Nat.mul_le_mul_left b hpred.le

private theorem geom_sum_le_one_div_sub {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (k : ℕ) :
    ∑ i ∈ Finset.range k, r ^ i ≤ 1 / (1 - r) := by
  have h1r : 0 < 1 - r := sub_pos.mpr hr1
  have hr_sub : r - 1 ≠ 0 := sub_ne_zero.mpr hr1.ne
  have hrk : 0 ≤ r ^ k := pow_nonneg hr0 k
  rw [geom_sum_eq hr1.ne k]
  have heq : (r ^ k - 1) / (r - 1) = (1 - r ^ k) / (1 - r) := by
    field_simp [h1r.ne', hr_sub]
    ring
  rw [heq]
  exact div_le_div_of_nonneg_right (by linarith) h1r.le

/-! ## Layer 2, Case 1: Sub-Critical / Leaf-Dominated Regime (`(b : ℝ) ^ d < a`) -/

/-- Explicit upper bound on `masterExpansion` in Case 1 (`0 ≤ d` and `(b : ℝ) ^ d < a`). -/
theorem masterExpansion_le_case1 {a : ℝ} {b : ℕ} {B C d : ℝ} {f : ℕ → ℝ} (hb : 1 < b)
    (hd : 0 ≤ d) (hba : (b : ℝ) ^ d < a) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hf : ∀ m, b ≤ m → f m ≤ C * (m : ℝ) ^ d) {n : ℕ} (hn : 1 ≤ n) :
    masterExpansion a b B f n ≤
      (B + C / (a / (b : ℝ) ^ d - 1)) * (n : ℝ) ^ Real.logb b a := by
  have hb1 : (1 : ℝ) < b := Nat.one_lt_cast.mpr hb
  have hb0 : (0 : ℝ) < b := zero_lt_one.trans hb1
  have hbd_ge1 : (1 : ℝ) ≤ (b : ℝ) ^ d := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hb1.le hd
  have ha1 : 1 ≤ a := hbd_ge1.trans hba.le
  have ha0 : 0 < a := zero_lt_one.trans_le ha1
  have hbd_pos : 0 < (b : ℝ) ^ d := zero_lt_one.trans_le hbd_ge1
  set p := Real.logb b a
  set r := a / (b : ℝ) ^ d
  set k := Nat.log b n
  have hr1 : 1 < r := (one_lt_div hbd_pos).mpr hba
  have hr_sub_pos : 0 < r - 1 := sub_pos.mpr hr1
  have hleaf : a ^ k * B ≤ B * (n : ℝ) ^ p := by
    have h := pow_natLog_le_rpow_logb ha1 hb hn
    nlinarith
  have hterm : ∀ i ∈ Finset.range k, a ^ i * f (n / b ^ i) ≤ C * (n : ℝ) ^ d * r ^ i := by
    intro i hi
    have hbm : b ≤ n / b ^ i := le_div_pow_of_lt_log hb (Finset.mem_range.mp hi)
    have hai : 0 ≤ a ^ i := pow_nonneg ha0.le i
    calc
      a ^ i * f (n / b ^ i) ≤ a ^ i * (C * ((n / b ^ i : ℕ) : ℝ) ^ d) :=
        mul_le_mul_of_nonneg_left (hf _ hbm) hai
      _ ≤ a ^ i * (C * ((n : ℝ) ^ d / ((b : ℝ) ^ d) ^ i)) := by
        gcongr
        exact natCast_div_pow_rpow_le hb hd i
      _ = C * (n : ℝ) ^ d * r ^ i := by
        rw [div_pow]
        ring
  have hsum_geom : ∑ i ∈ Finset.range k, a ^ i * f (n / b ^ i) ≤
      C / (r - 1) * ((n : ℝ) ^ d * r ^ k) := by
    have hnd_nonneg : 0 ≤ (n : ℝ) ^ d := Real.rpow_nonneg (Nat.cast_nonneg n) d
    calc
      ∑ i ∈ Finset.range k, a ^ i * f (n / b ^ i)
        ≤ ∑ i ∈ Finset.range k, C * (n : ℝ) ^ d * r ^ i := Finset.sum_le_sum hterm
      _ = C * (n : ℝ) ^ d * ∑ i ∈ Finset.range k, r ^ i := (Finset.mul_sum _ _ _).symm
      _ = C * (n : ℝ) ^ d * ((r ^ k - 1) / (r - 1)) := by rw [geom_sum_eq hr1.ne' k]
      _ ≤ C * (n : ℝ) ^ d * (r ^ k / (r - 1)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (by linarith) hr_sub_pos.le)
          (mul_nonneg hC hnd_nonneg)
      _ = C / (r - 1) * ((n : ℝ) ^ d * r ^ k) := by ring
  have hrk_le : (n : ℝ) ^ d * r ^ k ≤ (n : ℝ) ^ p := by
    have hdp : d < p := (Real.lt_logb_iff_rpow_lt hb1 ha0).mpr hba
    have hr_eq : r = (b : ℝ) ^ (p - d) := by
      unfold r
      rw [← Real.rpow_logb hb0 hb1.ne' ha0, ← Real.rpow_sub hb0 p d]
    have hrk_eq : r ^ k = ((b : ℝ) ^ k) ^ (p - d) := by
      rw [hr_eq, ← Real.rpow_natCast, ← Real.rpow_mul hb0.le, mul_comm,
        Real.rpow_mul hb0.le, Real.rpow_natCast]
    have hbk_le : (b : ℝ) ^ k ≤ (n : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self b (by omega : n ≠ 0)
    have hn_pos : (0 : ℝ) < n := by positivity
    calc
      (n : ℝ) ^ d * r ^ k = (n : ℝ) ^ d * ((b : ℝ) ^ k) ^ (p - d) := by rw [hrk_eq]
      _ ≤ (n : ℝ) ^ d * (n : ℝ) ^ (p - d) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by positivity) hbk_le (sub_nonneg.mpr hdp.le))
          (Real.rpow_nonneg hn_pos.le d)
      _ = (n : ℝ) ^ (d + (p - d)) := (Real.rpow_add hn_pos d (p - d)).symm
      _ = (n : ℝ) ^ p := by rw [add_sub_cancel]
  unfold masterExpansion
  have hCdiv : 0 ≤ C / (r - 1) := div_nonneg hC hr_sub_pos.le
  have hsum_final : ∑ i ∈ Finset.range k, a ^ i * f (n / b ^ i) ≤ C / (r - 1) * (n : ℝ) ^ p :=
    hsum_geom.trans (mul_le_mul_of_nonneg_left hrk_le hCdiv)
  linarith

/-- **Master Theorem — Case 1 (Explicit Bound)**: If `T n ≤ a * T (n / b) + f n` for `b ≤ n`,
`T m ≤ B` for `1 ≤ m < b`, and `f m ≤ C * (m : ℝ) ^ d` for `b ≤ m` with `0 ≤ d` and
`(b : ℝ) ^ d < a`, then `T n ≤ (B + C / (a / (b : ℝ) ^ d - 1)) * (n : ℝ) ^ Real.logb b a` for all
`1 ≤ n`. -/
theorem master_case1_le {T f : ℕ → ℝ} {a : ℝ} {b : ℕ} {B C d : ℝ} (hb : 1 < b) (hd : 0 ≤ d)
    (hba : (b : ℝ) ^ d < a) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hBase : ∀ m, 1 ≤ m → m < b → T m ≤ B)
    (hStep : ∀ n, b ≤ n → T n ≤ a * T (n / b) + f n)
    (hf : ∀ m, b ≤ m → f m ≤ C * (m : ℝ) ^ d) {n : ℕ} (hn : 1 ≤ n) :
    T n ≤ (B + C / (a / (b : ℝ) ^ d - 1)) * (n : ℝ) ^ Real.logb b a := by
  have ha0 : 0 ≤ a := (Real.rpow_nonneg (Nat.cast_nonneg b) d).trans hba.le
  exact (rec_le_masterExpansion_of_pos ha0 hb hBase hStep hn).trans
    (masterExpansion_le_case1 hb hd hba hB hC hf hn)

/-- **Master Theorem — Case 1 (`=O[atTop]`)**: Under the Case 1 hypotheses (and eventual
nonnegativity of `T`), `T =O[atTop] fun n : ℕ => (n : ℝ) ^ Real.logb b a`. -/
theorem master_case1_isBigO {T f : ℕ → ℝ} {a : ℝ} {b : ℕ} {B C d : ℝ} (hb : 1 < b) (hd : 0 ≤ d)
    (hba : (b : ℝ) ^ d < a) (hB : 0 ≤ B) (hC : 0 ≤ C) (hT_nonneg : ∀ᶠ n in atTop, 0 ≤ T n)
    (hBase : ∀ m, 1 ≤ m → m < b → T m ≤ B)
    (hStep : ∀ n, b ≤ n → T n ≤ a * T (n / b) + f n)
    (hf : ∀ m, b ≤ m → f m ≤ C * (m : ℝ) ^ d) :
    T =O[atTop] fun n : ℕ => (n : ℝ) ^ Real.logb b a := by
  refine IsBigO.of_bound (B + C / (a / (b : ℝ) ^ d - 1)) ?_
  filter_upwards [hT_nonneg, eventually_ge_atTop 1] with n hTn hn
  have hle := master_case1_le hb hd hba hB hC hBase hStep hf hn
  have hrpow_nonneg : 0 ≤ (n : ℝ) ^ Real.logb b a := Real.rpow_nonneg (Nat.cast_nonneg n) _
  rw [Real.norm_of_nonneg hTn, Real.norm_of_nonneg hrpow_nonneg]
  exact hle

/-- **Master Theorem — Case 1 (`=Θ[atTop]`)**: Two-sided leaf-dominated recurrence with positive
leaf lower bound `0 < B₀ ≤ T m ≤ B` (`1 ≤ m < b`) and `0 ≤ f m ≤ C * (m : ℝ) ^ d` (`b ≤ m`) yields
`T =Θ[atTop] fun n : ℕ => (n : ℝ) ^ Real.logb b a`. -/
theorem master_case1_isTheta {T f : ℕ → ℝ} {a : ℝ} {b : ℕ} {B₀ B C d : ℝ} (hb : 1 < b)
    (hd : 0 ≤ d) (hba : (b : ℝ) ^ d < a) (hB₀ : 0 < B₀) (hC : 0 ≤ C)
    (hBase_lo : ∀ m, 1 ≤ m → m < b → B₀ ≤ T m)
    (hBase_hi : ∀ m, 1 ≤ m → m < b → T m ≤ B)
    (hStep_lo : ∀ n, b ≤ n → a * T (n / b) + f n ≤ T n)
    (hStep_hi : ∀ n, b ≤ n → T n ≤ a * T (n / b) + f n)
    (hf_lo : ∀ m, b ≤ m → 0 ≤ f m)
    (hf_hi : ∀ m, b ≤ m → f m ≤ C * (m : ℝ) ^ d) :
    T =Θ[atTop] fun n : ℕ => (n : ℝ) ^ Real.logb b a := by
  have hb1 : (1 : ℝ) < b := Nat.one_lt_cast.mpr hb
  have hbd_ge1 : (1 : ℝ) ≤ (b : ℝ) ^ d := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hb1.le hd
  have ha1 : 1 ≤ a := hbd_ge1.trans hba.le
  have ha0 : 0 < a := zero_lt_one.trans_le ha1
  have hB : 0 ≤ B := hB₀.le.trans ((hBase_lo 1 le_rfl hb).trans (hBase_hi 1 le_rfl hb))
  have hlower : ∀ n : ℕ, 1 ≤ n → B₀ / a * (n : ℝ) ^ Real.logb b a ≤ T n := by
    intro n hn
    have hexp_le := masterExpansion_le_rec ha0.le hb hBase_lo hStep_lo hn
    have hsum_nonneg : 0 ≤ ∑ i ∈ Finset.range (Nat.log b n), a ^ i * f (n / b ^ i) := by
      refine Finset.sum_nonneg fun i hi => mul_nonneg (pow_nonneg ha0.le i) ?_
      exact hf_lo _ (le_div_pow_of_lt_log hb (Finset.mem_range.mp hi))
    have hleaf_lo := rpow_logb_div_le_pow_natLog ha1 hb hn
    have hmul : B₀ / a * (n : ℝ) ^ Real.logb b a ≤ a ^ Nat.log b n * B₀ := by
      calc
        B₀ / a * (n : ℝ) ^ Real.logb b a = B₀ * ((n : ℝ) ^ Real.logb b a / a) := by ring
        _ ≤ a ^ Nat.log b n * B₀ := by nlinarith
    unfold masterExpansion at hexp_le
    linarith
  have hT_nonneg : ∀ᶠ n in atTop, 0 ≤ T n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (mul_nonneg (div_nonneg hB₀.le ha0.le)
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)).trans (hlower n hn)
  refine ⟨master_case1_isBigO hb hd hba hB hC hT_nonneg hBase_hi hStep_hi hf_hi, ?_⟩
  refine IsBigO.of_bound (a / B₀) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hlo := hlower n hn
  have hrpow_nonneg : 0 ≤ (n : ℝ) ^ Real.logb b a := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hTn : 0 ≤ T n := (mul_nonneg (div_nonneg hB₀.le ha0.le) hrpow_nonneg).trans hlo
  rw [Real.norm_of_nonneg hrpow_nonneg, Real.norm_of_nonneg hTn]
  calc
    (n : ℝ) ^ Real.logb b a = a / B₀ * (B₀ / a * (n : ℝ) ^ Real.logb b a) := by
      field_simp [hB₀.ne', ha0.ne']
    _ ≤ a / B₀ * T n := mul_le_mul_of_nonneg_left hlo (div_nonneg ha0.le hB₀.le)

/-- **Master Theorem — Case 1 for Mixed Floor-and-Ceiling Splits (Explicit Bound)**:
For `T n ≤ a₁ * T (n / b) + a₂ * T ((n + b - 1) / b) + f n` (`2 ≤ n`), `(b : ℝ) ^ d < a₁ + a₂`,
no monotonicity of `T` or `f` is needed. -/
theorem master_div_ceil_case1_le {T f : ℕ → ℝ} {a₁ a₂ : ℝ} {b : ℕ} {B C d : ℝ}
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hb : 1 < b) (hd : 0 ≤ d) (hba : (b : ℝ) ^ d < a₁ + a₂)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hBase0 : T 0 ≤ B) (hBase1 : T 1 ≤ B)
    (hStep : ∀ n, 2 ≤ n → T n ≤ a₁ * T (n / b) + a₂ * T ((n + b - 1) / b) + f n)
    (hf : ∀ m, 2 ≤ m → f m ≤ C * (m : ℝ) ^ d) {n : ℕ} (hn : 1 ≤ n) :
    T n ≤ (a₁ + a₂) * (B + C / ((a₁ + a₂) / (b : ℝ) ^ d - 1)) *
      (n : ℝ) ^ Real.logb b (a₁ + a₂) := by
  have hb1 : (1 : ℝ) < b := Nat.one_lt_cast.mpr hb
  have hb0 : (0 : ℝ) < b := zero_lt_one.trans hb1
  have hbd_ge1 : (1 : ℝ) ≤ (b : ℝ) ^ d := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hb1.le hd
  have ha : 1 ≤ a₁ + a₂ := hbd_ge1.trans hba.le
  have ha0 : 0 < a₁ + a₂ := zero_lt_one.trans_le ha
  let g : ℕ → ℝ := fun m => C * (m : ℝ) ^ d
  have hg_mono : Monotone g := fun x y hxy =>
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg x) (Nat.cast_le.mpr hxy) hd) hC
  have hg_nonneg : ∀ m, b ≤ m → 0 ≤ g m := fun m _ =>
    mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg m) d)
  have hStep_g : ∀ m, 2 ≤ m → T m ≤ a₁ * T (m / b) + a₂ * T ((m + b - 1) / b) + g m :=
    fun m hm => (hStep m hm).trans (add_le_add_right (hf m hm) _)
  have hexp := rec_div_ceil_le_masterExpansion ha₁ ha₂ ha hb hB hg_mono hg_nonneg hBase0 hBase1
    hStep_g n
  set N := b ^ Nat.clog b n
  have hN1 : 1 ≤ N := Nat.one_le_pow _ _ (by omega)
  have hN_bound := masterExpansion_le_case1 hb hd hba hB hC (fun _ _ => le_rfl) hN1
  have hN_le : (N : ℝ) ≤ (b : ℝ) * (n : ℝ) := by exact_mod_cast pow_clog_le_mul hb hn
  have hp_nonneg : 0 ≤ Real.logb b (a₁ + a₂) := Real.logb_nonneg hb1 ha
  have hrpow_le : (N : ℝ) ^ Real.logb b (a₁ + a₂) ≤
      (a₁ + a₂) * (n : ℝ) ^ Real.logb b (a₁ + a₂) := by
    calc
      (N : ℝ) ^ Real.logb b (a₁ + a₂) ≤ ((b : ℝ) * (n : ℝ)) ^ Real.logb b (a₁ + a₂) :=
        Real.rpow_le_rpow (Nat.cast_nonneg N) hN_le hp_nonneg
      _ = (b : ℝ) ^ Real.logb b (a₁ + a₂) * (n : ℝ) ^ Real.logb b (a₁ + a₂) :=
        Real.mul_rpow hb0.le (Nat.cast_nonneg n)
      _ = (a₁ + a₂) * (n : ℝ) ^ Real.logb b (a₁ + a₂) := by
        rw [Real.rpow_logb hb0 hb1.ne' ha0]
  have hconst_nonneg : 0 ≤ B + C / ((a₁ + a₂) / (b : ℝ) ^ d - 1) :=
    add_nonneg hB (div_nonneg hC (sub_nonneg.mpr ((one_lt_div (by positivity)).mpr hba).le))
  calc
    T n ≤ (B + C / ((a₁ + a₂) / (b : ℝ) ^ d - 1)) * (N : ℝ) ^ Real.logb b (a₁ + a₂) :=
      hexp.trans hN_bound
    _ ≤ (B + C / ((a₁ + a₂) / (b : ℝ) ^ d - 1)) *
          ((a₁ + a₂) * (n : ℝ) ^ Real.logb b (a₁ + a₂)) :=
      mul_le_mul_of_nonneg_left hrpow_le hconst_nonneg
    _ = (a₁ + a₂) * (B + C / ((a₁ + a₂) / (b : ℝ) ^ d - 1)) *
          (n : ℝ) ^ Real.logb b (a₁ + a₂) := by ring

/-- **Master Theorem — Case 1 for Mixed Floor-and-Ceiling Splits (`=O[atTop]`)**. -/
theorem master_div_ceil_case1_isBigO {T f : ℕ → ℝ} {a₁ a₂ : ℝ} {b : ℕ} {B C d : ℝ}
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hb : 1 < b) (hd : 0 ≤ d) (hba : (b : ℝ) ^ d < a₁ + a₂)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hT_nonneg : ∀ᶠ n in atTop, 0 ≤ T n)
    (hBase0 : T 0 ≤ B) (hBase1 : T 1 ≤ B)
    (hStep : ∀ n, 2 ≤ n → T n ≤ a₁ * T (n / b) + a₂ * T ((n + b - 1) / b) + f n)
    (hf : ∀ m, 2 ≤ m → f m ≤ C * (m : ℝ) ^ d) :
    T =O[atTop] fun n : ℕ => (n : ℝ) ^ Real.logb b (a₁ + a₂) := by
  refine IsBigO.of_bound ((a₁ + a₂) * (B + C / ((a₁ + a₂) / (b : ℝ) ^ d - 1))) ?_
  filter_upwards [hT_nonneg, eventually_ge_atTop 1] with n hTn hn
  have hle := master_div_ceil_case1_le ha₁ ha₂ hb hd hba hB hC hBase0 hBase1 hStep hf hn
  have hrpow_nonneg : 0 ≤ (n : ℝ) ^ Real.logb b (a₁ + a₂) :=
    Real.rpow_nonneg (Nat.cast_nonneg n) _
  rw [Real.norm_of_nonneg hTn, Real.norm_of_nonneg hrpow_nonneg]
  exact hle

/-! ## Layer 2, Case 2: Critical / Balanced Regime (`d = Real.logb b a`) -/

/-- Explicit discrete upper bound on `masterExpansion` in Case 2 in terms of `Nat.log b n`. -/
theorem masterExpansion_le_case2_natLog {a : ℝ} {b : ℕ} {B C : ℝ} {f : ℕ → ℝ} (ha : 1 ≤ a)
    (hb : 1 < b) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hf : ∀ m, b ≤ m → f m ≤ C * (m : ℝ) ^ Real.logb b a) {n : ℕ} (hn : 1 ≤ n) :
    masterExpansion a b B f n ≤
      (B + C * (Nat.log b n : ℝ)) * (n : ℝ) ^ Real.logb b a := by
  have hb1 : (1 : ℝ) < b := Nat.one_lt_cast.mpr hb
  have hb0 : (0 : ℝ) < b := zero_lt_one.trans hb1
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  set p := Real.logb b a
  set k := Nat.log b n
  have hp_nonneg : 0 ≤ p := Real.logb_nonneg hb1 ha
  have hbp : (b : ℝ) ^ p = a := Real.rpow_logb hb0 hb1.ne' ha0
  have hleaf : a ^ k * B ≤ B * (n : ℝ) ^ p := by
    have h := pow_natLog_le_rpow_logb ha hb hn
    nlinarith
  have hterm : ∀ i ∈ Finset.range k, a ^ i * f (n / b ^ i) ≤ C * (n : ℝ) ^ p := by
    intro i hi
    have hbm : b ≤ n / b ^ i := le_div_pow_of_lt_log hb (Finset.mem_range.mp hi)
    have hai_pos : 0 < a ^ i := pow_pos ha0 i
    calc
      a ^ i * f (n / b ^ i) ≤ a ^ i * (C * ((n / b ^ i : ℕ) : ℝ) ^ p) :=
        mul_le_mul_of_nonneg_left (hf _ hbm) hai_pos.le
      _ ≤ a ^ i * (C * ((n : ℝ) ^ p / ((b : ℝ) ^ p) ^ i)) := by
        gcongr
        exact natCast_div_pow_rpow_le hb hp_nonneg i
      _ = a ^ i * (C * ((n : ℝ) ^ p / a ^ i)) := by rw [hbp]
      _ = C * (n : ℝ) ^ p := by field_simp [hai_pos.ne']
  have hsum : ∑ i ∈ Finset.range k, a ^ i * f (n / b ^ i) ≤
      C * (k : ℝ) * (n : ℝ) ^ p := by
    calc
      ∑ i ∈ Finset.range k, a ^ i * f (n / b ^ i)
        ≤ ∑ _i ∈ Finset.range k, C * (n : ℝ) ^ p := Finset.sum_le_sum hterm
      _ = (k : ℝ) * (C * (n : ℝ) ^ p) := by simp [Finset.sum_const, nsmul_eq_mul]
      _ = C * (k : ℝ) * (n : ℝ) ^ p := by ring
  unfold masterExpansion
  linarith

/-- Explicit real-logarithm upper bound on `masterExpansion` in Case 2 using `Real.logb b n`. -/
theorem masterExpansion_le_case2 {a : ℝ} {b : ℕ} {B C : ℝ} {f : ℕ → ℝ} (ha : 1 ≤ a)
    (hb : 1 < b) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hf : ∀ m, b ≤ m → f m ≤ C * (m : ℝ) ^ Real.logb b a) {n : ℕ} (hn : 1 ≤ n) :
    masterExpansion a b B f n ≤
      (B + C * Real.logb b n) * (n : ℝ) ^ Real.logb b a := by
  refine (masterExpansion_le_case2_natLog ha hb hB hC hf hn).trans ?_
  have hlog : (Nat.log b n : ℝ) ≤ Real.logb b n := Real.natLog_le_logb n b
  have hrpow : 0 ≤ (n : ℝ) ^ Real.logb b a := Real.rpow_nonneg (Nat.cast_nonneg n) _
  gcongr

/-- **Master Theorem — Case 2 (Discrete `Nat.log` Bound)**: If `T n ≤ a * T (n / b) + f n`
(`b ≤ n`), `T m ≤ B` (`1 ≤ m < b`), and `f m ≤ C * (m : ℝ) ^ Real.logb b a` (`b ≤ m`), then
`T n ≤ (B + C * Nat.log b n) * (n : ℝ) ^ Real.logb b a` for all `1 ≤ n`. -/
theorem master_case2_natLog_le {T f : ℕ → ℝ} {a : ℝ} {b : ℕ} {B C : ℝ} (ha : 1 ≤ a) (hb : 1 < b)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hBase : ∀ m, 1 ≤ m → m < b → T m ≤ B)
    (hStep : ∀ n, b ≤ n → T n ≤ a * T (n / b) + f n)
    (hf : ∀ m, b ≤ m → f m ≤ C * (m : ℝ) ^ Real.logb b a) {n : ℕ} (hn : 1 ≤ n) :
    T n ≤ (B + C * (Nat.log b n : ℝ)) * (n : ℝ) ^ Real.logb b a :=
  (rec_le_masterExpansion_of_pos (zero_le_one.trans ha) hb hBase hStep hn).trans
    (masterExpansion_le_case2_natLog ha hb hB hC hf hn)

/-- **Master Theorem — Case 2 (Explicit `Real.logb` Bound)**: Under Case 2 hypotheses,
`T n ≤ (B + C * Real.logb b n) * (n : ℝ) ^ Real.logb b a` for all `1 ≤ n`. -/
theorem master_case2_le {T f : ℕ → ℝ} {a : ℝ} {b : ℕ} {B C : ℝ} (ha : 1 ≤ a) (hb : 1 < b)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hBase : ∀ m, 1 ≤ m → m < b → T m ≤ B)
    (hStep : ∀ n, b ≤ n → T n ≤ a * T (n / b) + f n)
    (hf : ∀ m, b ≤ m → f m ≤ C * (m : ℝ) ^ Real.logb b a) {n : ℕ} (hn : 1 ≤ n) :
    T n ≤ (B + C * Real.logb b n) * (n : ℝ) ^ Real.logb b a :=
  (rec_le_masterExpansion_of_pos (zero_le_one.trans ha) hb hBase hStep hn).trans
    (masterExpansion_le_case2 ha hb hB hC hf hn)

/-- **Master Theorem — Case 2 (`=O[atTop]`)**: Under the Case 2 hypotheses (and eventual
nonnegativity of `T`), `T =O[atTop] fun n : ℕ => (n : ℝ) ^ Real.logb b a * Real.log (n : ℝ)`. -/
theorem master_case2_isBigO {T f : ℕ → ℝ} {a : ℝ} {b : ℕ} {B C : ℝ} (ha : 1 ≤ a) (hb : 1 < b)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hT_nonneg : ∀ᶠ n in atTop, 0 ≤ T n)
    (hBase : ∀ m, 1 ≤ m → m < b → T m ≤ B)
    (hStep : ∀ n, b ≤ n → T n ≤ a * T (n / b) + f n)
    (hf : ∀ m, b ≤ m → f m ≤ C * (m : ℝ) ^ Real.logb b a) :
    T =O[atTop] fun n : ℕ => (n : ℝ) ^ Real.logb b a * Real.log (n : ℝ) := by
  have hb1 : (1 : ℝ) < b := Nat.one_lt_cast.mpr hb
  have hlogb_pos : 0 < Real.log (b : ℝ) := Real.log_pos hb1
  refine IsBigO.of_bound ((B + C) / Real.log (b : ℝ)) ?_
  filter_upwards [hT_nonneg, eventually_ge_atTop b] with n hTn hbn
  have hn1 : 1 ≤ n := by omega
  have hbnR : (b : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hbn
  have hn_pos : (0 : ℝ) < n := by positivity
  have hlogn_ge1 : 1 ≤ Real.logb b n := by
    rw [← Real.logb_self_eq_one hb1]
    exact Real.logb_le_logb_of_le hb1 (zero_lt_one.trans hb1) hbnR
  have hrpow_nonneg : 0 ≤ (n : ℝ) ^ Real.logb b a := Real.rpow_nonneg hn_pos.le _
  have hlogn_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
  have hle := master_case2_le ha hb hB hC hBase hStep hf hn1
  have hstep2 : (B + C * Real.logb b n) * (n : ℝ) ^ Real.logb b a ≤
      (B + C) / Real.log (b : ℝ) * ((n : ℝ) ^ Real.logb b a * Real.log (n : ℝ)) := by
    calc
      (B + C * Real.logb b n) * (n : ℝ) ^ Real.logb b a
        ≤ ((B + C) * Real.logb b n) * (n : ℝ) ^ Real.logb b a := by
          gcongr
          nlinarith
      _ = (B + C) / Real.log (b : ℝ) * ((n : ℝ) ^ Real.logb b a * Real.log (n : ℝ)) := by
        rw [Real.logb]
        ring
  rw [Real.norm_of_nonneg hTn, Real.norm_of_nonneg (mul_nonneg hrpow_nonneg hlogn_nonneg)]
  exact hle.trans hstep2

/-- **Master Theorem — Case 2 (`=Θ[atTop]`)**: Two-sided balanced recurrence with `0 ≤ T m ≤ B`
(`1 ≤ m < b`) and `C₁ * (m : ℝ) ^ Real.logb b a ≤ f m ≤ C₂ * (m : ℝ) ^ Real.logb b a`
(`0 < C₁`, `b ≤ m`) yields
`T =Θ[atTop] fun n : ℕ => (n : ℝ) ^ Real.logb b a * Real.log (n : ℝ)`. -/
theorem master_case2_isTheta {T f : ℕ → ℝ} {a : ℝ} {b : ℕ} {B C₁ C₂ : ℝ} (ha : 1 ≤ a)
    (hb : 1 < b) (hB : 0 ≤ B) (hC₁ : 0 < C₁)
    (hBase_lo : ∀ m, 1 ≤ m → m < b → 0 ≤ T m)
    (hBase_hi : ∀ m, 1 ≤ m → m < b → T m ≤ B)
    (hStep_lo : ∀ n, b ≤ n → a * T (n / b) + f n ≤ T n)
    (hStep_hi : ∀ n, b ≤ n → T n ≤ a * T (n / b) + f n)
    (hf_lo : ∀ m, b ≤ m → C₁ * (m : ℝ) ^ Real.logb b a ≤ f m)
    (hf_hi : ∀ m, b ≤ m → f m ≤ C₂ * (m : ℝ) ^ Real.logb b a) :
    T =Θ[atTop] fun n : ℕ => (n : ℝ) ^ Real.logb b a * Real.log (n : ℝ) := by
  have hb1 : (1 : ℝ) < b := Nat.one_lt_cast.mpr hb
  have hb0 : (0 : ℝ) < b := zero_lt_one.trans hb1
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hC₂ : 0 ≤ C₂ := by
    have h := (hf_lo b le_rfl).trans (hf_hi b le_rfl)
    have hpos : 0 < (b : ℝ) ^ Real.logb b a := Real.rpow_pos_of_pos hb0 _
    nlinarith
  set p := Real.logb b a
  have hp_nonneg : 0 ≤ p := Real.logb_nonneg hb1 ha
  have hbp : (b : ℝ) ^ p = a := Real.rpow_logb hb0 hb1.ne' ha0
  have hT_nonneg_all : ∀ n, 1 ≤ n → 0 ≤ T n := by
    intro n hn
    refine (masterExpansion_nonneg ha0.le hb le_rfl ?_ n).trans
      (masterExpansion_le_rec ha0.le hb hBase_lo hStep_lo hn)
    intro m hm
    exact (mul_nonneg hC₁.le (Real.rpow_nonneg (Nat.cast_nonneg m) p)).trans (hf_lo m hm)
  have hT_nonneg : ∀ᶠ n in atTop, 0 ≤ T n := by
    filter_upwards [eventually_ge_atTop 1] with n hn using hT_nonneg_all n hn
  refine ⟨master_case2_isBigO ha hb hB hC₂ hT_nonneg hBase_hi hStep_hi hf_hi, ?_⟩
  have hlogb_pos : 0 < Real.log (b : ℝ) := Real.log_pos hb1
  have h2p_pos : 0 < (2 : ℝ) ^ p := Real.rpow_pos_of_pos zero_lt_two p
  set c₀ := C₁ / (2 * (2 : ℝ) ^ p * Real.log (b : ℝ))
  have hc₀_pos : 0 < c₀ := by positivity
  refine IsBigO.of_bound c₀⁻¹ ?_
  filter_upwards [eventually_ge_atTop (b ^ 2)] with n hbn2
  have hb2_pos : 1 ≤ b ^ 2 := Nat.one_le_pow 2 b (by omega)
  have hn1 : 1 ≤ n := hb2_pos.trans hbn2
  have hn_pos : (0 : ℝ) < n := by positivity
  have hexp_lo := masterExpansion_le_rec ha0.le hb hBase_lo hStep_lo hn1
  set k := Nat.log b n
  have hk2 : 2 ≤ k := Nat.le_log_of_pow_le hb hbn2
  have hterm_lo : ∀ i ∈ Finset.range k,
      C₁ / (2 : ℝ) ^ p * (n : ℝ) ^ p ≤ a ^ i * f (n / b ^ i) := by
    intro i hi
    set q := n / b ^ i
    have hbq : b ≤ q := le_div_pow_of_lt_log hb (Finset.mem_range.mp hi)
    have hq2 : 2 ≤ q := by omega
    have hlt_succ : n < (q + 1) * b ^ i := by
      rw [mul_comm]
      exact Nat.lt_mul_div_succ n (Nat.pow_pos (by omega))
    have hn_le_2q : (n : ℝ) ≤ (q : ℝ) * (2 * (b : ℝ) ^ i) := by
      have hnat : n ≤ 2 * q * b ^ i := by
        calc
          n ≤ (q + 1) * b ^ i := hlt_succ.le
          _ ≤ (2 * q) * b ^ i := Nat.mul_le_mul_right _ (by omega)
      have hcast : (n : ℝ) ≤ ((2 * q * b ^ i : ℕ) : ℝ) := Nat.cast_le.mpr hnat
      push_cast at hcast
      linarith
    have hbi_pos : (0 : ℝ) < (b : ℝ) ^ i := pow_pos hb0 i
    have hdiv_le_q : (n : ℝ) / (2 * (b : ℝ) ^ i) ≤ (q : ℝ) :=
      (div_le_iff₀ (by positivity)).mpr hn_le_2q
    have hpow_comm : ((b : ℝ) ^ i) ^ p = a ^ i := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hb0.le, mul_comm,
        Real.rpow_mul hb0.le, Real.rpow_natCast, hbp]
    have hqp_lo : (n : ℝ) ^ p / ((2 : ℝ) ^ p * a ^ i) ≤ (q : ℝ) ^ p := by
      calc
        (n : ℝ) ^ p / ((2 : ℝ) ^ p * a ^ i)
          = (n : ℝ) ^ p / ((2 * (b : ℝ) ^ i) ^ p) := by
            rw [Real.mul_rpow zero_le_two hbi_pos.le, hpow_comm]
        _ = ((n : ℝ) / (2 * (b : ℝ) ^ i)) ^ p :=
            (Real.div_rpow hn_pos.le (by positivity) p).symm
        _ ≤ (q : ℝ) ^ p := Real.rpow_le_rpow (by positivity) hdiv_le_q hp_nonneg
    have hai_pos : 0 < a ^ i := pow_pos ha0 i
    calc
      C₁ / (2 : ℝ) ^ p * (n : ℝ) ^ p
        = a ^ i * (C₁ * ((n : ℝ) ^ p / ((2 : ℝ) ^ p * a ^ i))) := by
          field_simp [h2p_pos.ne', hai_pos.ne']
      _ ≤ a ^ i * (C₁ * (q : ℝ) ^ p) := by gcongr
      _ ≤ a ^ i * f q := mul_le_mul_of_nonneg_left (hf_lo q hbq) hai_pos.le
  have hsum_lo : (k : ℝ) * (C₁ / (2 : ℝ) ^ p * (n : ℝ) ^ p) ≤ T n := by
    have hsum1 : ∑ _i ∈ Finset.range k, C₁ / (2 : ℝ) ^ p * (n : ℝ) ^ p ≤
        ∑ i ∈ Finset.range k, a ^ i * f (n / b ^ i) := Finset.sum_le_sum hterm_lo
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum1
    unfold masterExpansion at hexp_lo
    linarith [mul_zero (a ^ k)]
  have hlog_le_2k : Real.log (n : ℝ) / (2 * Real.log (b : ℝ)) ≤ (k : ℝ) := by
    have hn_lt_pow : (n : ℝ) < (b : ℝ) ^ ((k + 1 : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
      exact_mod_cast Nat.lt_pow_succ_log_self hb n
    have hlogb_lt : Real.logb b n < (k : ℝ) + 1 := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (Real.logb_lt_iff_lt_rpow hb1 hn_pos).mpr hn_lt_pow
    have hk_ge2R : (2 : ℝ) ≤ (k : ℝ) := Nat.ofNat_le_cast.mpr hk2
    have hlogb_le : Real.logb b n ≤ 2 * (k : ℝ) := by linarith
    rw [Real.logb] at hlogb_le
    rw [div_le_iff₀ (by positivity)]
    have hmul := (div_le_iff₀ hlogb_pos).mp hlogb_le
    linarith
  have hc₀_le : c₀ * ((n : ℝ) ^ p * Real.log (n : ℝ)) ≤ T n := by
    have hnonneg_term : 0 ≤ C₁ / (2 : ℝ) ^ p * (n : ℝ) ^ p :=
      mul_nonneg (div_nonneg hC₁.le h2p_pos.le) (Real.rpow_nonneg hn_pos.le p)
    calc
      c₀ * ((n : ℝ) ^ p * Real.log (n : ℝ))
        = (Real.log (n : ℝ) / (2 * Real.log (b : ℝ))) * (C₁ / (2 : ℝ) ^ p * (n : ℝ) ^ p) := by
          unfold c₀
          ring
      _ ≤ (k : ℝ) * (C₁ / (2 : ℝ) ^ p * (n : ℝ) ^ p) :=
          mul_le_mul_of_nonneg_right hlog_le_2k hnonneg_term
      _ ≤ T n := hsum_lo
  have hrhs_nonneg : 0 ≤ (n : ℝ) ^ p * Real.log (n : ℝ) :=
    mul_nonneg (Real.rpow_nonneg hn_pos.le p) (Real.log_nonneg (by exact_mod_cast hn1))
  rw [Real.norm_of_nonneg hrhs_nonneg, Real.norm_of_nonneg (hT_nonneg_all n hn1)]
  calc
    (n : ℝ) ^ p * Real.log (n : ℝ) = c₀⁻¹ * (c₀ * ((n : ℝ) ^ p * Real.log (n : ℝ))) := by
      field_simp [hc₀_pos.ne']
    _ ≤ c₀⁻¹ * T n := mul_le_mul_of_nonneg_left hc₀_le (inv_nonneg.mpr hc₀_pos.le)

/-- **Master Theorem — Case 2 for Mixed Floor-and-Ceiling Splits (Explicit Bound)**:
For `T n ≤ a₁ * T (n / b) + a₂ * T ((n + b - 1) / b) + f n` (`2 ≤ n`), `1 ≤ a₁ + a₂`, and
`f m ≤ C * (m : ℝ) ^ Real.logb b (a₁ + a₂)`, no monotonicity of `T` or `f` is needed. -/
theorem master_div_ceil_case2_le {T f : ℕ → ℝ} {a₁ a₂ : ℝ} {b : ℕ} {B C : ℝ}
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (ha : 1 ≤ a₁ + a₂) (hb : 1 < b) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hBase0 : T 0 ≤ B) (hBase1 : T 1 ≤ B)
    (hStep : ∀ n, 2 ≤ n → T n ≤ a₁ * T (n / b) + a₂ * T ((n + b - 1) / b) + f n)
    (hf : ∀ m, 2 ≤ m → f m ≤ C * (m : ℝ) ^ Real.logb b (a₁ + a₂)) {n : ℕ} (hn : 1 ≤ n) :
    T n ≤ (a₁ + a₂) * (B + C * (Real.logb b n + 1)) * (n : ℝ) ^ Real.logb b (a₁ + a₂) := by
  have hb1 : (1 : ℝ) < b := Nat.one_lt_cast.mpr hb
  have hb0 : (0 : ℝ) < b := zero_lt_one.trans hb1
  have ha0 : 0 < a₁ + a₂ := zero_lt_one.trans_le ha
  set p := Real.logb b (a₁ + a₂)
  have hp_nonneg : 0 ≤ p := Real.logb_nonneg hb1 ha
  let g : ℕ → ℝ := fun m => C * (m : ℝ) ^ p
  have hg_mono : Monotone g := fun x y hxy =>
    mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg x) (Nat.cast_le.mpr hxy) hp_nonneg) hC
  have hg_nonneg : ∀ m, b ≤ m → 0 ≤ g m := fun m _ =>
    mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg m) p)
  have hStep_g : ∀ m, 2 ≤ m → T m ≤ a₁ * T (m / b) + a₂ * T ((m + b - 1) / b) + g m :=
    fun m hm => (hStep m hm).trans (add_le_add_right (hf m hm) _)
  have hexp := rec_div_ceil_le_masterExpansion ha₁ ha₂ ha hb hB hg_mono hg_nonneg hBase0 hBase1
    hStep_g n
  set N := b ^ Nat.clog b n
  have hN1 : 1 ≤ N := Nat.one_le_pow _ _ (by omega)
  have hN_bound := masterExpansion_le_case2 ha hb hB hC (fun _ _ => le_rfl) hN1
  have hN_le : (N : ℝ) ≤ (b : ℝ) * (n : ℝ) := by exact_mod_cast pow_clog_le_mul hb hn
  have hN_pos : (0 : ℝ) < N := by positivity
  have hn_pos : (0 : ℝ) < n := by positivity
  have hlogN_le : Real.logb b N ≤ Real.logb b n + 1 := by
    calc
      Real.logb b N ≤ Real.logb b ((b : ℝ) * (n : ℝ)) := Real.logb_le_logb_of_le hb1 hN_pos hN_le
      _ = Real.logb b b + Real.logb b n := Real.logb_mul hb0.ne' hn_pos.ne'
      _ = Real.logb b n + 1 := by rw [Real.logb_self_eq_one hb1, add_comm]
  have hrpow_le : (N : ℝ) ^ p ≤ (a₁ + a₂) * (n : ℝ) ^ p := by
    calc
      (N : ℝ) ^ p ≤ ((b : ℝ) * (n : ℝ)) ^ p := Real.rpow_le_rpow hN_pos.le hN_le hp_nonneg
      _ = (b : ℝ) ^ p * (n : ℝ) ^ p := Real.mul_rpow hb0.le hn_pos.le
      _ = (a₁ + a₂) * (n : ℝ) ^ p := by rw [Real.rpow_logb hb0 hb1.ne' ha0]
  have hlogn_nonneg : 0 ≤ Real.logb b n := Real.logb_nonneg hb1 (by exact_mod_cast hn)
  calc
    T n ≤ (B + C * Real.logb b N) * (N : ℝ) ^ p := hexp.trans hN_bound
    _ ≤ (B + C * (Real.logb b n + 1)) * ((a₁ + a₂) * (n : ℝ) ^ p) := by
      refine mul_le_mul ?_ hrpow_le (Real.rpow_nonneg hN_pos.le p) ?_
      · gcongr
      · positivity
    _ = (a₁ + a₂) * (B + C * (Real.logb b n + 1)) * (n : ℝ) ^ p := by ring

/-- **Master Theorem — Case 2 for Mixed Floor-and-Ceiling Splits (`=O[atTop]`)**. -/
theorem master_div_ceil_case2_isBigO {T f : ℕ → ℝ} {a₁ a₂ : ℝ} {b : ℕ} {B C : ℝ}
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (ha : 1 ≤ a₁ + a₂) (hb : 1 < b) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hT_nonneg : ∀ᶠ n in atTop, 0 ≤ T n) (hBase0 : T 0 ≤ B) (hBase1 : T 1 ≤ B)
    (hStep : ∀ n, 2 ≤ n → T n ≤ a₁ * T (n / b) + a₂ * T ((n + b - 1) / b) + f n)
    (hf : ∀ m, 2 ≤ m → f m ≤ C * (m : ℝ) ^ Real.logb b (a₁ + a₂)) :
    T =O[atTop] fun n : ℕ => (n : ℝ) ^ Real.logb b (a₁ + a₂) * Real.log (n : ℝ) := by
  have hb1 : (1 : ℝ) < b := Nat.one_lt_cast.mpr hb
  have ha0 : 0 ≤ a₁ + a₂ := zero_le_one.trans ha
  have hlogb_pos : 0 < Real.log (b : ℝ) := Real.log_pos hb1
  refine IsBigO.of_bound ((a₁ + a₂) * (B + 2 * C) / Real.log (b : ℝ)) ?_
  filter_upwards [hT_nonneg, eventually_ge_atTop b] with n hTn hbn
  have hn1 : 1 ≤ n := by omega
  have hlogn_ge1 : 1 ≤ Real.logb b n := by
    rw [← Real.logb_self_eq_one hb1]
    exact Real.logb_le_logb_of_le hb1 (zero_lt_one.trans hb1) (Nat.cast_le.mpr hbn)
  have hrpow_nonneg : 0 ≤ (n : ℝ) ^ Real.logb b (a₁ + a₂) :=
    Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hlogn_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
  have hle := master_div_ceil_case2_le ha₁ ha₂ ha hb hB hC hBase0 hBase1 hStep hf hn1
  have hstep2 : (a₁ + a₂) * (B + C * (Real.logb b n + 1)) * (n : ℝ) ^ Real.logb b (a₁ + a₂) ≤
      (a₁ + a₂) * (B + 2 * C) / Real.log (b : ℝ) *
        ((n : ℝ) ^ Real.logb b (a₁ + a₂) * Real.log (n : ℝ)) := by
    calc
      (a₁ + a₂) * (B + C * (Real.logb b n + 1)) * (n : ℝ) ^ Real.logb b (a₁ + a₂)
        ≤ (a₁ + a₂) * ((B + 2 * C) * Real.logb b n) * (n : ℝ) ^ Real.logb b (a₁ + a₂) := by
          gcongr
          nlinarith
      _ = (a₁ + a₂) * (B + 2 * C) / Real.log (b : ℝ) *
            ((n : ℝ) ^ Real.logb b (a₁ + a₂) * Real.log (n : ℝ)) := by
        rw [Real.logb]
        ring
  rw [Real.norm_of_nonneg hTn, Real.norm_of_nonneg (mul_nonneg hrpow_nonneg hlogn_nonneg)]
  exact hle.trans hstep2

/-! ## Layer 2, Case 3: Super-Critical / Root-Dominated Regime -/

/-! ### Case 3A: General Regularity Form (`a * f (n / b) ≤ c * f n`, `0 ≤ c < 1`) -/

/-- Upper bound on `masterExpansion` under the Cormen regularity condition
`a * f (m / b) ≤ c * f m` (`b ≤ m`, `0 ≤ c < 1`). -/
theorem masterExpansion_le_case3_reg {a : ℝ} {b : ℕ} {B c : ℝ} {f : ℕ → ℝ} (ha : 0 ≤ a)
    (hb : 1 < b) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hReg : ∀ m, b ≤ m → a * f (m / b) ≤ c * f m) {n : ℕ} (hfn : 0 ≤ f n) :
    masterExpansion a b B f n ≤ a ^ Nat.log b n * B + f n / (1 - c) := by
  set k := Nat.log b n
  have hterm : ∀ i, i ≤ k → a ^ i * f (n / b ^ i) ≤ c ^ i * f n := by
    intro i
    induction i with
    | zero =>
      intro _
      simp
    | succ i ih =>
      intro hi
      have hik : i < k := Nat.lt_of_succ_le hi
      have hbi : b ≤ n / b ^ i := le_div_pow_of_lt_log hb hik
      calc
        a ^ (i + 1) * f (n / b ^ (i + 1))
          = a ^ i * (a * f (n / b ^ i / b)) := by
            rw [pow_succ, Nat.pow_succ, ← Nat.div_div_eq_div_mul, mul_assoc]
        _ ≤ a ^ i * (c * f (n / b ^ i)) :=
            mul_le_mul_of_nonneg_left (hReg _ hbi) (pow_nonneg ha i)
        _ = c * (a ^ i * f (n / b ^ i)) := by ring
        _ ≤ c * (c ^ i * f n) := mul_le_mul_of_nonneg_left (ih hik.le) hc0
        _ = c ^ (i + 1) * f n := by
            rw [pow_succ']
            ring
  have hsum : ∑ i ∈ Finset.range k, a ^ i * f (n / b ^ i) ≤ f n / (1 - c) := by
    calc
      ∑ i ∈ Finset.range k, a ^ i * f (n / b ^ i)
        ≤ ∑ i ∈ Finset.range k, c ^ i * f n :=
          Finset.sum_le_sum fun i hi => hterm i (Finset.mem_range.mp hi).le
      _ = (∑ i ∈ Finset.range k, c ^ i) * f n := (Finset.sum_mul _ _ _).symm
      _ ≤ (1 / (1 - c)) * f n :=
          mul_le_mul_of_nonneg_right (geom_sum_le_one_div_sub hc0 hc1 k) hfn
      _ = f n / (1 - c) := by ring
  unfold masterExpansion
  linarith

/-- **Master Theorem — Case 3 Regularity Form (Explicit Bound)**: Under `a * f (m / b) ≤ c * f m`
(`b ≤ m`, `0 ≤ c < 1`), `T n ≤ B * (n : ℝ) ^ Real.logb b a + f n / (1 - c)` for all `1 ≤ n` with
`0 ≤ f n`. -/
theorem master_case3_reg_le {T f : ℕ → ℝ} {a : ℝ} {b : ℕ} {B c : ℝ} (ha : 1 ≤ a) (hb : 1 < b)
    (hB : 0 ≤ B) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hBase : ∀ m, 1 ≤ m → m < b → T m ≤ B)
    (hStep : ∀ n, b ≤ n → T n ≤ a * T (n / b) + f n)
    (hReg : ∀ m, b ≤ m → a * f (m / b) ≤ c * f m) {n : ℕ} (hn : 1 ≤ n) (hfn : 0 ≤ f n) :
    T n ≤ B * (n : ℝ) ^ Real.logb b a + f n / (1 - c) := by
  have hexp := (rec_le_masterExpansion_of_pos (zero_le_one.trans ha) hb hBase hStep hn).trans
    (masterExpansion_le_case3_reg (zero_le_one.trans ha) hb hc0 hc1 hReg hfn)
  have hleaf := pow_natLog_le_rpow_logb ha hb hn
  nlinarith

/-- **Master Theorem — Case 3 Regularity Form (`=O[atTop]`)**: If `a * f (m / b) ≤ c * f m`
(`0 ≤ c < 1`) and `(fun n : ℕ => (n : ℝ) ^ Real.logb b a) =O[atTop] f`, then `T =O[atTop] f`. -/
theorem master_case3_reg_isBigO {T f : ℕ → ℝ} {a : ℝ} {b : ℕ} {B c : ℝ} (ha : 1 ≤ a) (hb : 1 < b)
    (hB : 0 ≤ B) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hT_nonneg : ∀ᶠ n in atTop, 0 ≤ T n) (hf_nonneg : ∀ᶠ n in atTop, 0 ≤ f n)
    (hBase : ∀ m, 1 ≤ m → m < b → T m ≤ B)
    (hStep : ∀ n, b ≤ n → T n ≤ a * T (n / b) + f n)
    (hReg : ∀ m, b ≤ m → a * f (m / b) ≤ c * f m)
    (hDom : (fun n : ℕ => (n : ℝ) ^ Real.logb b a) =O[atTop] f) :
    T =O[atTop] f := by
  obtain ⟨M, hM_pos, hM⟩ := isBigO_iff'.mp hDom
  refine IsBigO.of_bound (B * M + 1 / (1 - c)) ?_
  filter_upwards [hT_nonneg, hf_nonneg, hM, eventually_ge_atTop 1] with n hTn hfn hMn hn
  have hle := master_case3_reg_le ha hb hB hc0 hc1 hBase hStep hReg hn hfn
  have hrpow_nonneg : 0 ≤ (n : ℝ) ^ Real.logb b a := Real.rpow_nonneg (Nat.cast_nonneg n) _
  rw [Real.norm_of_nonneg hrpow_nonneg, Real.norm_of_nonneg hfn] at hMn
  rw [Real.norm_of_nonneg hTn, Real.norm_of_nonneg hfn]
  have hBM : B * (n : ℝ) ^ Real.logb b a ≤ B * (M * f n) :=
    mul_le_mul_of_nonneg_left hMn hB
  linarith [show f n / (1 - c) = 1 / (1 - c) * f n by ring]

/-- **Master Theorem — Case 3 Regularity Form (`=Θ[atTop]`)**: Two-sided recurrence under the
Cormen regularity condition yields `T =Θ[atTop] f`. -/
theorem master_case3_reg_isTheta {T f : ℕ → ℝ} {a : ℝ} {b : ℕ} {B c : ℝ} (ha : 1 ≤ a) (hb : 1 < b)
    (hB : 0 ≤ B) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hBase_lo : ∀ m, 1 ≤ m → m < b → 0 ≤ T m)
    (hBase_hi : ∀ m, 1 ≤ m → m < b → T m ≤ B)
    (hStep_lo : ∀ n, b ≤ n → a * T (n / b) + f n ≤ T n)
    (hStep_hi : ∀ n, b ≤ n → T n ≤ a * T (n / b) + f n)
    (hf_lo : ∀ m, b ≤ m → 0 ≤ f m)
    (hReg : ∀ m, b ≤ m → a * f (m / b) ≤ c * f m)
    (hDom : (fun n : ℕ => (n : ℝ) ^ Real.logb b a) =O[atTop] f) :
    T =Θ[atTop] f := by
  have ha0 : 0 ≤ a := zero_le_one.trans ha
  have hT_pos : ∀ n, 1 ≤ n → 0 ≤ T n := fun n hn =>
    (masterExpansion_nonneg ha0 hb le_rfl hf_lo n).trans
      (masterExpansion_le_rec ha0 hb hBase_lo hStep_lo hn)
  have hT_ev : ∀ᶠ n in atTop, 0 ≤ T n := by
    filter_upwards [eventually_ge_atTop 1] with n hn using hT_pos n hn
  have hf_ev : ∀ᶠ n in atTop, 0 ≤ f n := by
    filter_upwards [eventually_ge_atTop b] with n hn using hf_lo n hn
  refine ⟨master_case3_reg_isBigO ha hb hB hc0 hc1 hT_ev hf_ev hBase_hi hStep_hi hReg hDom, ?_⟩
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop b] with n hbn
  have hfn : 0 ≤ f n := hf_lo n hbn
  have hTn : 0 ≤ T n := hT_pos n (by omega)
  have hsub_nonneg : 0 ≤ T (n / b) := hT_pos (n / b) (Nat.div_pos hbn (by omega))
  have hst := hStep_lo n hbn
  rw [Real.norm_of_nonneg hfn, Real.norm_of_nonneg hTn]
  nlinarith

/-! ### Case 3B: Polynomial Form (`0 ≤ a < (b : ℝ) ^ d`) -/

private theorem pow_natLog_le_rpow_of_lt {a : ℝ} {b n : ℕ} {d : ℝ} (ha0 : 0 ≤ a) (hb : 1 < b)
    (hd : 0 ≤ d) (hab : a < (b : ℝ) ^ d) (hn : 1 ≤ n) :
    a ^ Nat.log b n ≤ (n : ℝ) ^ d := by
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
  rcases le_or_gt a 1 with ha1 | ha1
  · calc
      a ^ Nat.log b n ≤ 1 ^ Nat.log b n := by gcongr
      _ = (1 : ℝ) ^ d := by rw [one_pow, Real.one_rpow]
      _ ≤ (n : ℝ) ^ d := Real.rpow_le_rpow zero_le_one hn1R hd
  · have hb1 : (1 : ℝ) < b := Nat.one_lt_cast.mpr hb
    have hlog_lt : Real.logb b a < d :=
      (Real.logb_lt_iff_lt_rpow hb1 (zero_lt_one.trans ha1)).mpr hab
    exact (pow_natLog_le_rpow_logb ha1.le hb hn).trans
      (Real.rpow_le_rpow_of_exponent_le hn1R hlog_lt.le)

/-- Explicit upper bound on `masterExpansion` in Polynomial Case 3 (`0 ≤ a < (b : ℝ) ^ d`,
requiring no separate regularity hypothesis). -/
theorem masterExpansion_le_case3_poly {a : ℝ} {b : ℕ} {B C d : ℝ} {f : ℕ → ℝ} (ha : 0 ≤ a)
    (hb : 1 < b) (hd : 0 ≤ d) (hab : a < (b : ℝ) ^ d) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hf : ∀ m, b ≤ m → f m ≤ C * (m : ℝ) ^ d) {n : ℕ} (hn : 1 ≤ n) :
    masterExpansion a b B f n ≤ (B + C / (1 - a / (b : ℝ) ^ d)) * (n : ℝ) ^ d := by
  have hb0 : (0 : ℝ) < b := by positivity
  have hbd_pos : 0 < (b : ℝ) ^ d := Real.rpow_pos_of_pos hb0 d
  set r := a / (b : ℝ) ^ d
  set k := Nat.log b n
  have hr0 : 0 ≤ r := div_nonneg ha hbd_pos.le
  have hr1 : r < 1 := (div_lt_one hbd_pos).mpr hab
  have hleaf : a ^ k * B ≤ B * (n : ℝ) ^ d := by
    have h := pow_natLog_le_rpow_of_lt ha hb hd hab hn
    nlinarith
  have hterm : ∀ i ∈ Finset.range k, a ^ i * f (n / b ^ i) ≤ C * (n : ℝ) ^ d * r ^ i := by
    intro i hi
    have hbm : b ≤ n / b ^ i := le_div_pow_of_lt_log hb (Finset.mem_range.mp hi)
    have hai : 0 ≤ a ^ i := pow_nonneg ha i
    calc
      a ^ i * f (n / b ^ i) ≤ a ^ i * (C * ((n / b ^ i : ℕ) : ℝ) ^ d) :=
        mul_le_mul_of_nonneg_left (hf _ hbm) hai
      _ ≤ a ^ i * (C * ((n : ℝ) ^ d / ((b : ℝ) ^ d) ^ i)) := by
        gcongr
        exact natCast_div_pow_rpow_le hb hd i
      _ = C * (n : ℝ) ^ d * r ^ i := by
        rw [div_pow]
        ring
  have hnd_nonneg : 0 ≤ (n : ℝ) ^ d := Real.rpow_nonneg (Nat.cast_nonneg n) d
  have hsum : ∑ i ∈ Finset.range k, a ^ i * f (n / b ^ i) ≤ C / (1 - r) * (n : ℝ) ^ d := by
    calc
      ∑ i ∈ Finset.range k, a ^ i * f (n / b ^ i)
        ≤ ∑ i ∈ Finset.range k, C * (n : ℝ) ^ d * r ^ i := Finset.sum_le_sum hterm
      _ = C * (n : ℝ) ^ d * ∑ i ∈ Finset.range k, r ^ i := (Finset.mul_sum _ _ _).symm
      _ ≤ C * (n : ℝ) ^ d * (1 / (1 - r)) :=
          mul_le_mul_of_nonneg_left (geom_sum_le_one_div_sub hr0 hr1 k) (mul_nonneg hC hnd_nonneg)
      _ = C / (1 - r) * (n : ℝ) ^ d := by ring
  unfold masterExpansion
  linarith

/-- **Master Theorem — Case 3 Polynomial Form (Explicit Bound)**: If `0 ≤ a < (b : ℝ) ^ d`,
`T m ≤ B` (`1 ≤ m < b`), `T n ≤ a * T (n / b) + f n` (`b ≤ n`), and `f m ≤ C * (m : ℝ) ^ d`
(`b ≤ m`), then `T n ≤ (B + C / (1 - a / (b : ℝ) ^ d)) * (n : ℝ) ^ d` for all `1 ≤ n`. -/
theorem master_case3_poly_le {T f : ℕ → ℝ} {a : ℝ} {b : ℕ} {B C d : ℝ} (ha : 0 ≤ a) (hb : 1 < b)
    (hd : 0 ≤ d) (hab : a < (b : ℝ) ^ d) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hBase : ∀ m, 1 ≤ m → m < b → T m ≤ B)
    (hStep : ∀ n, b ≤ n → T n ≤ a * T (n / b) + f n)
    (hf : ∀ m, b ≤ m → f m ≤ C * (m : ℝ) ^ d) {n : ℕ} (hn : 1 ≤ n) :
    T n ≤ (B + C / (1 - a / (b : ℝ) ^ d)) * (n : ℝ) ^ d :=
  (rec_le_masterExpansion_of_pos ha hb hBase hStep hn).trans
    (masterExpansion_le_case3_poly ha hb hd hab hB hC hf hn)

/-- **Master Theorem — Case 3 Polynomial Form (`=O[atTop]`)**: For `0 ≤ a < (b : ℝ) ^ d` and
`f m ≤ C * (m : ℝ) ^ d`, `T =O[atTop] fun n : ℕ => (n : ℝ) ^ d`. -/
theorem master_case3_poly_isBigO {T f : ℕ → ℝ} {a : ℝ} {b : ℕ} {B C d : ℝ} (ha : 0 ≤ a)
    (hb : 1 < b) (hd : 0 ≤ d) (hab : a < (b : ℝ) ^ d) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hT_nonneg : ∀ᶠ n in atTop, 0 ≤ T n)
    (hBase : ∀ m, 1 ≤ m → m < b → T m ≤ B)
    (hStep : ∀ n, b ≤ n → T n ≤ a * T (n / b) + f n)
    (hf : ∀ m, b ≤ m → f m ≤ C * (m : ℝ) ^ d) :
    T =O[atTop] fun n : ℕ => (n : ℝ) ^ d := by
  refine IsBigO.of_bound (B + C / (1 - a / (b : ℝ) ^ d)) ?_
  filter_upwards [hT_nonneg, eventually_ge_atTop 1] with n hTn hn
  have hle := master_case3_poly_le ha hb hd hab hB hC hBase hStep hf hn
  have hrpow_nonneg : 0 ≤ (n : ℝ) ^ d := Real.rpow_nonneg (Nat.cast_nonneg n) d
  rw [Real.norm_of_nonneg hTn, Real.norm_of_nonneg hrpow_nonneg]
  exact hle

/-- **Master Theorem — Case 3 Polynomial Form (`=Θ[atTop]`)**: Two-sided polynomial root-dominated
recurrence with `0 ≤ a < (b : ℝ) ^ d` and `C₁ * (m : ℝ) ^ d ≤ f m ≤ C₂ * (m : ℝ) ^ d`
(`0 < C₁`, `b ≤ m`) yields `T =Θ[atTop] fun n : ℕ => (n : ℝ) ^ d`. -/
theorem master_case3_poly_isTheta {T f : ℕ → ℝ} {a : ℝ} {b : ℕ} {B C₁ C₂ d : ℝ} (ha : 0 ≤ a)
    (hb : 1 < b) (hd : 0 ≤ d) (hab : a < (b : ℝ) ^ d) (hB : 0 ≤ B) (hC₁ : 0 < C₁)
    (hBase_lo : ∀ m, 1 ≤ m → m < b → 0 ≤ T m)
    (hBase_hi : ∀ m, 1 ≤ m → m < b → T m ≤ B)
    (hStep_lo : ∀ n, b ≤ n → a * T (n / b) + f n ≤ T n)
    (hStep_hi : ∀ n, b ≤ n → T n ≤ a * T (n / b) + f n)
    (hf_lo : ∀ m, b ≤ m → C₁ * (m : ℝ) ^ d ≤ f m)
    (hf_hi : ∀ m, b ≤ m → f m ≤ C₂ * (m : ℝ) ^ d) :
    T =Θ[atTop] fun n : ℕ => (n : ℝ) ^ d := by
  have hb0 : (0 : ℝ) < b := by positivity
  have hC₂ : 0 ≤ C₂ := by
    have h := (hf_lo b le_rfl).trans (hf_hi b le_rfl)
    have hpos : 0 < (b : ℝ) ^ d := Real.rpow_pos_of_pos hb0 d
    nlinarith
  have hf_nonneg : ∀ m, b ≤ m → 0 ≤ f m := fun m hm =>
    (mul_nonneg hC₁.le (Real.rpow_nonneg (Nat.cast_nonneg m) d)).trans (hf_lo m hm)
  have hT_pos : ∀ n, 1 ≤ n → 0 ≤ T n := fun n hn =>
    (masterExpansion_nonneg ha hb le_rfl hf_nonneg n).trans
      (masterExpansion_le_rec ha hb hBase_lo hStep_lo hn)
  have hT_ev : ∀ᶠ n in atTop, 0 ≤ T n := by
    filter_upwards [eventually_ge_atTop 1] with n hn using hT_pos n hn
  refine ⟨master_case3_poly_isBigO ha hb hd hab hB hC₂ hT_ev hBase_hi hStep_hi hf_hi, ?_⟩
  refine IsBigO.of_bound C₁⁻¹ ?_
  filter_upwards [eventually_ge_atTop b] with n hbn
  have hrpow_nonneg : 0 ≤ (n : ℝ) ^ d := Real.rpow_nonneg (Nat.cast_nonneg n) d
  have hTn : 0 ≤ T n := hT_pos n (by omega)
  have hsub_nonneg : 0 ≤ T (n / b) := hT_pos (n / b) (Nat.div_pos hbn (by omega))
  have hlo : C₁ * (n : ℝ) ^ d ≤ T n := by
    have h1 := hf_lo n hbn
    have h2 := hStep_lo n hbn
    nlinarith
  rw [Real.norm_of_nonneg hrpow_nonneg, Real.norm_of_nonneg hTn]
  calc
    (n : ℝ) ^ d = C₁⁻¹ * (C₁ * (n : ℝ) ^ d) := by field_simp [hC₁.ne']
    _ ≤ C₁⁻¹ * T n := mul_le_mul_of_nonneg_left hlo (inv_nonneg.mpr hC₁.le)

/-- **Master Theorem — Case 3 Polynomial Form for Mixed Floor-and-Ceiling Splits (Explicit Bound)**:
For `T n ≤ a₁ * T (n / b) + a₂ * T ((n + b - 1) / b) + f n` (`2 ≤ n`), `1 ≤ a₁ + a₂ < (b : ℝ) ^ d`,
no monotonicity of `T` or `f` is needed. -/
theorem master_div_ceil_case3_poly_le {T f : ℕ → ℝ} {a₁ a₂ : ℝ} {b : ℕ} {B C d : ℝ}
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (ha : 1 ≤ a₁ + a₂) (hb : 1 < b) (hd : 0 ≤ d)
    (hab : a₁ + a₂ < (b : ℝ) ^ d) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hBase0 : T 0 ≤ B) (hBase1 : T 1 ≤ B)
    (hStep : ∀ n, 2 ≤ n → T n ≤ a₁ * T (n / b) + a₂ * T ((n + b - 1) / b) + f n)
    (hf : ∀ m, 2 ≤ m → f m ≤ C * (m : ℝ) ^ d) {n : ℕ} (hn : 1 ≤ n) :
    T n ≤ (b : ℝ) ^ d * (B + C / (1 - (a₁ + a₂) / (b : ℝ) ^ d)) * (n : ℝ) ^ d := by
  have hb0 : (0 : ℝ) < b := by positivity
  have hbd_pos : 0 < (b : ℝ) ^ d := Real.rpow_pos_of_pos hb0 d
  let g : ℕ → ℝ := fun m => C * (m : ℝ) ^ d
  have hg_mono : Monotone g := fun x y hxy =>
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg x) (Nat.cast_le.mpr hxy) hd) hC
  have hg_nonneg : ∀ m, b ≤ m → 0 ≤ g m := fun m _ =>
    mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg m) d)
  have hStep_g : ∀ m, 2 ≤ m → T m ≤ a₁ * T (m / b) + a₂ * T ((m + b - 1) / b) + g m :=
    fun m hm => (hStep m hm).trans (add_le_add_right (hf m hm) _)
  have hexp := rec_div_ceil_le_masterExpansion ha₁ ha₂ ha hb hB hg_mono hg_nonneg hBase0 hBase1
    hStep_g n
  set N := b ^ Nat.clog b n
  have hN1 : 1 ≤ N := Nat.one_le_pow _ _ (by omega)
  have hN_bound := masterExpansion_le_case3_poly (zero_le_one.trans ha) hb hd hab hB hC
    (fun _ _ => le_rfl) hN1
  have hN_le : (N : ℝ) ≤ (b : ℝ) * (n : ℝ) := by exact_mod_cast pow_clog_le_mul hb hn
  have hrpow_le : (N : ℝ) ^ d ≤ (b : ℝ) ^ d * (n : ℝ) ^ d := by
    calc
      (N : ℝ) ^ d ≤ ((b : ℝ) * (n : ℝ)) ^ d := Real.rpow_le_rpow (Nat.cast_nonneg N) hN_le hd
      _ = (b : ℝ) ^ d * (n : ℝ) ^ d := Real.mul_rpow hb0.le (Nat.cast_nonneg n)
  have hr1 : (a₁ + a₂) / (b : ℝ) ^ d < 1 := (div_lt_one hbd_pos).mpr hab
  have hconst_nonneg : 0 ≤ B + C / (1 - (a₁ + a₂) / (b : ℝ) ^ d) :=
    add_nonneg hB (div_nonneg hC (sub_nonneg.mpr hr1.le))
  calc
    T n ≤ (B + C / (1 - (a₁ + a₂) / (b : ℝ) ^ d)) * (N : ℝ) ^ d := hexp.trans hN_bound
    _ ≤ (B + C / (1 - (a₁ + a₂) / (b : ℝ) ^ d)) * ((b : ℝ) ^ d * (n : ℝ) ^ d) :=
      mul_le_mul_of_nonneg_left hrpow_le hconst_nonneg
    _ = (b : ℝ) ^ d * (B + C / (1 - (a₁ + a₂) / (b : ℝ) ^ d)) * (n : ℝ) ^ d := by ring

/-- **Master Theorem — Case 3 Polynomial Form for Mixed Floor-and-Ceiling Splits (`=O[atTop]`)**. -/
theorem master_div_ceil_case3_poly_isBigO {T f : ℕ → ℝ} {a₁ a₂ : ℝ} {b : ℕ} {B C d : ℝ}
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (ha : 1 ≤ a₁ + a₂) (hb : 1 < b) (hd : 0 ≤ d)
    (hab : a₁ + a₂ < (b : ℝ) ^ d) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hT_nonneg : ∀ᶠ n in atTop, 0 ≤ T n) (hBase0 : T 0 ≤ B) (hBase1 : T 1 ≤ B)
    (hStep : ∀ n, 2 ≤ n → T n ≤ a₁ * T (n / b) + a₂ * T ((n + b - 1) / b) + f n)
    (hf : ∀ m, 2 ≤ m → f m ≤ C * (m : ℝ) ^ d) :
    T =O[atTop] fun n : ℕ => (n : ℝ) ^ d := by
  refine IsBigO.of_bound ((b : ℝ) ^ d * (B + C / (1 - (a₁ + a₂) / (b : ℝ) ^ d))) ?_
  filter_upwards [hT_nonneg, eventually_ge_atTop 1] with n hTn hn
  have hle := master_div_ceil_case3_poly_le ha₁ ha₂ ha hb hd hab hB hC hBase0 hBase1 hStep hf hn
  have hrpow_nonneg : 0 ≤ (n : ℝ) ^ d := Real.rpow_nonneg (Nat.cast_nonneg n) d
  rw [Real.norm_of_nonneg hTn, Real.norm_of_nonneg hrpow_nonneg]
  exact hle

/-! ## Layer 3: Concrete `ℕ` Recurrences & `TimeM` Paradigm Combinators -/

/-- Pure `ℕ` recursion-tree expansion bound for `T n ≤ a * T (n / b) + f n`. -/
theorem nat_rec_le_pow_log_add_sum {T f : ℕ → ℕ} {a b B : ℕ} (hb : 1 < b)
    (hBase : ∀ m < b, T m ≤ B) (hStep : ∀ n, b ≤ n → T n ≤ a * T (n / b) + f n) (n : ℕ) :
    T n ≤ a ^ Nat.log b n * B + ∑ i ∈ Finset.range (Nat.log b n), a ^ i * f (n / b ^ i) := by
  have hR := rec_le_masterExpansion (T := fun m => (T m : ℝ)) (f := fun m => (f m : ℝ))
    (a := (a : ℝ)) (B := (B : ℝ)) (Nat.cast_nonneg a) hb
    (fun m hm => Nat.cast_le.mpr (hBase m hm))
    (fun m hm => by exact_mod_cast hStep m hm) n
  unfold masterExpansion at hR
  rw [← Nat.cast_le (α := ℝ)]
  push_cast
  exact hR

/-- **Binary Search Recurrence (`ℕ` Explicit Bound)**: If `T 0 ≤ B`, `T 1 ≤ B`, and
`T n ≤ T (n / 2) + c` for `2 ≤ n`, then `T n ≤ B + c * Nat.log 2 n` for all `n : ℕ`. -/
theorem master_binary_search {T : ℕ → ℕ} {B c : ℕ} (hBase0 : T 0 ≤ B) (hBase1 : T 1 ≤ B)
    (hStep : ∀ n, 2 ≤ n → T n ≤ T (n / 2) + c) (n : ℕ) :
    T n ≤ B + c * Nat.log 2 n := by
  have hbase : ∀ m < 2, T m ≤ B := by
    intro m hm
    rcases m with _ | _ | m
    · exact hBase0
    · exact hBase1
    · omega
  have hexp := nat_rec_le_pow_log_add_sum (a := 1) (f := fun _ => c) Nat.one_lt_two hbase
    (fun m hm => by simpa only [one_mul] using hStep m hm) n
  simp only [one_pow, one_mul, Finset.sum_const, Finset.card_range, smul_eq_mul] at hexp
  linarith

/-- **Binary Search Recurrence (`=O[atTop]`)**: `T n ≤ T (n / 2) + c` implies
`(fun n => (T n : ℝ)) =O[atTop] fun n : ℕ => Real.log (n : ℝ)`. -/
theorem master_binary_search_isBigO {T : ℕ → ℕ} {B c : ℕ} (hBase1 : T 1 ≤ B)
    (hStep : ∀ n, 2 ≤ n → T n ≤ T (n / 2) + c) :
    (fun n => (T n : ℝ)) =O[atTop] fun n : ℕ => Real.log (n : ℝ) := by
  have hbase : ∀ m, 1 ≤ m → m < 2 → (T m : ℝ) ≤ (B : ℝ) := by
    intro m hm1 hm2
    obtain rfl : m = 1 := by omega
    exact_mod_cast hBase1
  have hbigO := master_case2_isBigO (T := fun n => (T n : ℝ)) (f := fun _ => (c : ℝ))
    (a := 1) (b := 2) (B := (B : ℝ)) (C := (c : ℝ)) le_rfl Nat.one_lt_two
    (Nat.cast_nonneg B) (Nat.cast_nonneg c)
    (Eventually.of_forall fun n => Nat.cast_nonneg (T n)) hbase
    (fun n hn => by
      have h := hStep n hn
      simpa only [one_mul, Nat.cast_add] using (Nat.cast_le.mpr h : (T n : ℝ) ≤ _))
    (fun m _ => by simp)
  simpa only [Real.logb_one, Real.rpow_zero, one_mul] using hbigO

/-- **Ceiling Binary Search Recurrence (`ℕ` Explicit Bound)**: If `T 0 ≤ B`, `T 1 ≤ B`, and
`T n ≤ T ((n + 1) / 2) + c` for `2 ≤ n`, then `T n ≤ B + c * Nat.clog 2 n` for all `n : ℕ`. -/
theorem master_binary_search_ceil {T : ℕ → ℕ} {B c : ℕ} (hBase0 : T 0 ≤ B) (hBase1 : T 1 ≤ B)
    (hStep : ∀ n, 2 ≤ n → T n ≤ T ((n + 1) / 2) + c) (n : ℕ) :
    T n ≤ B + c * Nat.clog 2 n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases n with _ | _ | m
    · simpa using hBase0
    · simpa using hBase1
    · set N := m + 2
      have hN : 2 ≤ N := by omega
      have hlt : (N + 1) / 2 < N := by omega
      have hclog : Nat.clog 2 N = Nat.clog 2 ((N + 1) / 2) + 1 := by
        simpa using Nat.clog_of_two_le Nat.one_lt_two hN
      have hih := ih ((N + 1) / 2) hlt
      have hst := hStep N hN
      rw [hclog, Nat.mul_add, Nat.mul_one]
      omega

/-- **Ceiling Binary Search Recurrence (`=O[atTop]`)**: `T n ≤ T ((n + 1) / 2) + c` implies
`(fun n => (T n : ℝ)) =O[atTop] fun n : ℕ => Real.log (n : ℝ)`. -/
theorem master_binary_search_ceil_isBigO {T : ℕ → ℕ} {B c : ℕ} (hBase0 : T 0 ≤ B)
    (hBase1 : T 1 ≤ B) (hStep : ∀ n, 2 ≤ n → T n ≤ T ((n + 1) / 2) + c) :
    (fun n => (T n : ℝ)) =O[atTop] fun n : ℕ => Real.log (n : ℝ) := by
  have hbigO := master_div_ceil_case2_isBigO (T := fun n => (T n : ℝ)) (f := fun _ => (c : ℝ))
    (a₁ := 0) (a₂ := 1) (b := 2) (B := (B : ℝ)) (C := (c : ℝ))
    le_rfl zero_le_one (by norm_num) Nat.one_lt_two (Nat.cast_nonneg B) (Nat.cast_nonneg c)
    (Eventually.of_forall fun n => Nat.cast_nonneg (T n))
    (Nat.cast_le.mpr hBase0) (Nat.cast_le.mpr hBase1)
    (fun n hn => by
      have heq : (n + 2 - 1) / 2 = (n + 1) / 2 := by omega
      rw [heq, zero_mul, zero_add, one_mul]
      exact_mod_cast hStep n hn)
    (fun m _ => by simp)
  simpa only [zero_add, Real.logb_one, Real.rpow_zero, one_mul] using hbigO

/-- **Geometric Linear Halving (`ℕ` Explicit Bound)**: If `T 0 ≤ B`, `T 1 ≤ B`, and
`T n ≤ T (n / 2) + c * n` for `2 ≤ n` (as in quickselect / geometric shrinking), then
`T n ≤ B + 2 * c * n` for all `n : ℕ`. -/
theorem master_linear_divide {T : ℕ → ℕ} {B c : ℕ} (hBase0 : T 0 ≤ B) (hBase1 : T 1 ≤ B)
    (hStep : ∀ n, 2 ≤ n → T n ≤ T (n / 2) + c * n) (n : ℕ) :
    T n ≤ B + 2 * c * n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases n with _ | _ | m
    · simpa using hBase0
    · exact hBase1.trans (Nat.le_add_right B _)
    · set N := m + 2
      have hN : 2 ≤ N := by omega
      have hih := ih (N / 2) (Nat.div_lt_self (by omega) Nat.one_lt_two)
      have hst := hStep N hN
      have hmul : 2 * c * (N / 2) ≤ c * N := by
        calc
          2 * c * (N / 2) = c * (2 * (N / 2)) := by ring
          _ ≤ c * N := Nat.mul_le_mul_left c (Nat.mul_div_le N 2)
      calc
        T N ≤ B + 2 * c * (N / 2) + c * N := by omega
        _ ≤ B + c * N + c * N := by omega
        _ = B + 2 * c * N := by ring

/-- **Geometric Linear Halving (`=O[atTop]`)**: `T n ≤ T (n / 2) + c * n` implies
`(fun n => (T n : ℝ)) =O[atTop] fun n : ℕ => (n : ℝ)`. -/
theorem master_linear_divide_isBigO {T : ℕ → ℕ} {B c : ℕ} (hBase1 : T 1 ≤ B)
    (hStep : ∀ n, 2 ≤ n → T n ≤ T (n / 2) + c * n) :
    (fun n => (T n : ℝ)) =O[atTop] fun n : ℕ => (n : ℝ) := by
  have hbase : ∀ m, 1 ≤ m → m < 2 → (T m : ℝ) ≤ (B : ℝ) := by
    intro m hm1 hm2
    obtain rfl : m = 1 := by omega
    exact_mod_cast hBase1
  have hbigO := master_case3_poly_isBigO (T := fun n => (T n : ℝ))
    (f := fun n => (c : ℝ) * (n : ℝ) ^ (1 : ℝ)) (a := 1) (b := 2) (B := (B : ℝ))
    (C := (c : ℝ)) (d := 1) zero_le_one Nat.one_lt_two zero_le_one
    (by norm_num) (Nat.cast_nonneg B) (Nat.cast_nonneg c)
    (Eventually.of_forall fun n => Nat.cast_nonneg (T n)) hbase
    (fun n hn => by
      have h := hStep n hn
      simpa only [one_mul, Real.rpow_one, Nat.cast_add, Nat.cast_mul] using
        (Nat.cast_le.mpr h : (T n : ℝ) ≤ _))
    (fun _ _ => le_rfl)
  simpa only [Real.rpow_one] using hbigO

/-- **Binary Split with Linear Combine (`ℕ` Explicit Floor Bound)**: If `T 1 ≤ B` and
`T n ≤ 2 * T (n / 2) + c * n` for `2 ≤ n`, then `T n ≤ B * n + c * n * Nat.log 2 n` for all
`1 ≤ n`. -/
theorem master_binary_split_linear {T : ℕ → ℕ} {B c : ℕ} (hBase1 : T 1 ≤ B)
    (hStep : ∀ n, 2 ≤ n → T n ≤ 2 * T (n / 2) + c * n) {n : ℕ} (hn : 1 ≤ n) :
    T n ≤ B * n + c * n * Nat.log 2 n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases lt_or_ge n 2 with hn2 | hn2
    · obtain rfl : n = 1 := by omega
      simpa using hBase1
    · have hih := ih (n / 2) (Nat.div_lt_self (by omega) Nat.one_lt_two) (by omega)
      have hst := hStep n hn2
      set k := Nat.log 2 (n / 2)
      have hlog : Nat.log 2 n = k + 1 := Nat.log_of_one_lt_of_le Nat.one_lt_two hn2
      have h2div : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
      have hB_le : 2 * (B * (n / 2)) ≤ B * n := by
        calc
          2 * (B * (n / 2)) = B * (2 * (n / 2)) := by ring
          _ ≤ B * n := Nat.mul_le_mul_left B h2div
      have hc_le : 2 * (c * (n / 2) * k) ≤ c * n * k := by
        calc
          2 * (c * (n / 2) * k) = c * (2 * (n / 2)) * k := by ring
          _ ≤ c * n * k := Nat.mul_le_mul_right k (Nat.mul_le_mul_left c h2div)
      calc
        T n ≤ 2 * (B * (n / 2) + c * (n / 2) * k) + c * n := by omega
        _ = 2 * (B * (n / 2)) + 2 * (c * (n / 2) * k) + c * n := by ring
        _ ≤ B * n + c * n * k + c * n := by omega
        _ = B * n + c * n * (k + 1) := by ring
        _ = B * n + c * n * Nat.log 2 n := by rw [← hlog]

/-- **Balanced Binary Split with Linear Combine (`ℕ` Explicit MergeSort Bound)**: If `T 1 ≤ B` and
`T n ≤ T (n / 2) + T ((n + 1) / 2) + c * n` for `2 ≤ n`, then
`T n ≤ B * n + c * n * Nat.clog 2 n` for all `1 ≤ n`. -/
theorem master_balanced_split_linear {T : ℕ → ℕ} {B c : ℕ} (hBase1 : T 1 ≤ B)
    (hStep : ∀ n, 2 ≤ n → T n ≤ T (n / 2) + T ((n + 1) / 2) + c * n) {n : ℕ} (hn : 1 ≤ n) :
    T n ≤ B * n + c * n * Nat.clog 2 n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases lt_or_ge n 2 with hn2 | hn2
    · obtain rfl : n = 1 := by omega
      simpa using hBase1
    · have hih_lo := ih (n / 2) (Nat.div_lt_self (by omega) Nat.one_lt_two) (by omega)
      have hih_hi := ih ((n + 1) / 2) (by omega) (by omega)
      set k := Nat.clog 2 ((n + 1) / 2)
      have hclog_eq : Nat.clog 2 n = k + 1 := by
        simpa using Nat.clog_of_two_le Nat.one_lt_two hn2
      have hclog_lo : Nat.clog 2 (n / 2) ≤ k :=
        Nat.clog_mono_right 2 (Nat.div_le_div_right (by omega))
      have hlo_k : T (n / 2) ≤ B * (n / 2) + c * (n / 2) * k :=
        hih_lo.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hclog_lo) _)
      have hsplit : n / 2 + (n + 1) / 2 = n := by omega
      have hst := hStep n hn2
      calc
        T n ≤ (B * (n / 2) + c * (n / 2) * k) +
              (B * ((n + 1) / 2) + c * ((n + 1) / 2) * k) + c * n := by omega
        _ = B * (n / 2 + (n + 1) / 2) + c * (n / 2 + (n + 1) / 2) * k + c * n := by ring
        _ = B * n + c * n * (k + 1) := by
          rw [hsplit]
          ring
        _ = B * n + c * n * Nat.clog 2 n := by rw [← hclog_eq]

/-- **Balanced Binary Split with Linear Combine (`=O[atTop]`)**:
`T n ≤ T (n / 2) + T ((n + 1) / 2) + c * n` implies
`(fun n => (T n : ℝ)) =O[atTop] fun n : ℕ => (n : ℝ) * Real.log (n : ℝ)`. -/
theorem master_balanced_split_linear_isBigO {T : ℕ → ℕ} {B c : ℕ} (hBase0 : T 0 ≤ B)
    (hBase1 : T 1 ≤ B) (hStep : ∀ n, 2 ≤ n → T n ≤ T (n / 2) + T ((n + 1) / 2) + c * n) :
    (fun n => (T n : ℝ)) =O[atTop] fun n : ℕ => (n : ℝ) * Real.log (n : ℝ) := by
  have hlog2 : Real.logb ((2 : ℕ) : ℝ) (1 + 1) = 1 := by
    norm_num [Real.logb_self_eq_one one_lt_two]
  have hbigO := master_div_ceil_case2_isBigO (T := fun n => (T n : ℝ))
    (f := fun n => (c : ℝ) * (n : ℝ)) (a₁ := 1) (a₂ := 1) (b := 2)
    (B := (B : ℝ)) (C := (c : ℝ)) zero_le_one zero_le_one (by norm_num) Nat.one_lt_two
    (Nat.cast_nonneg B) (Nat.cast_nonneg c)
    (Eventually.of_forall fun n => Nat.cast_nonneg (T n))
    (Nat.cast_le.mpr hBase0) (Nat.cast_le.mpr hBase1)
    (fun n hn => by
      have heq : (n + 2 - 1) / 2 = (n + 1) / 2 := by omega
      rw [heq, one_mul, one_mul]
      exact_mod_cast hStep n hn)
    (fun m _ => by rw [hlog2, Real.rpow_one])
  simpa only [hlog2, Real.rpow_one] using hbigO

/-- **Karatsuba Multiplication Recurrence (Explicit Bound)**: For `T 1 ≤ B` and
`T n ≤ 3 * T (n / 2) + c * n` (`2 ≤ n`), `(T n : ℝ) ≤ (B + 2 * c) * (n : ℝ) ^ Real.logb 2 3`
for all `1 ≤ n`. -/
theorem master_karatsuba_le {T : ℕ → ℕ} {B c : ℕ} (hBase1 : T 1 ≤ B)
    (hStep : ∀ n, 2 ≤ n → T n ≤ 3 * T (n / 2) + c * n) {n : ℕ} (hn : 1 ≤ n) :
    (T n : ℝ) ≤ ((B : ℝ) + 2 * (c : ℝ)) * (n : ℝ) ^ Real.logb 2 3 := by
  have hbase : ∀ m, 1 ≤ m → m < 2 → (T m : ℝ) ≤ (B : ℝ) := by
    intro m hm1 hm2
    obtain rfl : m = 1 := by omega
    exact_mod_cast hBase1
  have hle := master_case1_le (T := fun m => (T m : ℝ)) (f := fun m => (c : ℝ) * (m : ℝ))
    (a := 3) (b := 2) (B := (B : ℝ)) (C := (c : ℝ)) (d := 1)
    Nat.one_lt_two zero_le_one (by norm_num) (Nat.cast_nonneg B) (Nat.cast_nonneg c) hbase
    (fun m hm => by exact_mod_cast hStep m hm)
    (fun m _ => by rw [Real.rpow_one]) hn
  have hconst : (B : ℝ) + (c : ℝ) / ((3 : ℝ) / (2 : ℝ) ^ (1 : ℝ) - 1) =
      (B : ℝ) + 2 * (c : ℝ) := by
    rw [Real.rpow_one]
    ring
  simpa only [Nat.cast_ofNat, hconst] using hle

/-- **Karatsuba Multiplication Recurrence (`=O[atTop]`)**: `T n ≤ 3 * T (n / 2) + c * n` implies
`(fun n => (T n : ℝ)) =O[atTop] fun n : ℕ => (n : ℝ) ^ Real.logb 2 3`. -/
theorem master_karatsuba_isBigO {T : ℕ → ℕ} {B c : ℕ} (hBase1 : T 1 ≤ B)
    (hStep : ∀ n, 2 ≤ n → T n ≤ 3 * T (n / 2) + c * n) :
    (fun n => (T n : ℝ)) =O[atTop] fun n : ℕ => (n : ℝ) ^ Real.logb 2 3 := by
  refine IsBigO.of_bound ((B : ℝ) + 2 * (c : ℝ)) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hle := master_karatsuba_le hBase1 hStep hn
  rw [Real.norm_of_nonneg (Nat.cast_nonneg (T n)),
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  exact hle

/-- **Strassen Matrix Multiplication Recurrence (Explicit Bound)**: For `T 1 ≤ B` and
`T n ≤ 7 * T (n / 2) + c * n ^ 2` (`2 ≤ n`),
`(T n : ℝ) ≤ (B + 4 / 3 * c) * (n : ℝ) ^ Real.logb 2 7` for all `1 ≤ n`. -/
theorem master_strassen_le {T : ℕ → ℕ} {B c : ℕ} (hBase1 : T 1 ≤ B)
    (hStep : ∀ n, 2 ≤ n → T n ≤ 7 * T (n / 2) + c * n ^ 2) {n : ℕ} (hn : 1 ≤ n) :
    (T n : ℝ) ≤ ((B : ℝ) + 4 / 3 * (c : ℝ)) * (n : ℝ) ^ Real.logb 2 7 := by
  have hbase : ∀ m, 1 ≤ m → m < 2 → (T m : ℝ) ≤ (B : ℝ) := by
    intro m hm1 hm2
    obtain rfl : m = 1 := by omega
    exact_mod_cast hBase1
  have hpow2 : ((2 : ℕ) : ℝ) ^ (2 : ℝ) = 4 := by
    norm_num [Real.rpow_natCast]
  have hle := master_case1_le (T := fun m => (T m : ℝ))
    (f := fun m => (c : ℝ) * (m : ℝ) ^ (2 : ℕ))
    (a := 7) (b := 2) (B := (B : ℝ)) (C := (c : ℝ)) (d := 2)
    Nat.one_lt_two (by norm_num) (by linarith) (Nat.cast_nonneg B) (Nat.cast_nonneg c) hbase
    (fun m hm => by exact_mod_cast hStep m hm)
    (fun m _ => by
      have hm2 : (m : ℝ) ^ (2 : ℝ) = (m : ℝ) ^ (2 : ℕ) :=
        Real.rpow_natCast (m : ℝ) 2
      rw [hm2]) hn
  have hconst : (B : ℝ) + (c : ℝ) / ((7 : ℝ) / (2 : ℝ) ^ (2 : ℝ) - 1) =
      (B : ℝ) + 4 / 3 * (c : ℝ) := by
    have h24 : (2 : ℝ) ^ (2 : ℝ) = 4 := by exact_mod_cast hpow2
    rw [h24]
    ring
  simpa only [Nat.cast_ofNat, hconst] using hle

/-- **Strassen Matrix Multiplication Recurrence (`=O[atTop]`)**:
`T n ≤ 7 * T (n / 2) + c * n ^ 2` implies
`(fun n => (T n : ℝ)) =O[atTop] fun n : ℕ => (n : ℝ) ^ Real.logb 2 7`. -/
theorem master_strassen_isBigO {T : ℕ → ℕ} {B c : ℕ} (hBase1 : T 1 ≤ B)
    (hStep : ∀ n, 2 ≤ n → T n ≤ 7 * T (n / 2) + c * n ^ 2) :
    (fun n => (T n : ℝ)) =O[atTop] fun n : ℕ => (n : ℝ) ^ Real.logb 2 7 := by
  refine IsBigO.of_bound ((B : ℝ) + 4 / 3 * (c : ℝ)) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hle := master_strassen_le hBase1 hStep hn
  rw [Real.norm_of_nonneg (Nat.cast_nonneg (T n)),
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  exact hle

/-! ### `TimeM` Divide-and-Conquer Paradigm Combinators -/

private theorem list_sum_map_le {α : Type*} (ys : List α) (g : α → ℝ) {M : ℝ}
    (hg : ∀ y ∈ ys, g y ≤ M) : (ys.map g).sum ≤ (ys.length : ℝ) * M := by
  induction ys with
  | nil => simp
  | cons y ys ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    have hy : g y ≤ M := hg y (by simp)
    have hys : (ys.map g).sum ≤ (ys.length : ℝ) * M :=
      ih fun z hz => hg z (by simp [hz])
    linarith

namespace TimeM

/-- **Algorithmic Divide-and-Conquer Bound (`TimeM`, Floor Subproblems)**:
If a `TimeM ℕ` algorithm `alg` with size measure `size : α → ℕ` costs at most `B` on base inputs
(`size x < b`) and on larger inputs (`b ≤ size x`) makes at most `a` recursive calls `ys` each of
size `≤ size x / b` with combine overhead `f (size x)`, then
`((alg x).time : ℝ) ≤ masterExpansion a b B f (size x)` for every input `x : α` — without needing
to define an intermediate recurrence function on `ℕ`. -/
theorem time_le_masterExpansion {α β : Type*} (alg : α → TimeM ℕ β) (size : α → ℕ)
    {a b : ℕ} {B : ℝ} {f : ℕ → ℝ} (ha : 1 ≤ a) (hb : 1 < b) (hB : 0 ≤ B)
    (hf_mono : Monotone f) (hf_nonneg : ∀ m, b ≤ m → 0 ≤ f m)
    (hBase : ∀ x, size x < b → ((alg x).time : ℝ) ≤ B)
    (hStep : ∀ x, b ≤ size x → ∃ ys : List α, ys.length ≤ a ∧
      (∀ y ∈ ys, size y ≤ size x / b) ∧
      ((alg x).time : ℝ) ≤ (ys.map fun y => ((alg y).time : ℝ)).sum + f (size x))
    (x : α) :
    ((alg x).time : ℝ) ≤ masterExpansion (a : ℝ) b B f (size x) := by
  have haR : (1 : ℝ) ≤ a := Nat.one_le_cast.mpr ha
  have hmono := masterExpansion_mono haR hb hB hf_mono hf_nonneg
  suffices ∀ n (z : α), size z = n →
      ((alg z).time : ℝ) ≤ masterExpansion (a : ℝ) b B f n from this (size x) x rfl
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro z hsz
    rcases lt_or_ge n b with hnb | hbn
    · rw [masterExpansion_of_lt _ B f hnb]
      exact hBase z (hsz ▸ hnb)
    · obtain ⟨ys, hlen, hys_sz, htime⟩ := hStep z (hsz ▸ hbn)
      rw [hsz] at hys_sz htime
      have hdiv_lt : n / b < n := Nat.div_lt_self (by omega) hb
      have hE_nonneg : 0 ≤ masterExpansion (a : ℝ) b B f (n / b) :=
        masterExpansion_nonneg (zero_le_one.trans haR) hb hB hf_nonneg (n / b)
      have hys_bound : ∀ y ∈ ys,
          ((alg y).time : ℝ) ≤ masterExpansion (a : ℝ) b B f (n / b) := by
        intro y hy
        have hsy : size y ≤ n / b := hys_sz y hy
        exact (ih (size y) (hsy.trans_lt hdiv_lt) y rfl).trans (hmono hsy)
      have hsum_le : (ys.map fun y => ((alg y).time : ℝ)).sum ≤
          (a : ℝ) * masterExpansion (a : ℝ) b B f (n / b) := by
        calc
          (ys.map fun y => ((alg y).time : ℝ)).sum
            ≤ (ys.length : ℝ) * masterExpansion (a : ℝ) b B f (n / b) :=
              list_sum_map_le ys _ hys_bound
          _ ≤ (a : ℝ) * masterExpansion (a : ℝ) b B f (n / b) :=
              mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hlen) hE_nonneg
      rw [masterExpansion_of_le (a : ℝ) hb B f hbn]
      linarith

/-- **Algorithmic Divide-and-Conquer Bound (`TimeM`, Balanced / Ceiling Subproblems)**:
If base inputs (`size x ≤ 1`) cost at most `B` and recursive inputs (`2 ≤ size x`) make at most
`a` recursive calls each of size `≤ (size x + b - 1) / b`, then
`((alg x).time : ℝ) ≤ masterExpansion a b B f (b ^ Nat.clog b (size x))` for every `x : α`. -/
theorem time_le_masterExpansion_ceil {α β : Type*} (alg : α → TimeM ℕ β) (size : α → ℕ)
    {a b : ℕ} {B : ℝ} {f : ℕ → ℝ} (ha : 1 ≤ a) (hb : 1 < b) (hB : 0 ≤ B)
    (hf_mono : Monotone f) (hf_nonneg : ∀ m, b ≤ m → 0 ≤ f m)
    (hBase : ∀ x, size x ≤ 1 → ((alg x).time : ℝ) ≤ B)
    (hStep : ∀ x, 2 ≤ size x → ∃ ys : List α, ys.length ≤ a ∧
      (∀ y ∈ ys, size y ≤ (size x + b - 1) / b) ∧
      ((alg x).time : ℝ) ≤ (ys.map fun y => ((alg y).time : ℝ)).sum + f (size x))
    (x : α) :
    ((alg x).time : ℝ) ≤ masterExpansion (a : ℝ) b B f (b ^ Nat.clog b (size x)) := by
  have haR : (1 : ℝ) ≤ a := Nat.one_le_cast.mpr ha
  have hmono := masterExpansion_mono haR hb hB hf_mono hf_nonneg
  suffices ∀ n (z : α), size z = n →
      ((alg z).time : ℝ) ≤ masterExpansion (a : ℝ) b B f (b ^ Nat.clog b n) from
    this (size x) x rfl
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro z hsz
    rcases lt_or_ge n 2 with hn2 | hn2
    · have hle1 : n ≤ 1 := by omega
      rw [Nat.clog_of_right_le_one hle1, pow_zero, masterExpansion_of_lt _ B f hb]
      exact hBase z (hsz ▸ hle1)
    · obtain ⟨ys, hlen, hys_sz, htime⟩ := hStep z (hsz ▸ hn2)
      rw [hsz] at hys_sz htime
      have hceil_lt : (n + b - 1) / b < n := Nat.add_pred_div_lt hb hn2
      set k := Nat.clog b ((n + b - 1) / b)
      have hclog_eq : Nat.clog b n = k + 1 := Nat.clog_of_two_le hb hn2
      have hE_nonneg : 0 ≤ masterExpansion (a : ℝ) b B f (b ^ k) :=
        masterExpansion_nonneg (zero_le_one.trans haR) hb hB hf_nonneg (b ^ k)
      have hys_bound : ∀ y ∈ ys,
          ((alg y).time : ℝ) ≤ masterExpansion (a : ℝ) b B f (b ^ k) := by
        intro y hy
        have hsy : size y ≤ (n + b - 1) / b := hys_sz y hy
        have hclog_y : Nat.clog b (size y) ≤ k := Nat.clog_mono_right b hsy
        exact (ih (size y) (hsy.trans_lt hceil_lt) y rfl).trans
          (hmono (Nat.pow_le_pow_right (by omega) hclog_y))
      have hsum_le : (ys.map fun y => ((alg y).time : ℝ)).sum ≤
          (a : ℝ) * masterExpansion (a : ℝ) b B f (b ^ k) := by
        calc
          (ys.map fun y => ((alg y).time : ℝ)).sum
            ≤ (ys.length : ℝ) * masterExpansion (a : ℝ) b B f (b ^ k) :=
              list_sum_map_le ys _ hys_bound
          _ ≤ (a : ℝ) * masterExpansion (a : ℝ) b B f (b ^ k) :=
              mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hlen) hE_nonneg
      have hf_le : f n ≤ f (b ^ (k + 1)) := by
        apply hf_mono
        rw [← hclog_eq]
        exact Nat.le_pow_clog hb n
      rw [hclog_eq, masterExpansion_pow_succ (a : ℝ) hb B f k]
      linarith

/-- **`TimeM` Master Theorem — Case 1 (Balanced / Ceiling Subproblems)**:
Direct leaf-dominated polynomial bound on `(alg x).time` for `1 ≤ size x`. -/
theorem time_le_master_case1 {α β : Type*} (alg : α → TimeM ℕ β) (size : α → ℕ)
    {a b : ℕ} {B C d : ℝ} (hb : 1 < b) (hd : 0 ≤ d) (hba : (b : ℝ) ^ d < a)
    (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hBase : ∀ x, size x ≤ 1 → ((alg x).time : ℝ) ≤ B)
    (hStep : ∀ x, 2 ≤ size x → ∃ ys : List α, ys.length ≤ a ∧
      (∀ y ∈ ys, size y ≤ (size x + b - 1) / b) ∧
      ((alg x).time : ℝ) ≤ (ys.map fun y => ((alg y).time : ℝ)).sum + C * (size x : ℝ) ^ d)
    {x : α} (hx : 1 ≤ size x) :
    ((alg x).time : ℝ) ≤
      (a : ℝ) * (B + C / ((a : ℝ) / (b : ℝ) ^ d - 1)) *
        (size x : ℝ) ^ Real.logb b a := by
  have hb1 : (1 : ℝ) < b := Nat.one_lt_cast.mpr hb
  have hb0 : (0 : ℝ) < b := zero_lt_one.trans hb1
  have hbd_ge1 : (1 : ℝ) ≤ (b : ℝ) ^ d := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hb1.le hd
  have haR : (1 : ℝ) < a := hbd_ge1.trans_lt hba
  have ha : 1 ≤ a := by exact_mod_cast haR.le
  let g : ℕ → ℝ := fun m => C * (m : ℝ) ^ d
  have hg_mono : Monotone g := fun u v huv =>
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg u) (Nat.cast_le.mpr huv) hd) hC
  have hg_nonneg : ∀ m, b ≤ m → 0 ≤ g m := fun m _ =>
    mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg m) d)
  have hexp := time_le_masterExpansion_ceil alg size ha hb hB hg_mono hg_nonneg hBase hStep x
  set N := b ^ Nat.clog b (size x)
  have hN1 : 1 ≤ N := Nat.one_le_pow _ _ (by omega)
  have hN_bound := masterExpansion_le_case1 hb hd hba hB hC (fun _ _ => le_rfl) hN1
  have hN_le : (N : ℝ) ≤ (b : ℝ) * (size x : ℝ) := by exact_mod_cast pow_clog_le_mul hb hx
  have hp_nonneg : 0 ≤ Real.logb b a := Real.logb_nonneg hb1 haR.le
  have hrpow_le : (N : ℝ) ^ Real.logb b a ≤ (a : ℝ) * (size x : ℝ) ^ Real.logb b a := by
    calc
      (N : ℝ) ^ Real.logb b a ≤ ((b : ℝ) * (size x : ℝ)) ^ Real.logb b a :=
        Real.rpow_le_rpow (Nat.cast_nonneg N) hN_le hp_nonneg
      _ = (b : ℝ) ^ Real.logb b a * (size x : ℝ) ^ Real.logb b a :=
        Real.mul_rpow hb0.le (Nat.cast_nonneg _)
      _ = (a : ℝ) * (size x : ℝ) ^ Real.logb b a := by
        rw [Real.rpow_logb hb0 hb1.ne' (zero_lt_one.trans haR)]
  have hconst_nonneg : 0 ≤ B + C / ((a : ℝ) / (b : ℝ) ^ d - 1) :=
    add_nonneg hB (div_nonneg hC (sub_nonneg.mpr ((one_lt_div (by positivity)).mpr hba).le))
  calc
    ((alg x).time : ℝ) ≤ (B + C / ((a : ℝ) / (b : ℝ) ^ d - 1)) * (N : ℝ) ^ Real.logb b a :=
      hexp.trans hN_bound
    _ ≤ (B + C / ((a : ℝ) / (b : ℝ) ^ d - 1)) * ((a : ℝ) * (size x : ℝ) ^ Real.logb b a) :=
      mul_le_mul_of_nonneg_left hrpow_le hconst_nonneg
    _ = (a : ℝ) * (B + C / ((a : ℝ) / (b : ℝ) ^ d - 1)) * (size x : ℝ) ^ Real.logb b a := by
      ring

/-- **`TimeM` Master Theorem — Case 2 (Balanced / Ceiling Subproblems)**:
Direct critical-regime bound on `(alg x).time` for `1 ≤ size x`. -/
theorem time_le_master_case2 {α β : Type*} (alg : α → TimeM ℕ β) (size : α → ℕ)
    {a b : ℕ} {B C : ℝ} (ha : 1 ≤ a) (hb : 1 < b) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hBase : ∀ x, size x ≤ 1 → ((alg x).time : ℝ) ≤ B)
    (hStep : ∀ x, 2 ≤ size x → ∃ ys : List α, ys.length ≤ a ∧
      (∀ y ∈ ys, size y ≤ (size x + b - 1) / b) ∧
      ((alg x).time : ℝ) ≤
        (ys.map fun y => ((alg y).time : ℝ)).sum + C * (size x : ℝ) ^ Real.logb b a)
    {x : α} (hx : 1 ≤ size x) :
    ((alg x).time : ℝ) ≤
      (a : ℝ) * (B + C * (Real.logb b (size x) + 1)) * (size x : ℝ) ^ Real.logb b a := by
  have hb1 : (1 : ℝ) < b := Nat.one_lt_cast.mpr hb
  have hb0 : (0 : ℝ) < b := zero_lt_one.trans hb1
  have haR : (1 : ℝ) ≤ a := Nat.one_le_cast.mpr ha
  have ha0 : (0 : ℝ) < a := zero_lt_one.trans_le haR
  set p := Real.logb b a
  have hp_nonneg : 0 ≤ p := Real.logb_nonneg hb1 haR
  let g : ℕ → ℝ := fun m => C * (m : ℝ) ^ p
  have hg_mono : Monotone g := fun u v huv =>
    mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg u) (Nat.cast_le.mpr huv) hp_nonneg) hC
  have hg_nonneg : ∀ m, b ≤ m → 0 ≤ g m := fun m _ =>
    mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg m) p)
  have hexp := time_le_masterExpansion_ceil alg size ha hb hB hg_mono hg_nonneg hBase hStep x
  set N := b ^ Nat.clog b (size x)
  have hN1 : 1 ≤ N := Nat.one_le_pow _ _ (by omega)
  have hN_bound := masterExpansion_le_case2 haR hb hB hC (fun _ _ => le_rfl) hN1
  have hN_le : (N : ℝ) ≤ (b : ℝ) * (size x : ℝ) := by exact_mod_cast pow_clog_le_mul hb hx
  have hN_pos : (0 : ℝ) < N := by positivity
  have hsx_pos : (0 : ℝ) < size x := by positivity
  have hlogN_le : Real.logb b N ≤ Real.logb b (size x) + 1 := by
    calc
      Real.logb b N ≤ Real.logb b ((b : ℝ) * (size x : ℝ)) :=
        Real.logb_le_logb_of_le hb1 hN_pos hN_le
      _ = Real.logb b b + Real.logb b (size x) := Real.logb_mul hb0.ne' hsx_pos.ne'
      _ = Real.logb b (size x) + 1 := by rw [Real.logb_self_eq_one hb1, add_comm]
  have hrpow_le : (N : ℝ) ^ p ≤ (a : ℝ) * (size x : ℝ) ^ p := by
    calc
      (N : ℝ) ^ p ≤ ((b : ℝ) * (size x : ℝ)) ^ p := Real.rpow_le_rpow hN_pos.le hN_le hp_nonneg
      _ = (b : ℝ) ^ p * (size x : ℝ) ^ p := Real.mul_rpow hb0.le hsx_pos.le
      _ = (a : ℝ) * (size x : ℝ) ^ p := by rw [Real.rpow_logb hb0 hb1.ne' ha0]
  have hlogsx_nonneg : 0 ≤ Real.logb b (size x) := Real.logb_nonneg hb1 (by exact_mod_cast hx)
  calc
    ((alg x).time : ℝ) ≤ (B + C * Real.logb b N) * (N : ℝ) ^ p := hexp.trans hN_bound
    _ ≤ (B + C * (Real.logb b (size x) + 1)) * ((a : ℝ) * (size x : ℝ) ^ p) := by
      refine mul_le_mul ?_ hrpow_le (Real.rpow_nonneg hN_pos.le p) ?_
      · gcongr
      · positivity
    _ = (a : ℝ) * (B + C * (Real.logb b (size x) + 1)) * (size x : ℝ) ^ p := by ring

/-- **`TimeM` Master Theorem — Case 3 Polynomial Form (Balanced / Ceiling Subproblems)**:
Direct root-dominated polynomial bound on `(alg x).time` for `1 ≤ size x`. -/
theorem time_le_master_case3 {α β : Type*} (alg : α → TimeM ℕ β) (size : α → ℕ)
    {a b : ℕ} {B C d : ℝ} (ha : 1 ≤ a) (hb : 1 < b) (hd : 0 ≤ d) (hab : (a : ℝ) < (b : ℝ) ^ d)
    (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hBase : ∀ x, size x ≤ 1 → ((alg x).time : ℝ) ≤ B)
    (hStep : ∀ x, 2 ≤ size x → ∃ ys : List α, ys.length ≤ a ∧
      (∀ y ∈ ys, size y ≤ (size x + b - 1) / b) ∧
      ((alg x).time : ℝ) ≤ (ys.map fun y => ((alg y).time : ℝ)).sum + C * (size x : ℝ) ^ d)
    {x : α} (hx : 1 ≤ size x) :
    ((alg x).time : ℝ) ≤
      (b : ℝ) ^ d * (B + C / (1 - (a : ℝ) / (b : ℝ) ^ d)) * (size x : ℝ) ^ d := by
  have hb0 : (0 : ℝ) < b := by positivity
  have hbd_pos : 0 < (b : ℝ) ^ d := Real.rpow_pos_of_pos hb0 d
  let g : ℕ → ℝ := fun m => C * (m : ℝ) ^ d
  have hg_mono : Monotone g := fun u v huv =>
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg u) (Nat.cast_le.mpr huv) hd) hC
  have hg_nonneg : ∀ m, b ≤ m → 0 ≤ g m := fun m _ =>
    mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg m) d)
  have hexp := time_le_masterExpansion_ceil alg size ha hb hB hg_mono hg_nonneg hBase hStep x
  set N := b ^ Nat.clog b (size x)
  have hN1 : 1 ≤ N := Nat.one_le_pow _ _ (by omega)
  have hN_bound := masterExpansion_le_case3_poly (Nat.cast_nonneg a) hb hd hab hB hC
    (fun _ _ => le_rfl) hN1
  have hN_le : (N : ℝ) ≤ (b : ℝ) * (size x : ℝ) := by exact_mod_cast pow_clog_le_mul hb hx
  have hrpow_le : (N : ℝ) ^ d ≤ (b : ℝ) ^ d * (size x : ℝ) ^ d := by
    calc
      (N : ℝ) ^ d ≤ ((b : ℝ) * (size x : ℝ)) ^ d := Real.rpow_le_rpow (Nat.cast_nonneg N) hN_le hd
      _ = (b : ℝ) ^ d * (size x : ℝ) ^ d := Real.mul_rpow hb0.le (Nat.cast_nonneg _)
  have hr1 : (a : ℝ) / (b : ℝ) ^ d < 1 := (div_lt_one hbd_pos).mpr hab
  have hconst_nonneg : 0 ≤ B + C / (1 - (a : ℝ) / (b : ℝ) ^ d) :=
    add_nonneg hB (div_nonneg hC (sub_nonneg.mpr hr1.le))
  calc
    ((alg x).time : ℝ) ≤ (B + C / (1 - (a : ℝ) / (b : ℝ) ^ d)) * (N : ℝ) ^ d := hexp.trans hN_bound
    _ ≤ (B + C / (1 - (a : ℝ) / (b : ℝ) ^ d)) * ((b : ℝ) ^ d * (size x : ℝ) ^ d) :=
      mul_le_mul_of_nonneg_left hrpow_le hconst_nonneg
    _ = (b : ℝ) ^ d * (B + C / (1 - (a : ℝ) / (b : ℝ) ^ d)) * (size x : ℝ) ^ d := by ring

end TimeM

end Cslib.Algorithms.Lean
