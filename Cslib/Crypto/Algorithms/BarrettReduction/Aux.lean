/-
Copyright (c) 2026 Alix Trieu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alix Trieu
-/

module

public import Cslib.Init
public import Mathlib.Data.Nat.Log
public import Mathlib.Algebra.Order.Round
public import Mathlib.Data.Rat.Floor
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Data.Int.DivMod
import Mathlib.Tactic

/-!
# Auxiliary definitions and lemmas

- Defines `clog2`, a base 2 upper logarithm and some associated lemmas
- Additional facts about `bmod`, `floor` and `round`
-/

@[expose]
public section

namespace Nat

abbrev clog2 : ℕ → ℕ := Nat.clog 2

lemma le_clog2_self (n : ℕ) :
    n ≤ 2 ^ (n.clog2) := by
  apply le_pow_clog (by simp) n

lemma log2_le_clog2 (n : ℕ) :
    n.log2 ≤ n.clog2 := by
  rw [log2_eq_log_two]
  apply Nat.log_le_clog 2 n

lemma le_pow_iff_clog2_le {x y : ℕ} :
    x ≤ 2 ^ y ↔ clog2 x ≤ y :=
  by symm; apply Nat.clog_le_iff_le_pow; simp

lemma clog2_le_log2 (n : ℕ) :
    n.clog2 ≤ n.log2 + 1 := by
  rw [log2_eq_log_two]
  rw [← le_pow_iff_clog2_le]
  apply le_of_lt
  cases n with
  | zero => simp
  | succ n =>
    rw [← log2_eq_log_two, ← Nat.log2_lt (by simp)]
    simp

lemma clog2_eq (n : ℕ) :
    n.clog2 = if 2 ^ n.log2 < n then n.log2 + 1 else n.log2 := by
  have H₀ := clog2_le_log2 n
  have H₁ := log2_le_clog2 n
  split_ifs with Hcond <;> rw [← Nat.lt_clog_iff_pow_lt (by simp), ← clog2] at Hcond <;> linarith

end Nat

namespace Int

lemma abs_bmod_le (x : ℤ) (m : ℕ) (Hm : 0 < m) :
    |x.bmod m| ≤ m / 2 := by
  rw [abs_le]; apply And.intro
  · apply Int.le_bmod Hm
  · transitivity
    · apply Int.bmod_le Hm
    · omega

lemma bmod_eq' (x : ℤ) (m : ℕ) :
    x.bmod m = x - m * (round (x / (m: ℚ))) := by
  rw [round_eq, Int.bmod]
  have X: x % m < (m + 1) / 2 ↔ 2 * (x % m) < m := by omega
  cases Nat.eq_zero_or_pos m with
  | inl Hz => rw [Hz]; simp
  | inr Hpos =>
    rw [div_add_div] <;>
      simp only [mul_one, Nat.cast_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true] <;>
      try linarith
    split_ifs with Hcond <;> rw [X] at Hcond
    · rw [Int.emod_def]; simp only [sub_right_inj, _root_.mul_eq_mul_left_iff, natCast_eq_zero]
      left; rw [show m * (2:ℚ) = ↑(2 * m) by simp; linarith]
      rw [show x * 2 + (m:ℚ) = ↑(2 * x + m) by simp; linarith]
      rw [Rat.floor_intCast_div_natCast]; symm
      apply ((@Int.ediv_emod_unique _ _ (2 * (x % m) + m) _ (by omega)).mpr ?_).left
      apply And.intro
      · nth_rw 3 [← Int.mul_ediv_add_emod x m]; simp
        linarith
      · have X := @Int.emod_nonneg x m (by omega)
        simp only [Nat.cast_mul, Nat.cast_ofNat]; apply And.intro <;> linarith
    · rw [show m * (2:ℚ) = ↑(2 * m) by simp; linarith]
      rw [show x * 2 + (m:ℚ) = ↑(2 * x + m) by simp; linarith]
      rw [Rat.floor_intCast_div_natCast]
      rw [Int.emod_def]; simp only [Nat.cast_mul, Nat.cast_ofNat]
      nth_rw 3 [← mul_one m]
      rw [Int.sub_sub, Nat.cast_mul, ← mul_add]; simp only [Nat.cast_one, sub_right_inj,
        _root_.mul_eq_mul_left_iff, natCast_eq_zero]
      left; symm
      apply ((@Int.ediv_emod_unique _ _ (2 * (x % m) - m) _ (by omega)).mpr ?_).left
      apply And.intro
      · nth_rw 3 [← Int.mul_ediv_add_emod x m]
        linarith
      · have X := @Int.emod_lt_of_pos x m (by omega)
        simp only [Int.sub_nonneg]; apply And.intro <;> try linarith

lemma emod_def' (x : ℤ) (m : ℕ) :
    x % ↑m = if x.bmod m < 0 then m + x.bmod m else x.bmod m := by
  simp [Int.bmod_def]
  split_ifs <;> try omega
  · cases Nat.eq_zero_or_pos m with
    | inl Hz => rw [Hz]; simp
    | inr Hpos =>
      have X := @Int.emod_nonneg x m (by omega); linarith
  · cases Nat.eq_zero_or_pos m with
    | inl Hz => rw [Hz]; simp
    | inr Hpos =>
      have X := @Int.emod_lt_of_pos x m (by omega); linarith

lemma bmod_eq_of_abs_lt {n : ℤ} {m : ℕ} (hlt : |n| < m / 2) :
    n.bmod m = n := by
  rw [abs_lt] at hlt
  apply Int.bmod_eq_of_le <;> omega

lemma bmod_bmod_eq_of_le {x : ℤ} {m1 m2 : ℕ} (h : 0 < m1) (h' : m1 ≤ m2) :
    (x.bmod m1).bmod m2 = x.bmod m1 := by
  have X0 := @Int.le_bmod x m1 h
  have X1 := @Int.bmod_le x m1 h
  rw [@Int.bmod_eq_of_le _ m2] <;> omega

lemma bmod_bmod_eq_of_lt {x : ℤ} {m1 m2 : ℕ} (h : 0 < m1) (h' : m1 < m2) :
    (x.bmod m1).bmod m2 = x.bmod m1 := by
  rw [bmod_bmod_eq_of_le] <;> omega
end Int

end

@[expose]
public section

variable {α : Type*}
variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]

lemma floor_sub_abs (a b : α) :
    |⌊a⌋ - ⌊b⌋| ≤ ⌈|a - b|⌉ := by
  wlog Hab: a ≥ b
  · rw [abs_sub_comm ⌊a⌋, abs_sub_comm a]
    apply this; apply le_of_not_ge at Hab; assumption
  · rw [abs_of_nonneg, abs_of_nonneg] <;>
      [skip; linarith; (simp only [Int.sub_nonneg]; apply Int.floor_mono; assumption)]
    nth_rw 2 [← Int.fract_add_floor a]
    nth_rw 2 [← Int.fract_add_floor b]
    rw [show (Int.fract a + ↑⌊a⌋ - (Int.fract b + ↑⌊b⌋)=(Int.fract a - Int.fract b) + ↑(⌊a⌋ - ⌊b⌋))
      by rw [Int.cast_sub]; linarith]
    rw [Int.ceil_add_intCast]; simp only [le_add_iff_nonneg_left]
    rw [show (0 = -1 + 1) by omega]
    apply Int.add_one_le_of_lt
    rw [Int.lt_ceil]; simp
    have Ha₀: 0 ≤ Int.fract a := by apply Int.fract_nonneg
    have Hb₁: Int.fract b < 1 := by apply Int.fract_lt_one
    linarith

lemma floor_lt_iff (a b : α) :
    ⌊a⌋ < ⌊b⌋ ↔ ∃ (n: ℤ), a < ↑n ∧ ↑n ≤ b := by
  apply Iff.intro
  · intro H; cases lt_or_ge a ↑⌊b⌋ with
    | inl Hlt => use ↑⌊b⌋; apply And.intro
                 · assumption
                 · exact Int.floor_le b
    | inr Hge =>
      apply Int.le_floor.mpr at Hge; linarith
  · intro ⟨n, Ha, Hb⟩
    have H := Int.floor_le_floor Hb
    rw [Int.floor_intCast] at H
    apply @lt_of_lt_of_le _ _ _ n
    · exact Int.floor_lt.mpr Ha
    · assumption

lemma round_sub_abs (a b : α) :
    |round a - round b| ≤ ⌈|a - b|⌉ := by
  rw [round_eq, round_eq]
  rw [show (a - b = (a + 1/2) - (b + 1/2)) by linarith]
  apply floor_sub_abs

lemma round_lt_iff (a b : α) :
    round a < round b ↔ ∃ (n: ℤ), a < n + 1/2 ∧ n + 1/2 ≤ b := by
  apply Iff.intro
  · rw [round_eq, round_eq]; intro H
    rw [floor_lt_iff] at H
    let ⟨n, Ha, Hb⟩ := H
    use (n - 1); apply And.intro <;> (simp; linarith)
  · intro ⟨n, Ha, Hb⟩
    rw [round_eq, round_eq]
    rw [floor_lt_iff]
    use (n + 1); apply And.intro <;> (simp; linarith)

end
