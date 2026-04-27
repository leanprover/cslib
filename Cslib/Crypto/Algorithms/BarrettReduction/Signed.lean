/-
Copyright (c) 2026 Alix Trieu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alix Trieu
-/

module

public import Cslib.Init
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Rat.Floor
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Algebra.Order.Round
import Mathlib.Tactic
public import Cslib.Crypto.Algorithms.BarrettReduction.Aux

/-
# Signed Barrett Reduction

This file formalizes signed variant of the Barrett reduction algorithm used in many
schemes such as ML-DSA or ML-KEM.

This formalization is inspired by Section 2.4 of the following paper
Efficient Multiplication of Somewhat Small Integers Using Number-Theoretic Transforms
Hanno Becker, Vincent Hwang, Matthias J. Kannwischer, Lorenz Panny, and Bo-Yin Yang
IWSEC 2022

The main theorem is `barrett_reduce_spec`.

See example at the end of file for how to use it.
-/

namespace Cslib.Crypto.Algorithms.BarrettReduction.Signed

notation "⌊" x "⌉" => round (x : ℚ)

def is_approx (δ : ℚ) (α : ℚ → ℤ) : Prop :=
  ∀ (x: ℚ), |(x - α x)| ≤ δ

lemma round_is_approx : is_approx (1/2) round := by
  intro x; apply abs_sub_round

def round_to_even (x : ℚ) : ℤ :=
  2 * ⌊(x / 2)⌉

def mod_approx (α : ℚ → ℤ) (x : ℤ) (N : ℕ) : ℤ := x - ↑N * (α (x/N))

public def smod (x : ℤ) (N : ℕ) : ℤ := mod_approx round x N

notation x "mod±" N => smod x N

lemma smod_is_bmod (x : ℤ) (N : ℕ) :
  (x mod± N) = (x.bmod N) := by
  rw [Int.bmod_eq_self_sub_mul_bdiv, smod, mod_approx]
  rw [Int.bdiv]; split_ifs with HN
  · rw [HN]; simp
  · simp only [mul_ite, sub_right_inj]
    rw [round_eq, show (↑x / ↑N + 1 / (2:ℚ)) = (↑(2 * x + N) / ↑(2 * N)) by
        rw [← Rat.mkRat_eq_div, ← Rat.mkRat_eq_div]
        rw [show (1/2:ℚ) = mkRat 1 2 by cbv]
        rw [Rat.mkRat_add_mkRat] <;> try omega
        rw [Rat.mkRat_eq_iff] <;> try omega
        simp; linarith]
    rw [Rat.floor_intCast_div_natCast]; simp only [Nat.cast_mul, Nat.cast_ofNat]
    have X: x % N < (N + 1) / 2 ↔ 2 * (x % N) < N := by omega
    rw [show ((2 * x + ↑N) / (2 * ↑N)) = if x % ↑N < (↑N + 1) / 2 then (x / ↑N) else (x / ↑N + 1) by
          refine ((@Int.ediv_emod_unique (2 * x + ↑N) (2 * ↑N)
            (if x % ↑N < (↑N + 1) / 2 then 2 * (x % ↑N) + ↑N else 2 * (x % ↑N) - ↑N)
            (if x % ↑N < (↑N + 1) / 2 then x / ↑N else x / ↑N + 1) (by omega)).mpr ?_).left
          apply And.intro
          · split_ifs with A <;> nth_rw 3 [← Int.mul_ediv_add_emod x N] <;> linarith
          · apply And.intro
            · have Y := @Int.emod_nonneg x N (by omega)
              split_ifs with A
              · linarith
              · rw [X] at A; linarith
            · split_ifs with A <;> rw [X] at A
              · linarith
              · have Y := @Int.emod_lt_of_pos x N (by omega)
                linarith]
    split <;> simp

def barrett_mul (R : ℕ) (a b : ℤ) (q : ℕ) : ℤ :=
  a * b - q * ⌊((a * ⌊((b * R) / q)⌉) / R)⌉

-- This is Fact 2 of cited paper above.
-- M is the bitwidth of the considered integer type, e.g., 16, 32, 64, etc.
lemma barrett_mul_spec (a b : ℤ) (M R k q : ℕ)
  (H1_le_k : 1 ≤ k)
  (Hk : |((b * R) / (q : ℚ)) - ⌊((b * R) / q)⌉| ≤ (1 / (2 ^ k)))
  (HOddq : Odd q) (HR : R = 2 ^ (M - 1 + q.log2 - |b|.toNat.clog2))
  (HM : 2 ≤ M)
  (Hb : |b| ≤ 2 ^ (M - 2))
  (Ha' : |a| ≤ 2 ^ ((M - 2) - |b|.toNat.clog2 + (k - 1))) :
  barrett_mul R a b q = (a * b).bmod q := by
  have Hqpos: q > 0 := by exact Odd.pos HOddq
  have HRpos: R > 0 := by subst R; exact Nat.two_pow_pos _
  rw [← smod_is_bmod, barrett_mul, smod, mod_approx]
  simp only [Int.cast_mul, sub_right_inj, mul_eq_mul_left_iff, Int.natCast_eq_zero]; left
  let δ := a * (round ((b * R) / (q: ℚ))) / (R: ℚ) - ((a * b) / q)
  rw [show ↑a * ↑(round (↑b * ↑R / (q:ℚ))) / (R: ℚ) = ((a * b) / q) + δ by simp [δ]]
  cases eq_or_ne ⌊(a * b) / q⌉ ⌊(a * b) / q + δ⌉ with
  | inl _ => omega
  | inr Hne =>
    exfalso
    have Hδ₀: |δ| ≤ ↑|a| / (2^k * ↑R) := by
      rw [show δ = (a / R) * (round ((b * R) / (q: ℚ)) - (b * R) / (q: ℚ)) by
        unfold δ; qify at Hqpos; qify at HRpos
        rw [mul_sub, ← mul_div_right_comm, ← mul_div_mul_comm]
        rw [← mul_assoc, mul_comm (R: ℚ) q, mul_div_mul_right]; linarith]
      rw [abs_mul, abs_sub_comm, abs_div, @abs_of_nonneg _ _ _ (↑R:ℚ) _ (Nat.cast_nonneg' R)]
      rw [show ↑|a| / (2^k * ↑R) = |↑a| / (↑R:ℚ) * (1 / 2^k) by
            rw [div_mul_div_comm, mul_comm]; simp]
      apply mul_le_mul_of_nonneg_left
      · apply Hk
      · apply div_nonneg <;> simp
    have Hδ₁: 1 / (2*q: ℚ) ≤ |δ| := by
      cases lt_or_gt_of_ne Hne with
      | inl Hlt =>
        rw [round_lt_iff] at Hlt
        let ⟨n, Ha, Hb⟩ := Hlt
        have Hδ₀: 0 < (↑n:ℚ) + 1 / 2 - ↑(a* b) / ↑q ∧ ↑n + 1 / 2 - ↑(a * b) / ↑q ≤ δ := by
          apply And.intro <;> qify <;> linarith
        rw [← div_one (↑n:ℚ), div_add_div, div_sub_div] at Hδ₀ <;>
          [skip ; simp; (qify at Hqpos; linarith); simp ; simp]
        simp only [mul_one, one_mul, Int.cast_mul] at Hδ₀
        let ⟨Hδ₁, Hδ₂⟩ := Hδ₀
        rw [div_pos_iff_of_pos_right] at Hδ₁ <;> [skip; (qify at Hqpos; linarith only [Hqpos])]
        have H: 1 ≤ (n * 2 + 1) * q - 2 * (a * b) := by
          suffices 0 < (n * 2 + 1) * q - 2 * (a * b) by linarith
          qify; linarith
        transitivity δ <;> [skip; apply le_abs_self]
        transitivity ((↑n * 2 + 1) * ↑q - 2 * (a * b)) / (2 * ↑q) <;> [skip; assumption]
        refine (div_le_div_iff_of_pos_right ?_).mpr ?_ <;> (qify at Hqpos; qify at H; linarith)
      | inr Hgt =>
        rw [round_lt_iff] at Hgt
        let ⟨n, Ha, Hb⟩ := Hgt
        have Hδ₀: δ < (↑n:ℚ) + 1 / 2 - ↑(a * b) / ↑q ∧ ↑n + 1 / 2 - ↑(a * b) / ↑q ≤ (0:ℚ) := by
          apply And.intro <;> qify <;> linarith
        rw [← div_one (↑n:ℚ), div_add_div, div_sub_div] at Hδ₀ <;>
          [skip ; simp; (qify at Hqpos; linarith); simp ; simp]
        simp only [mul_one, one_mul, Int.cast_mul] at Hδ₀
        let ⟨Hδ₁, Hδ₂⟩ := Hδ₀
        have X: δ < 0 := by apply lt_of_lt_of_le <;> assumption
        apply neg_lt_neg at Hδ₁
        apply neg_le_neg at Hδ₂
        rw [← abs_of_neg X, ← neg_div] at Hδ₁
        rw [← neg_div] at Hδ₂
        simp only [neg_sub] at Hδ₁; simp only [neg_zero, neg_sub] at Hδ₂
        rw [div_nonneg_iff] at Hδ₂
        cases Hδ₂ with
        | inl H =>
          let ⟨H₀, _⟩ := H
          have H₁: 0 ≤ 2 * (a * b) - (n * 2 + 1) * q := by qify; linarith
          have H₂: 0 = 2 * (a * b) - (n * 2 + 1) * q ∨ 1 ≤ 2 * (a * b) - (n * 2 + 1) * q := by omega
          cases H₂ with
          | inl Hz =>
            symm at Hz; rw [Int.sub_eq_zero] at Hz
            have Heven: Even (2 * (a * b)) := by exact even_two_mul (a * b)
            have Hodd: Odd (2 * (a * b)) := by
              rw [Hz]; apply Odd.mul
              · rw [Odd]; use n; linarith
              · simp only [Int.odd_coe_nat]; assumption
            exfalso; apply (@Int.not_odd_iff_even (2 * (a * b))).mpr <;> assumption
          | inr Hle =>
            apply le_of_lt; apply lt_of_le_of_lt _ Hδ₁
            refine (div_le_div_iff_of_pos_right ?_).mpr ?_ <;> (qify at Hqpos; qify at Hle;linarith)
        | inr H =>
          let ⟨_, H'⟩ := H
          qify at Hqpos; linarith
    suffices X: ↑|a| / (2 ^ k * ↑R) < 1 / (2 * (q: ℚ)) by linarith
    rw [div_lt_div_iff₀] <;> [simp only [Int.cast_abs, one_mul];
                              (qify at HRpos; rw [mul_pos_iff]; left; apply And.intro
                               · exact pow_pos rfl k
                               · linarith); (qify at Hqpos; linarith)]
    rw [HR]
    cases eq_or_ne |↑a| (0: ℚ) with
    | inl Heq =>
      rw [Heq]; simp
    | inr Hne =>
      simp only [Nat.cast_pow, Nat.cast_ofNat]; rw [← pow_add]
      apply lt_of_le_of_lt
      · qify at Ha'
        apply (Rat.mul_le_mul_of_nonneg_right Ha' ( by qify at Hqpos; linarith))
      · nth_rw 4 [← pow_one 2]
        rw [← mul_assoc, ← pow_add]
        apply lt_of_lt_of_le
        · have X: q < 2 ^ (q.log2 + 1) := by rw [← Nat.log2_lt] <;> linarith
          qify at X; apply (Rat.mul_lt_mul_of_pos_left X)
          apply pow_pos; rfl
        · rw [← pow_add]
          apply pow_le_pow_right₀
          · simp
          · have X: |b|.toNat.clog2 ≤ M - 2 := by
              rw [← Nat.le_pow_iff_clog2_le]; zify
              rw [Int.toNat_of_nonneg]
              · omega
              · apply abs_nonneg
            ring_nf; omega

public def barrett_reduce (R : ℕ) (a : ℤ) (q : ℕ) : ℤ :=
  a - q * ⌊((a * ⌊(R / q)⌉) / R)⌉

public theorem barrett_reduce_spec (a : ℤ) (M R k q : ℕ)
  (H1_le_k : 1 ≤ k)
  (Hk : |(R / (q : ℚ)) - ⌊(R / q)⌉| ≤ (1 / (2 ^ k)))
  (HOddq : Odd q) (HR : R = 2 ^ (M - 1 + q.log2))
  (HM : 2 ≤ M)
  (Ha' : |a| ≤ 2 ^ ((M - 2) + (k - 1))) :
  barrett_reduce R a q = a.bmod q := by
  nth_rw 2 [← mul_one a]
  rw [← barrett_mul_spec a 1 M R k q] <;> try assumption
  · rw [barrett_reduce, barrett_mul]
    rw [mul_one]; simp
  · simp only [Int.cast_one, one_mul, one_div]; simp at Hk; assumption
  · simp only [abs_one]; refine one_le_pow₀ (by simp)

end Cslib.Crypto.Algorithms.BarrettReduction.Signed

section MLKEMExample
open Cslib.Crypto.Algorithms.BarrettReduction.Signed

/-
Proof of correctness for the signed Barrett reduction
used in the reference implementation of Kyber/MLKEM
https://github.com/pq-crystals/kyber/blob/main/ref/reduce.c#L25-L42
-/

def M : ℕ := 16    -- 16 bits
def q : ℕ := 3329  -- prime modulus used for MLKEM
def R : ℕ := 2 ^ 26
def k : ℕ := 2

-- This follows closely the original C code, though in ℤ
def mlkem_barrett_reduce (a : ℤ) : ℤ :=
  let v := 20159
  let t := (v * a + (1 <<< 25)) >>> (26: ℕ)
  let t := t * 3329
  a - t

lemma mlkem_barrett_reduce_correct (a : ℤ) (Ha : |a| ≤ 2 ^ 15) :
  mlkem_barrett_reduce a = a.bmod q := by
  rw [← barrett_reduce_spec a M R k q]
  · rw [mlkem_barrett_reduce, barrett_reduce, R, q]; simp only [Nat.cast_ofNat,
    Nat.reduceShiftLeft, Nat.reducePow, sub_right_inj]
    rw [show (round (67108864 / (3329:ℚ))) = 20159 by decide +kernel]
    rw [Int.shiftRight_eq_div_pow, round_eq]
    rw [div_add_div] <;> try decide
    simp only [Nat.reducePow, Nat.cast_ofNat, Int.cast_ofNat, mul_one]
    rw [show ↑a * 20159 * 2 + 67108864 = (20159 * a + 33554432) * (2:ℚ) by linarith]
    rw [mul_div_mul_right _ _ (by simp)]
    rw [show 20159 * ↑a + (33554432:ℚ) = ↑(20159 * a + (33554432:ℤ)) by simp]
    rw [show (67108864:ℚ) = ↑(67108864:ℕ) by simp]
    rw [Rat.floor_intCast_div_natCast]; simp; omega
  · simp [k]
  · decide +kernel
  · use (q/2); decide
  · decide
  · decide
  · transitivity
    · apply Ha
    · decide

-- This is basically the C code translated manually into Lean
def mlkem_barrett_reduce_impl (a : Int16) : Int16 :=
  let v: Int16 := 20159
  let t: Int32 := (v.toInt32 * a.toInt32 + ((1: Int32) <<< 25)) >>> 26
  let t: Int16 := t.toInt16 * 3329
  a - t

lemma mlkem_barrett_reduce_impl_correct (a : Int16) :
  Int16.toInt (mlkem_barrett_reduce_impl a) = (Int16.toInt a).bmod q := by
  rw [← mlkem_barrett_reduce_correct]
  · rw [mlkem_barrett_reduce, mlkem_barrett_reduce_impl]
    rw [Int16.toInt_sub, Int16.toInt_mul]
    simp only [Nat.reduceLeDiff, Int16.toInt32_ofNat, Int32.toInt_toInt16, Nat.reducePow,
      Int16.reduceToInt, Int.bmod_mul_bmod, Int.sub_bmod_bmod, Nat.cast_ofNat, Nat.reduceShiftLeft]
    rw [show ((1:Int32) <<< 25 = 33554432) by decide]
    rw [← Int32.toInt_toBitVec, Int32.toBitVec_shiftRight]
    simp only [Int32.toBitVec_add, Int32.toBitVec_mul, Int32.toBitVec_ofNat, BitVec.ofNat_eq_ofNat,
      Int16.toBitVec_toInt32, BitVec.reduceSMod, BitVec.sshiftRight_eq', BitVec.toNat_ofNat,
      Nat.reducePow, Nat.reduceMod, BitVec.toInt_sshiftRight, BitVec.toInt_add, BitVec.toInt_mul,
      BitVec.reduceToInt, Int.bmod_add_bmod]
    rw [BitVec.toInt_signExtend_of_le] <;> [skip;simp]
    rw [Int16.toInt_toBitVec]
    have Hle := Int16.le_toInt a
    have Hlt := Int16.toInt_lt a
    rw [@Int.bmod_eq_of_le _ 4294967296] <;> [skip; (simp; omega); (simp; omega)]
    rw [show (a.toInt - (20159 * a.toInt + 33554432) >>> 26 * 3329 = mlkem_barrett_reduce a.toInt)
      by rw [mlkem_barrett_reduce]; simp]
    rw [mlkem_barrett_reduce_correct, q]
    · rw [Int.bmod_bmod_eq_of_lt] <;> omega
    · rw [abs_le]; omega
  · rw [abs_le']; split_ands
    · apply Int.le_of_lt
      apply Int16.toInt_lt
    · apply Int.neg_le_of_neg_le
      apply Int16.le_toInt

end MLKEMExample
