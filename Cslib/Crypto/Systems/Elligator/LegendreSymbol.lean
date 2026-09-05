/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Cslib.Crypto.Systems.Elligator.FiniteFieldBasic

/-!
# Legendre Symbol

In this file we introduce a special case of the traditional Legendre Symbol.

The quadratic character `χ` used here is Mathlib's `quadraticChar`, whose values are cast from
`ℤ` into the finite field `F` itself; this is the form in which the Elligator 1 paper uses it.
All the facts below are consequences of the Mathlib API for `quadraticChar`, specialised to a
field `F` with `Fintype.card F = q` and `q % 4 = 3`.

## References

See [bernstein2013a], Section 3.1.
-/

@[expose] public section

namespace Cslib.Crypto.Systems.Elligator.LegendreSymbol

open Cslib.Crypto.Systems.Elligator.FiniteFieldBasic

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {q : ℕ}

/-- χ(a) is the quadratic character of a in the finite field F with q elements, where q is a
prime congruent to 3 modulo 4, viewed as an element of `F`.

This is Mathlib's `quadraticChar` composed with the cast `ℤ → F`, since
`Mathlib.NumberTheory.LegendreSymbol.Basics` is restricted to `ℤ`.
-/
def χ (a : F) : F := ((quadraticChar F a : ℤ) : F)

lemma χ_zero : χ (0 : F) = 0 := by simp [χ]

lemma χ_one : χ (1 : F) = 1 := by simp [χ]

/-- Euler's criterion: `χ` is given by the `(q - 1) / 2`-th power. -/
lemma χ_eq_pow (a : F) (hq_mod : Fintype.card F % 4 = 3) :
    χ a = a ^ ((Fintype.card F - 1) / 2) := by
  have h : (Fintype.card F - 1) / 2 = Fintype.card F / 2 := by
    omega
  rw [χ, h]
  exact quadraticChar_eq_pow_of_char_ne_two' (ringChar_ne_two hq_mod) a

lemma χ_values {a : F} : χ a = 0 ∨ χ a = -1 ∨ χ a = 1 := by
  rcases eq_or_ne a 0 with ha | ha
  · simp [χ_zero, ha]
  · rcases quadraticChar_dichotomy ha with h | h <;> simp [χ, h]

lemma χ_a_ne_zero {a : F} (a_ne_zero : a ≠ 0) : χ a ≠ 0 := by
  rcases quadraticChar_dichotomy a_ne_zero with h | h <;> simp [χ, h]

lemma a_eq_zero_of_χ_of_a_eq_zero {a : F} : χ a = 0 → a = 0 := by
  intro h
  by_contra ha
  apply χ_a_ne_zero ha
  exact h

@[simp]
lemma χ_a_eq_one {a : F} (a_ne_zero : a ≠ 0) (a_square : IsSquare a) : χ a = 1 := by
  rw [χ, (quadraticChar_one_iff_isSquare a_ne_zero).mpr a_square]
  simp

lemma χ_eq_one_iff_isSquare {a : F}
    (a_ne_zero : a ≠ 0) (hq_mod : Fintype.card F % 4 = 3) :
    χ a = 1 ↔ IsSquare a := by
  constructor
  · intro h
    rcases quadraticChar_dichotomy a_ne_zero with h' | h'
    · exact (quadraticChar_one_iff_isSquare a_ne_zero).mp h'
    · simp_all only [χ]
      have heq : (2 : F) = 0 := by grind
      have hne : (2 : F) ≠ 0 := by simp_all [FiniteFieldBasic.two_ne_zero]
      contradiction
  · exact χ_a_eq_one a_ne_zero

lemma χ_sq {a : F} (a_ne_zero : a ≠ 0) : χ (a ^ 2) = 1 := by
  rw [χ, quadraticChar_sq_one' a_ne_zero, Int.cast_one]

lemma χ_neg_one (hq_mod : Fintype.card F % 4 = 3) :
    χ (-1 : F) = -1 := by
  rw [χ, quadraticChar_neg_one_iff_not_isSquare.mpr (neg_one_non_square hq_mod)]
  simp

lemma χ_mul {a b : F} : χ (a * b) = (χ a) * (χ b) := by
  simp [χ, quadraticCharFun_mul]

lemma neg_χ_a_ne_χ_a {a : F}
    (a_ne_zero : a ≠ 0) (hq_mod : Fintype.card F % 4 = 3)
    : χ a ≠ -(χ a) := by
  intro h
  have heq : (2 : F) * χ a = 0 := by
    rw [← add_left_inj (χ a)] at h
    ring_nf at h
    rwa [mul_comm]
  rcases mul_eq_zero.mp heq with hzero | hzero
  · exact two_ne_zero hq_mod hzero
  · exact χ_a_ne_zero a_ne_zero hzero

@[simp]
lemma χ_of_a_even_pow_n_eq_one {a : F} (a_ne_zero : a ≠ 0) (n : {n : ℕ | Even n}) :
    (χ a) ^ (n.val) = 1 := by
  rcases χ_values (a := a) with h | h | h
  · exact absurd h (χ_a_ne_zero a_ne_zero)
  · rw [h]
    exact n.prop.neg_one_pow
  · rw [h, one_pow]

@[simp]
lemma χ_of_a_pow_n_eq_χ_a (a : F) (n : {n : ℕ | Odd n}) :
    (χ a) ^ (n.val) = χ a := by
  have hn := n.prop
  rcases χ_values (a := a) with h | h | h
  · rw [h, zero_pow hn.pos.ne']
  · rw [h]
    exact hn.neg_one_pow
  · rw [h, one_pow]

lemma χ_χ_eq_χ {a : F} (hq_mod : Fintype.card F % 4 = 3) :
    χ (χ a) = χ a := by
  rcases χ_values (a := a) with h | h | h
  · rw [h, χ_zero]
  · rw [h, χ_neg_one hq_mod]
  · rw [h, χ_one]

lemma χ_inv {a : F} : χ a = χ (1 / a) := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · have heq : χ (1 / a) * χ a = 1 := by
      rw [← χ_mul, one_div, inv_mul_cancel₀ ha, χ_one]
    rcases χ_values (a := a) with h | h | h
    · exact absurd h (χ_a_ne_zero ha)
    · rw [h] at heq ⊢
      grind
    · rw [h] at heq ⊢
      grind

lemma one_div_χ_of_a_eq_χ_a {a : F} : χ a = 1 / χ a := by
  rcases χ_values (a := a) with h | h | h <;> rw [h] <;> norm_num

/-- Multiplying by a nonzero square does not change the quadratic character.
Introduced in paper theory theorem 3.A proof. -/
lemma χ_of_a_eq_χ_a_mul_b_pow_two {a b : F} (b_ne_zero : b ≠ 0) :
    χ (a * b ^ 2) = χ a := by
  rw [χ_mul, χ_sq b_ne_zero, mul_one]

lemma a_pow_q_add_one_div_two_eq_χ_of_a_mul_a {a : F}
    (hq_mod : Fintype.card F % 4 = 3) :
    a ^ ((Fintype.card F + 1) / 2) = (χ a) * a := by
  rw [χ_eq_pow a hq_mod, ← pow_succ]
  congr 1
  omega

omit [DecidableEq F] in
lemma a_pow_q_add_one_div_two_eq_a {a : F}
    (a_square : IsSquare a) (hq_mod : Fintype.card F % 4 = 3) :
    a ^ ((Fintype.card F + 1) / 2) = a := by
  rcases eq_or_ne a 0 with rfl | ha
  · exact zero_pow (by omega)
  · classical
    rw [a_pow_q_add_one_div_two_eq_χ_of_a_mul_a hq_mod]
    rw [χ_a_eq_one ha a_square, one_mul]

lemma b_pow_q_add_one_div_four_eq_χ_of_a_mul_a {a : F}
    (hq_mod : Fintype.card F % 4 = 3) :
    (a ^ 2) ^ ((Fintype.card F + 1) / 4) = (χ a) * a := by
  rw [← pow_mul]
  have h : 2 * ((Fintype.card F + 1) / 4) = (Fintype.card F + 1) / 2 := by omega
  rw [h, a_pow_q_add_one_div_two_eq_χ_of_a_mul_a hq_mod]

lemma χ_a_mul_a_IsSquare {a : F}
    (a_ne_zero : a ≠ 0) (hq_mod : Fintype.card F % 4 = 3)
    : IsSquare ((χ a) * a) := by
  have h : (χ a) * a ≠ 0 := mul_ne_zero (χ_a_ne_zero a_ne_zero) a_ne_zero
  apply (χ_eq_one_iff_isSquare h hq_mod).mp
  rw [χ_mul, χ_χ_eq_χ hq_mod, ← pow_two]
  exact χ_of_a_even_pow_n_eq_one a_ne_zero ⟨2, even_two⟩

end Cslib.Crypto.Systems.Elligator.LegendreSymbol
