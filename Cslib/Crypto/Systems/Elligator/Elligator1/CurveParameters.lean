/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Cslib.Crypto.Systems.Elligator.Basic
public import Cslib.Crypto.Systems.Elligator.LegendreSymbol
public import Cslib.Crypto.Systems.Elligator.Context

/-!
# Curve Parameters

The parameters `c`, `r`, `d` derived from the Elligator 1 parameter `s`, together with the
nonvanishing and non-square facts about them needed throughout the rest of the development.

## Main Results

* `c`, `r`, `d`: the curve parameters of [bernstein2013a], Section 3.2, Theorem 1.
* `c_mul_sub_one_mul_add_one_ne_zero`: `c(c - 1)(c + 1) ≠ 0`.
* `r_ne_zero`, `four_add_r_ne_zero`, `r_sub_two_ne_zero`: `r`'s nonvanishing facts, used in
  the well-definedness of the auxiliary and output coordinates.
* `d_nonsquare`, `one_div_d_nonsquare`, `d_ne_zero_and_d_ne_one`: `d` is neither `0`, `1`, nor
  a square, the criterion making the resulting curve a valid complete Edwards curve.
* `neg_d_eq_r_add_two_div_r_sub_two`: relates `d` back to `r`, used in Theorem 3.

## References

See [bernstein2013a], Section 3.2, Theorem 1.
-/

@[expose] public section

namespace Cslib.Crypto.Systems.Elligator.Elligator1.CurveParameters

variable {F : Type*} [Field F]

open Cslib.Crypto.Systems.Elligator
open Cslib.Crypto.Systems.Elligator.FiniteFieldBasic
open Cslib.Crypto.Systems.Elligator.LegendreSymbol

variable (D : ParamData F)

section s

lemma s_pow_two_ne_two [IsRegularParam D.s] :
    D.s ^ 2 ≠ 2 :=
  sub_ne_zero.mp (left_ne_zero_of_mul s_sq_ne_pm_two)

lemma s_pow_two_ne_neg_two [IsRegularParam D.s] :
    D.s ^ 2 ≠ -2 := by
  have hright_ne_zero_of_mul : D.s^2 + 2 ≠ 0 := right_ne_zero_of_mul s_sq_ne_pm_two
  rwa [ne_eq, add_eq_zero_iff_eq_neg] at hright_ne_zero_of_mul

end s

section c

/-- c(s) is a function defined in the paper.

Original:, Section "3.2 The map": Theorem 1
-/
def c (s : F) : F := 2 / s ^ 2

def _root_.Cslib.Crypto.Systems.Elligator.ParamData.c (D : ParamData F) : F := CurveParameters.c D.s

lemma c_ne_zero [Fintype F] [IsNonzeroParam D.s] [IsCardThreeModFour F] :
    D.c ≠ 0 := by
  unfold ParamData.c c
  exact div_ne_zero (two_ne_zero card_mod_four) (pow_ne_zero 2 s_ne_zero)

lemma c_ne_one [IsRegularParam D.s] : D.c ≠ 1 := by
  unfold ParamData.c c
  exact div_ne_one_of_ne (s_pow_two_ne_two D).symm

lemma c_sub_one_ne_zero [IsRegularParam D.s] : D.c - 1 ≠ 0 :=
  sub_ne_zero.2 (c_ne_one D)

lemma c_ne_neg_one [IsRegularParam D.s] : (D.c) ≠ -1 := by
  unfold ParamData.c c
  intro h_contra
  have hs_sq_eq_neg_two : D.s ^ 2 = -2 := by grind
  have hs_sq_ne_neg_two := s_pow_two_ne_neg_two D
  contradiction

lemma c_add_one_ne_zero [IsRegularParam D.s] : D.c + 1 ≠ 0 := by
  intro h_contra
  have hc_ne_neg_one := c_ne_neg_one D
  rw [← add_left_inj (-1)] at h_contra
  ring_nf at h_contra
  contradiction

lemma c_mul_sub_one_mul_add_one_ne_zero [Fintype F]
    [IsNonzeroParam D.s] [IsRegularParam D.s] [IsCardThreeModFour F] :
    D.c * (D.c - 1) * (D.c + 1) ≠ 0 := by
  unfold ParamData.c c
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact c_ne_zero D
    · exact c_sub_one_ne_zero D
  · exact c_add_one_ne_zero D

lemma s_pow_two_eq_two_div_c [Fintype F] [IsCardThreeModFour F] : D.s ^ 2 = 2 / (D.c) := by
  unfold ParamData.c c
  field_simp [FiniteFieldBasic.two_ne_zero card_mod_four]

end c

variable [Fintype F]

section r

/-- r(s) is a function defined in the paper.

Original:, Section "3.2 The map": Theorem 1
-/
def r (s : F) : F :=
    let c := c s
    c + 1 / c

def _root_.Cslib.Crypto.Systems.Elligator.ParamData.r (D : ParamData F) : F := CurveParameters.r D.s

lemma r_ne_zero [IsNonzeroParam D.s] [IsCardThreeModFour F] :
    D.r ≠ 0 := by
  intro h_contra
  change D.c + 1 / D.c = 0 at h_contra
  have hcneg : D.c = -1 / D.c := by
    rw [← add_left_inj (1 / D.c)]
    rw [neg_div, neg_add_cancel (1 / D.c)]
    exact h_contra
  have hcpow : D.c ^ 2 = -1 := by
    calc
      D.c ^ 2 = -1 / D.c * D.c := by
        rw [← div_left_inj' (c_ne_zero D)]
        rw [pow_two, mul_div_assoc, div_self (c_ne_zero D), mul_one]
        rw [mul_div_assoc, div_self (c_ne_zero D), mul_one]
        exact hcneg
      _ = -1 := by
        nth_rw 1 [← neg_one_mul 1]
        ring_nf
        rw [mul_inv_cancel₀ (c_ne_zero D)]
  have hsq : IsSquare (-1 : F) := by
    rw [← hcpow, pow_two]
    exact IsSquare.mul_self D.c
  exact false_of_isSquare_neg_one card_mod_four hsq

lemma four_add_r_ne_zero [IsNonzeroParam D.s] [IsCardThreeModFour F] :
    4 + D.r ≠ 0 := by
  intro h_contra
  -- Step 1: clear `1/c` from `r`'s definition.
  have h_quad : (D.c) ^ 2 + 4 * (D.c) + 1 = 0 := by
    unfold ParamData.r r at h_contra
    change 4 + (D.c + 1 / D.c) = 0 at h_contra
    rw [← div_left_inj' (c_ne_zero D), zero_div]
    rw [← h_contra, add_div, add_div, pow_two, mul_div_assoc, mul_div_assoc]
    rw [div_self (c_ne_zero D), mul_one, mul_one]
    ring
  -- Step 2: substitute `c = 2/s²`, clear denominators - `(s²+4)² = 12`.
  let a : F := D.s ^ 2 + 4
  have ha_sq : a ^ 2 = 12 := by
    unfold a
    rw [← mul_left_inj' (pow_ne_zero 2 (s_ne_zero (s := D.s))), zero_mul] at h_quad
    change ((2 / D.s ^ 2) ^ 2 + 4 * (2 / D.s ^ 2) + 1) * D.s ^ 2 = 0 at h_quad
    rw [add_mul, add_mul] at h_quad
    rw [← mul_div_assoc, div_mul_comm, div_self (pow_ne_zero 2 s_ne_zero)] at h_quad
    field_simp [s_ne_zero] at h_quad
    linear_combination h_quad
  -- Step 3: halving, `u² = 3`.
  let u : F := a / 2
  have hu_sq : u ^ 2 = 3 := by
    unfold u
    rw [div_pow, ha_sq]
    rw [← mul_left_inj' (FiniteFieldBasic.four_ne_zero card_mod_four), div_mul]
    norm_num
    rw [div_self (FiniteFieldBasic.four_ne_zero card_mod_four), div_one]
  -- Step 4: `2u = a`, so `u² - 2u + 1 = 3 - a + 1 = -s²`, giving `((u-1)/s)² = -1`.
  have hu_eq_a : 2 * u = a := by
    unfold u
    rw [mul_div_left_comm]
    rw [div_self (FiniteFieldBasic.two_ne_zero card_mod_four), mul_one]
  have h_neg_one_sq : (-1 : F) = ((u - 1) / D.s) ^ 2 := by
    rw [div_pow, eq_div_iff (pow_ne_zero 2 s_ne_zero)]
    ring_nf
    rw [hu_sq]
    unfold u
    rw [div_mul, div_self (FiniteFieldBasic.two_ne_zero card_mod_four)]
    ring
  exact false_of_isSquare_neg_one card_mod_four ⟨_, h_neg_one_sq.trans (sq _)⟩

lemma r_sq_sub_two_eq_c_sq_add_inv_c_sq [IsNonzeroParam D.s] [IsCardThreeModFour F] :
    (D.r ^ 2 - 2) = D.c ^ 2 + 1 / D.c ^ 2 := by
  calc
    D.r ^ 2 - 2 = (D.c + 1 / D.c) ^ 2 - 2 := by rfl
    _ = D.c ^ 2 + 2 * (D.c * (1 / D.c)) + (1 / D.c) ^ 2 - 2 := by ring
    _ = D.c ^ 2 + 2 + 1 / D.c ^ 2 - 2 := by
      ring_nf
      rw [mul_inv_cancel₀ (c_ne_zero D)]
      ring
    _ = D.c ^ 2 + 1 / D.c ^ 2 := by ring

lemma r_sub_two_ne_zero [IsNonzeroParam D.s] [IsCardThreeModFour F] [IsRegularParam D.s] :
    D.r - 2 ≠ 0 := by
  have hc_ne_zero := c_ne_zero D
  change (D.c + 1 / D.c) - 2 ≠ 0
  have hceq : (D.c + 1 / D.c) - 2 = (D.c - 1) ^ 2 / D.c := by
    rw [← mul_left_inj' hc_ne_zero]
    rw [sub_mul, div_mul, div_self hc_ne_zero]
    ring_nf
    rw [mul_inv_cancel₀ hc_ne_zero]
    ring
  rw [hceq]
  have hdnez : (D.c - 1) ^ 2 ≠ 0 := pow_ne_zero 2 (c_sub_one_ne_zero D)
  exact div_ne_zero hdnez hc_ne_zero

end r

section d

/-- d(s) is a function defined in the paper.

Original:, Section "3.2 The map": Theorem 1
-/
def d (s : F) : F :=
    let c := c s;
    -(c + 1) ^ 2 / (c - 1) ^ 2

def _root_.Cslib.Crypto.Systems.Elligator.ParamData.d (D : ParamData F) : F := CurveParameters.d D.s

lemma d_nonsquare [IsRegularParam D.s] [IsCardThreeModFour F] : ¬IsSquare D.d := by
  rw [isSquare_iff_exists_mul_self D.d]
  change ¬∃ w, (-((2 / D.s ^ 2) + 1) ^ 2 / ((2 / D.s ^ 2) - 1) ^ 2) = w * w
  rintro ⟨w, Pw⟩
  have hdivd : (2 / D.s ^ 2 - 1) ^ 2 ≠ 0 := by grind [s_sq_ne_pm_two]
  have hdivs : (2 / D.s ^ 2 + 1) ^ 2 ≠ 0 := by grind [s_sq_ne_pm_two]
  have heq : w ^ 2 * ((2 / D.s ^ 2) - 1) ^ 2 / ((2 / D.s ^ 2) + 1) ^ 2 = -1 := by
    rw [pow_two, ← Pw]
    rw [mul_div_assoc, div_mul_div_comm]
    rw [mul_comm, ← div_mul_div_comm]
    rw [div_self hdivd, neg_eq_neg_one_mul, mul_div_assoc, div_self hdivs]
    ring
  have hsq : IsSquare (-1 : F) := by
    rw [← heq]
    have hw_sq : IsSquare (w ^ 2) := by
      rw [pow_two]
      exact IsSquare.mul_self w
    have hdiv_sq : IsSquare (((2 / D.s ^ 2) - 1) ^ 2 / ((2 / D.s ^ 2) + 1) ^ 2) := by
      apply IsSquare.div
      · rw [pow_two]
        exact IsSquare.mul_self (2 / D.s ^ 2 - 1)
      · rw [pow_two]
        exact IsSquare.mul_self (2 / D.s ^ 2 + 1)
    rw [mul_div_assoc]
    exact IsSquare.mul hw_sq hdiv_sq
  exact false_of_isSquare_neg_one card_mod_four hsq

lemma d_ne_zero [IsRegularParam D.s] [IsCardThreeModFour F] : D.d ≠ 0 := by
  have hd_nsq := d_nonsquare D
  intro hd_eq_zero
  have hd_sq : IsSquare D.d := by
    unfold IsSquare
    use 0
    rwa [mul_zero]
  contradiction

lemma one_div_d_nonsquare [IsRegularParam D.s] [IsCardThreeModFour F] : ¬IsSquare (1 / D.d) := by
  rintro ⟨a, ha⟩
  have hd_ne_zero := d_ne_zero D
  -- `1/d = a*a ≠ 0` (since `d ≠ 0`), so `a ≠ 0`.
  have ha_ne_zero : a ≠ 0 := by
    rintro rfl
    simp only [one_div, mul_zero, inv_eq_zero] at ha
    exact hd_ne_zero (by rw [ha])
  -- Reciprocal of both sides: `d = 1/(a*a) = (1/a)*(1/a)`.
  apply d_nonsquare D
  unfold IsSquare
  use 1 / a
  field_simp
  rw [pow_two, ← ha, mul_div_left_comm, div_self hd_ne_zero, mul_one]

lemma d_ne_one [IsRegularParam D.s] [IsCardThreeModFour F] : D.d ≠ 1 := by
  have hd_non_sq := d_nonsquare D
  intro hd_eq_one
  have hd_sq : IsSquare D.d := by
    rw [hd_eq_one]
    exact IsSquare.one
  contradiction

lemma d_ne_zero_and_d_ne_one [IsRegularParam D.s] [IsCardThreeModFour F] : D.d ≠ 0 ∧ D.d ≠ 1 := by
  have hd_ne_zero := d_ne_zero D
  have hd_ne_one := d_ne_one D
  exact ⟨hd_ne_zero, hd_ne_one⟩

lemma neg_d_eq_r_add_two_div_r_sub_two [IsNonzeroParam D.s] [IsCardThreeModFour F] :
    -D.d = (D.r + 2) / (D.r - 2) := by
  calc
    -D.d = (D.c + 2 + 1 / D.c) / (D.c - 2 + 1 / D.c) := by
      change -(-(D.c + 1) ^ 2 / (D.c - 1) ^ 2) = (D.c + 2 + 1 / D.c) / (D.c - 2 + 1 / D.c)
      rw [← neg_one_mul]
      nth_rw 2 [← neg_one_mul]
      rw [mul_div_assoc, ← mul_assoc, add_pow_two, sub_pow_two]
      rw [mul_neg, mul_one, neg_neg, one_pow, one_mul, one_div, mul_one]
      nth_rw 1 [← mul_left_inj' (one_ne_zero' F)]
      rw [mul_one]
      nth_rw 3 [← div_self (c_ne_zero D)]
      rw [div_mul_div_comm, add_mul, add_mul, add_mul, sub_mul]
      rw [← pow_two, inv_mul_cancel₀ (c_ne_zero D)]
    _ = (D.r + 2) / (D.r - 2) := by
      rw [add_assoc, add_comm 2 (1 / D.c), ← add_assoc]
      nth_rw 3 [add_comm]
      rw [← add_sub_assoc]
      nth_rw 3 [add_comm]
      rfl

end d

end Cslib.Crypto.Systems.Elligator.Elligator1.CurveParameters
