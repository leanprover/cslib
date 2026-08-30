/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Cslib.Crypto.Systems.Elligator.Basic
public import Cslib.Crypto.Systems.Elligator.LegendreSymbol

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
variable {s : F}
variable {q : ℕ}

open Cslib.Crypto.Systems.Elligator
open Cslib.Crypto.Systems.Elligator.FiniteFieldBasic
open Cslib.Crypto.Systems.Elligator.LegendreSymbol

section s

lemma s_pow_two_ne_two (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0) :
    s ^ 2 ≠ 2 :=
  sub_ne_zero.mp (left_ne_zero_of_mul sq_ne_pm_two)

lemma s_pow_two_ne_neg_two (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0) :
    s ^ 2 ≠ -2 := by
  have hright_ne_zero_of_mul := right_ne_zero_of_mul sq_ne_pm_two
  rwa [ne_eq, add_eq_zero_iff_eq_neg] at hright_ne_zero_of_mul

end s

section c

/-- c(s) is a function defined in the paper.

Original:, Section "3.2 The map": Theorem 1
-/
def c (s : F) : F := 2 / s ^ 2

lemma c_ne_zero [Fintype F]
    (hs_ne_zero : s ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    c s ≠ 0 := by
  unfold c
  exact div_ne_zero (two_ne_zero hq_card hq_mod) (pow_ne_zero 2 hs_ne_zero)

lemma c_ne_one (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0) :
    c s ≠ 1 := by
  unfold c
  exact div_ne_one_of_ne (s_pow_two_ne_two sq_ne_pm_two).symm

lemma c_sub_one_ne_zero (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0) :
    (c s) - 1 ≠ 0 :=
  sub_ne_zero.2 (c_ne_one sq_ne_pm_two)

lemma c_ne_neg_one (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0) : (c s) ≠ -1 := by
  unfold c
  intro h_contra
  have hs_sq_eq_neg_two : s ^ 2 = -2 := by grind
  have hs_sq_ne_neg_two := s_pow_two_ne_neg_two sq_ne_pm_two
  contradiction

lemma c_add_one_ne_zero (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0) :
    (c s) + 1 ≠ 0 := by
  intro h_contra
  have hc_ne_neg_one := c_ne_neg_one sq_ne_pm_two
  rw [← add_left_inj (-1)] at h_contra
  ring_nf at h_contra
  contradiction

lemma c_mul_sub_one_mul_add_one_ne_zero [Fintype F]
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let c := c s
    c * (c - 1) * (c + 1) ≠ 0 := by
  unfold c
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact c_ne_zero hs_ne_zero hq_card hq_mod
    · exact c_sub_one_ne_zero sq_ne_pm_two
  · exact c_add_one_ne_zero sq_ne_pm_two

lemma s_pow_two_eq_two_div_c [Fintype F]
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    s ^ 2 = 2 / (c s) := by
  unfold c
  field_simp [FiniteFieldBasic.two_ne_zero]

end c

variable [Fintype F]

section r

/-- r(s) is a function defined in the paper.

Original:, Section "3.2 The map": Theorem 1
-/
def r (s : F) : F :=
    let c := c s
    c + 1 / c

lemma r_ne_zero (hs_ne_zero : s ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    r s ≠ 0 := by
  intro h_contra
  let c := c s
  change c + 1 / c = 0 at h_contra
  have hc_ne_zero := c_ne_zero hs_ne_zero hq_card hq_mod
  have hcneg : c = (-1 : F) / c := by
    rw [← add_left_inj (1 / c)]
    rw [neg_div, neg_add_cancel (1 / c)]
    exact h_contra
  have hcpow : c ^ 2 = -1 := by
    calc
      c ^ 2 = -1 / c * c := by
        rw [← div_left_inj' hc_ne_zero]
        rw [pow_two, mul_div_assoc, div_self hc_ne_zero, mul_one]
        rw [mul_div_assoc, div_self hc_ne_zero, mul_one]
        exact hcneg
      _ = -1 := by
        nth_rw 1 [← neg_one_mul 1]
        ring_nf
        rw [mul_inv_cancel₀ (c_ne_zero hs_ne_zero hq_card hq_mod)]
  have hsq : IsSquare (-1 : F) := by
    rw [← hcpow, pow_two]
    exact IsSquare.mul_self c
  exact false_of_isSquare_neg_one hq_card hq_mod hsq

lemma four_add_r_ne_zero (hs_ne_zero : s ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    4 + (r s) ≠ 0 := by
  intro h_contra
  have hc_ne_zero := c_ne_zero hs_ne_zero hq_card hq_mod
  -- Step 1: clear `1/c` from `r`'s definition.
  have h_quad : (c s) ^ 2 + 4 * (c s) + 1 = 0 := by
    unfold r at h_contra
    field_simp at h_contra
    rw [add_comm, add_assoc, mul_zero] at h_contra
    linear_combination h_contra
  -- Step 2: substitute `c = 2/s²`, clear denominators - `(s²+4)² = 12`.
  let a : F := s ^ 2 + 4
  have ha_sq : a ^ 2 = 12 := by
    unfold c at h_quad
    field_simp at h_quad
    linear_combination h_quad
  -- Step 3: halving, `u² = 3`.
  let u : F := a / 2
  have hu_sq : u ^ 2 = 3 := by
    unfold u
    rw [div_pow, ha_sq]
    have hfour_ne_zero := FiniteFieldBasic.four_ne_zero hq_card hq_mod
    rw [← mul_left_inj' hfour_ne_zero, div_mul]
    norm_num
    rw [div_self hfour_ne_zero, div_one]
  -- Step 4: `2u = a`, so `u² - 2u + 1 = 3 - a + 1 = -s²`, giving `((u-1)/s)² = -1`.
  have hu_eq_a : 2 * u = a := by
    unfold u
    rw [mul_div_left_comm]
    rw [div_self (FiniteFieldBasic.two_ne_zero hq_card hq_mod), mul_one]
  have h_neg_one_sq : (-1 : F) = ((u - 1) / s) ^ 2 := by
    rw [div_pow, eq_div_iff (pow_ne_zero 2 hs_ne_zero)]
    ring_nf
    rw [hu_sq]
    unfold u
    rw [div_mul, div_self (FiniteFieldBasic.two_ne_zero hq_card hq_mod)]
    ring
  exact false_of_isSquare_neg_one hq_card hq_mod ⟨_, h_neg_one_sq.trans (sq _)⟩

lemma r_sq_sub_two_eq_c_sq_add_inv_c_sq (hs_ne_zero : s ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let r := r s
    let c := c s
    (r ^ 2 - 2) = c ^ 2 + 1 / c ^ 2 := by
  intro r c
  calc
    r ^ 2 - 2 = (c + 1 / c) ^ 2 - 2 := by rfl
    _ = c ^ 2 + 2 * (c * (1 / c)) + (1 / c) ^ 2 - 2 := by ring
    _ = c ^ 2 + 2 + 1 / c ^ 2 - 2 := by
      ring_nf
      rw [mul_inv_cancel₀ (c_ne_zero hs_ne_zero hq_card hq_mod)]
      ring
    _ = c ^ 2 + 1 / c ^ 2 := by ring

lemma r_sub_two_ne_zero (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    (r s) - 2 ≠ 0 := by
  let c := c s
  have hc_ne_zero := c_ne_zero hs_ne_zero hq_card hq_mod
  change (c + 1 / c) - 2 ≠ 0
  have hceq : (c + 1 / c) - 2 = (c - 1) ^ 2 / c := by
    rw [← mul_left_inj' hc_ne_zero]
    change ((c + 1 / c) - 2) * c = ((c - 1) ^ 2 / c) * c
    rw [sub_mul, div_mul, div_self hc_ne_zero]
    ring_nf
    rw [mul_inv_cancel₀ hc_ne_zero]
    ring
  rw [hceq]
  have hdnez : (c - 1) ^ 2 ≠ 0 := pow_ne_zero 2 (c_sub_one_ne_zero sq_ne_pm_two)
  exact div_ne_zero hdnez hc_ne_zero

end r

section d

/-- d(s) is a function defined in the paper.

Original:, Section "3.2 The map": Theorem 1
-/
def d (s : F) : F :=
    let c := c s;
    -(c + 1) ^ 2 / (c - 1) ^ 2

lemma d_nonsquare (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    ¬IsSquare (d s) := by
  rw [isSquare_iff_exists_mul_self (d s)]
  change ¬∃ w, (-((2 / s ^ 2) + 1) ^ 2 / ((2 / s ^ 2) - 1) ^ 2) = w * w
  rintro ⟨w, Pw⟩
  have hdivd : (2 / s ^ 2 - 1) ^ 2 ≠ 0 := by grind
  have hdivs : (2 / s ^ 2 + 1) ^ 2 ≠ 0 := by grind
  have heq : w ^ 2 * ((2 / s ^ 2) - 1) ^ 2 / ((2 / s ^ 2) + 1) ^ 2 = -1 := by
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
    have hdiv_sq : IsSquare (((2 / s ^ 2) - 1) ^ 2 / ((2 / s ^ 2) + 1) ^ 2) := by
      apply IsSquare.div
      · rw [pow_two]
        exact IsSquare.mul_self (2 / s ^ 2 - 1)
      · rw [pow_two]
        exact IsSquare.mul_self (2 / s ^ 2 + 1)
    rw [mul_div_assoc]
    exact IsSquare.mul hw_sq hdiv_sq
  exact false_of_isSquare_neg_one hq_card hq_mod hsq

lemma d_ne_zero (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    (d s) ≠ 0 := by
  have hd_nsq := d_nonsquare sq_ne_pm_two hq_card hq_mod
  intro hd_eq_zero
  have hd_sq : IsSquare (d s) := by
    unfold IsSquare
    use 0
    rwa [mul_zero]
  contradiction

lemma one_div_d_nonsquare (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    ¬IsSquare (1 / (d s)) := by
  rintro ⟨a, ha⟩
  have hd_ne_zero := d_ne_zero sq_ne_pm_two hq_card hq_mod
  -- `1/d = a*a ≠ 0` (since `d ≠ 0`), so `a ≠ 0`.
  have ha_ne_zero : a ≠ 0 := by
    rintro rfl
    simp only [one_div, mul_zero, inv_eq_zero] at ha
    exact hd_ne_zero (by rw [ha])
  -- Reciprocal of both sides: `d = 1/(a*a) = (1/a)*(1/a)`.
  apply d_nonsquare sq_ne_pm_two hq_card hq_mod
  unfold IsSquare
  use 1 / a
  field_simp
  rw [pow_two, ← ha, mul_div_left_comm, div_self hd_ne_zero, mul_one]

lemma d_ne_one (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    (d s) ≠ 1 := by
  have hd_non_sq := d_nonsquare sq_ne_pm_two hq_card hq_mod
  intro hd_eq_one
  have hd_sq : IsSquare (d s) := by
    rw [hd_eq_one]
    exact IsSquare.one
  contradiction

lemma d_ne_zero_and_d_ne_one (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    (d s) ≠ 0 ∧ (d s) ≠ 1 :=
  ⟨d_ne_zero sq_ne_pm_two hq_card hq_mod, d_ne_one sq_ne_pm_two hq_card hq_mod⟩

lemma neg_d_eq_r_add_two_div_r_sub_two (hs_ne_zero : s ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let r := r s
    let d := d s
    (-d) = (r + 2) / (r - 2) := by
  intro r d
  let c := c s
  calc
    -d = (c + 2 + 1 / c) / (c - 2 + 1 / c) := by
      change -(-(c + 1) ^ 2 / (c - 1) ^ 2) = (c + 2 + 1 / c) / (c - 2 + 1 / c)
      rw [← neg_one_mul]
      nth_rw 2 [← neg_one_mul]
      rw [mul_div_assoc, ← mul_assoc, add_pow_two, sub_pow_two]
      have hc_ne_zero := c_ne_zero hs_ne_zero hq_card hq_mod
      rw [mul_neg, mul_one, neg_neg, one_pow, one_mul, one_div, mul_one]
      nth_rw 2 [← mul_left_inj' (one_ne_zero' F)]
      rw [mul_one]
      nth_rw 3 [← div_self hc_ne_zero]
      rw [div_mul_div_comm, add_mul, add_mul, add_mul, sub_mul]
      rw [← pow_two, inv_mul_cancel₀ hc_ne_zero]
    _ = (r + 2) / (r - 2) := by
      rw [add_assoc, add_comm 2 (1 / c), ← add_assoc]
      nth_rw 3 [add_comm]
      rw [← add_sub_assoc]
      nth_rw 3 [add_comm]
      rfl

end d

end Cslib.Crypto.Systems.Elligator.Elligator1.CurveParameters
