/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Cslib.Crypto.Systems.Elligator.Elligator1.Variables
public import Cslib.Crypto.Systems.Elligator.Elligator1.cProperties

/-!
# d Variable Properties

In this file we introduce some generally helpful lemmas for `d` as introduced
in `Cslib.Crypto.Systems.Elligator.Elligator1.Variables`.

## References

See [bernstein2013a], Section 3.2, Theorem 1.
-/

@[expose] public section

namespace Cslib.Crypto.Systems.Elligator.Elligator1

open Elligator.FiniteFieldBasic

variable {F : Type*} [Field F] [Fintype F]
variable {s : F}
variable {q : ℕ}

lemma d_nonsquare
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  : ¬IsSquare (d s) := by
    rw [isSquare_iff_exists_mul_self (d s)]
    change ¬∃ r, (-((2 / s^2) + 1)^2 / ((2 / s^2) - 1)^2) = r * r
    rintro ⟨w, Pw⟩
    have hdivd : (2 / s^2 - 1)^2 ≠ 0 := by grind
    have hdivs : (2 / s^2 + 1)^2 ≠ 0 := by grind
    have heq : w^2 * ((2 / s^2) - 1)^2 / ((2 / s^2) + 1)^2 = -1 := by grind
    have hsq : IsSquare (-1 : F) := by
      rw [← heq]
      have hw_sq : IsSquare (w^2) := by
        rw [pow_two]
        apply IsSquare.mul_self w
      have hdiv_sq : IsSquare (((2 / s^2) - 1)^2 / ((2 / s^2) + 1)^2) := by
        apply IsSquare.div
        · rw [pow_two]
          apply IsSquare.mul_self (2 / s^2 - 1)
        · rw [pow_two]
          apply IsSquare.mul_self (2 / s^2 + 1)
      rw [mul_div_assoc]
      apply IsSquare.mul hw_sq hdiv_sq
    exact false_of_isSquare_neg_one hq_card hq_mod hsq

lemma d_ne_zero
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  : (d s) ≠ 0 := by
    have hd_nsq := d_nonsquare sq_ne_pm_two hq_card hq_mod
    intro hd_eq_zero
    have hd_sq : IsSquare (d s) := by
      unfold IsSquare
      use 0
      rwa [mul_zero]
    contradiction

lemma one_div_d_nonsquare
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  : ¬IsSquare (1 / (d s)) := by
    rintro ⟨a, ha⟩
    have hd_ne_zero : d s ≠ 0 := d_ne_zero sq_ne_pm_two hq_card hq_mod
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

lemma d_ne_one
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0) (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
  : (d s) ≠ 1 := by
    have hd_non_sq := d_nonsquare sq_ne_pm_two hq_card hq_mod
    intro hd_eq_one
    have hd_sq : IsSquare (d s) := by
      rw [hd_eq_one]
      apply IsSquare.one
    contradiction

lemma d_ne_zero_and_d_ne_one
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  : (d s) ≠ 0 ∧ (d s) ≠ 1 :=
    ⟨d_ne_zero sq_ne_pm_two hq_card hq_mod, d_ne_one sq_ne_pm_two hq_card hq_mod⟩

lemma neg_d_eq_r_add_two_div_r_sub_two
  (hs_ne_zero : s ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  :
  let r := r s;
  let d := d s;
  -d = (r + 2) / (r - 2) := by
    intro r d
    let c := c s
    calc
      -d = (c + 2 + 1 / c) / (c - 2 + 1 / c) := by
        change -(-(c + 1)^2 / (c - 1)^2) = (c + 2 + 1 / c) / (c - 2 + 1 / c)
        rw [← neg_one_mul]
        nth_rw 2 [← neg_one_mul]
        rw [mul_div_assoc, ← mul_assoc, add_pow_two, sub_pow_two]
        have hne : 1 / c ≠ 0 := by
          rw [← inv_eq_one_div]
          apply inv_ne_zero
          apply c_ne_zero hs_ne_zero hq_card hq_mod
        simp_all
        grind
      _ = (r + 2) / (r - 2) := by
        rw [add_assoc, add_comm 2 (1 / c), ← add_assoc]
        nth_rw 3 [add_comm]
        rw [← add_sub_assoc]
        nth_rw 3 [add_comm]
        rfl

end Cslib.Crypto.Systems.Elligator.Elligator1
