/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Cslib.Crypto.Systems.Elligator.Elligator1.Variables
public import Cslib.Crypto.Systems.Elligator.Elligator1.sProperties
public import Cslib.Crypto.Systems.Elligator.Elligator1.cProperties
public import Cslib.Crypto.Systems.Elligator.Elligator1.uProperties
public import Cslib.Crypto.Systems.Elligator.Elligator1.vProperties
public import Cslib.Crypto.Systems.Elligator.Elligator1.XProperties

/-!
# Y Variable Properties

In this file we introduce some generally helpful lemmas for `Y` as introduced in
`Cslib.Crypto.Systems.Elligator.Elligator1.Variables`.

## References

See [bernstein2013a], Section 3.2, Theorem 1.
-/

@[expose] public section

namespace Cslib.Crypto.Systems.Elligator.Elligator1

open Elligator.FiniteFieldBasic
open Elligator.LegendreSymbol

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {s : F}
variable {q : ℕ}

omit [DecidableEq F] in
lemma Y_ne_zero
  [DecidableEq F]
  (hs_ne_zero : s ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  :
  let Y := Y t s q
  Y ≠ 0 := by
    let u := u t
    let v := v t s
    let χ_of_sum := χ (u^2 + 1 / (c s)^2)
    intro Y
    change ((χ v) * v)^((q + 1) / 4) * (χ v) * χ_of_sum ≠ 0
    have hv_ne_zero := v_ne_zero hs_ne_zero hq_card hq_mod t
    apply mul_ne_zero
    · apply mul_ne_zero
      · rw [mul_pow (χ v) v ((q + 1) / 4)]
        apply mul_ne_zero
        · apply pow_ne_zero (((q + 1) / 4) : ℕ)
          apply χ_a_ne_zero hv_ne_zero
        · apply pow_ne_zero (((q + 1) / 4) : ℕ)
          apply hv_ne_zero
      · apply χ_a_ne_zero hv_ne_zero
    · apply χ_a_ne_zero (v_factored_third_factor_ne_zero hs_ne_zero hq_card hq_mod t)

omit [DecidableEq F] in
lemma X_mul_Y_ne_zero
  [DecidableEq F]
  (hs_ne_zero : s ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  :
  let X := X t s
  let Y := Y t s q
  X * Y ≠ 0 := by
    apply mul_ne_zero
    · apply X_ne_zero hs_ne_zero hq_card hq_mod t
    · apply Y_ne_zero hs_ne_zero hq_card hq_mod t

omit [DecidableEq F] in
lemma one_add_X_ne_zero
  [DecidableEq F]
  (hs_ne_zero : s ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  :
  let X := X t s
  (1 + X) ≠ (0 : F) := by
    let u := u t
    let v := v t s
    let r := r s
    have hv_ne_zero := v_ne_zero hs_ne_zero hq_card hq_mod t
    intro X
    change 1 + (χ v) * u ≠ 0
    intro h_contra
    have h_chi_v_mul_u_eq_neg_one : (χ v) * u = -1 := by grind
    have h_u_eq_neg_chi_v : u = -(χ v) := by grind [one_div_χ_of_a_eq_χ_a]
    have h_v_eq_expand : v = -(χ v) * (1 + r^2 - 2 + 1) := by
      change u^5 + (r^2 - 2) * u^3 + u = -(χ v) * (1 + r^2 - 2 + 1)
      repeat rw [h_u_eq_neg_chi_v]
      rw [← neg_one_mul, mul_pow, mul_pow]
      grind [χ_of_a_pow_n_eq_χ_a]
    have h_v_eq_neg_chi_v_mul_r_sq : v = -(χ v) * r^2 := by grind
    have h_chi_v_eq_neg_chi_v : (χ v) = -(χ v) := by
      rw [h_u_eq_neg_chi_v] at h_chi_v_mul_u_eq_neg_one
      change (χ v) * -(χ v) = -1 at h_chi_v_mul_u_eq_neg_one
      nth_rw 1 [h_v_eq_neg_chi_v_mul_r_sq] at h_chi_v_mul_u_eq_neg_one
      rw [χ_mul] at h_chi_v_mul_u_eq_neg_one
      nth_rw 1 [← neg_one_mul] at h_chi_v_mul_u_eq_neg_one
      rw [χ_mul, χ_neg_one hq_card hq_mod] at h_chi_v_mul_u_eq_neg_one
      rw [χ_χ_eq_χ hq_card hq_mod] at h_chi_v_mul_u_eq_neg_one
      have hr_sq_ne_zero : r^2 ≠ 0 := pow_ne_zero 2 (r_ne_zero hs_ne_zero hq_card hq_mod)
      have hr_sq_isSquare : IsSquare (r^2) := IsSquare.sq r
      grind [χ_a_eq_one]
    have h_chi_v_ne_neg_chi_v : (χ v) ≠ -(χ v) := neg_χ_a_ne_χ_a hv_ne_zero hq_card hq_mod
    contradiction

omit [DecidableEq F] in
lemma Y_comparison
  [DecidableEq F]
  (t : { t : F // t ≠ 1 ∧ t ≠ -1})
  (hs_ne_zero : s ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  :
  let t1 := t.val
  let t2 := -t1
  let X1 := X t s
  let Y1 := Y t s q
  let Y2 := Y ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s q
  Y2 = Y1 / X1^3 := by
    intro t1 t2 X1 Y1 Y2
    let t_h := neg_t_ne_one_and_neg_t_ne_neg_one t
    let c := c s
    let r := r s
    let u1 := u t
    let u2 := u ⟨t2, t_h⟩
    let v1 := v t s
    let v2 := v ⟨t2, t_h⟩ s
    have hu1_ne_zero := u_ne_zero (t := t)
    have first_factor :
      ((χ v2) * v2)^((q + 1) / 4) = ((χ v1) * v1)^((q + 1) / 4) * (χ u1) / u1^3 := by
        have h_v2_mul_v2_eq_v1_mul_v1_div_u1_pow6 : (χ v2) * v2 = (χ v1) * v1 / u1^6 := by
          rw [v_comparison_implication4 t]
          unfold v2
          rw [v_comparison_implication2 t]
          change (χ v1) * (v1 / u1^6) = (χ v1) * v1 / u1 ^ 6
          rw [← mul_div_assoc]
        have h_chi_u1_mul_u1_cubed_isSquare : IsSquare ((χ u1) * u1^3) := by
          have h_chi_u1_mul_u1_cubed_ne_zero : (χ u1) * u1^3 ≠ 0 := by
            apply mul_ne_zero
            · apply χ_a_ne_zero hu1_ne_zero
            · apply pow_ne_zero 3 hu1_ne_zero
          apply (χ_eq_one_iff_isSquare h_chi_u1_mul_u1_cubed_ne_zero hq_card hq_mod).mp
          have h_three_eq_one_add_two : (3 : ℕ) = 1 + 2 := by norm_num
          rw [h_three_eq_one_add_two, pow_add u1 1 2, ← mul_assoc, pow_one]
          rw [χ_mul, χ_mul]
          rw [χ_χ_eq_χ hq_card hq_mod]
          rw [← χ_mul, ← pow_two]
          have h_u1_sq_isSquare : IsSquare (u1^2) := IsSquare.sq u1
          have h_chi_u1_sq_eq_one : χ (u1 ^ 2) = 1 := by
            apply (χ_eq_one_iff_isSquare (pow_ne_zero 2 hu1_ne_zero) hq_card hq_mod).mpr
            exact h_u1_sq_isSquare
          simp [h_chi_u1_sq_eq_one]
        have h_u1_pow6_pow_eq_chi_u1_mul_u1_cubed : (u1^6)^((q + 1) / 4) = (χ u1) * u1^3 := by
          have h_six_eq_three_mul_two : 6 = 3 * 2 := by norm_num
          rw [h_six_eq_three_mul_two, ← pow_mul, mul_assoc, mul_comm, pow_mul, mul_comm]
          rw [add_comm, one_add_q_div_four_mul_two_eq_one_add_q_div_two hq_mod]
          rw [add_comm, a_pow_q_add_one_div_two_eq_χ_of_a_mul_a hq_card hq_mod]
          change ((χ u1) * u1)^3 = (χ u1) * u1^3
          rw [mul_pow, χ_of_a_pow_n_eq_χ_a u1 ⟨3, by trivial⟩]
        calc
          ((χ v2) * v2)^((q + 1) / 4) = ((χ v1) * v1 / u1^6)^((q + 1) / 4) := by
            rw [h_v2_mul_v2_eq_v1_mul_v1_div_u1_pow6]
          _ = ((χ v1) * v1)^((q + 1) / 4) * (χ u1) / u1^3 := by
            rw [div_pow, h_u1_pow6_pow_eq_chi_u1_mul_u1_cubed]
            nth_rw 2 [one_div_χ_of_a_eq_χ_a]
            grind
    have second_factor : (χ v2) = (χ v1) := v_comparison_implication4 t
    have third_factor : χ (u2^2 + 1 / c^2) = χ (u1 * v1 * (u1^2 + 1 / c^2)) := by
      calc
        χ (u2^2 + 1 / c^2)
          = χ ((c^2 * u1^4 * (u2^2 + 1 / c^2)) * (u1^2 + 1 / c^2)^2) := by
          rw [← χ_of_a_eq_χ_a_mul_b_pow_two (c_ne_zero hs_ne_zero hq_card hq_mod)]
          rw [mul_comm, ← χ_of_a_eq_χ_a_mul_b_pow_two (pow_ne_zero 2 hu1_ne_zero)]
          rw [χ_of_a_eq_χ_a_mul_b_pow_two
            (v_factored_third_factor_ne_zero hs_ne_zero hq_card hq_mod t)]
          grind
        _ = χ ((u1^2 * (c^2 + u1^2)) * (u1^2 + 1 / c^2)^2) := by
          rw [pow_two u2]
          unfold u2
          rw [u_comparison t]
          change χ (c^2 * u1^4 * (1 / u1 * (1 / u1) + 1 / c^2) * (u1^2 + 1 / c^2)^2)
            = χ (u1^2 * (c^2 + u1^2) * (u1^2 + 1 / c^2)^2)
          have h_clear_denominators :
              c^2 * u1^4 * (1 / u1 * (1 / u1) + 1 / c^2) = u1^2 * (c^2 + u1^2) := by
            have hc_sq_ne_zero : c^2 ≠ 0 := pow_ne_zero 2 (c_ne_zero hs_ne_zero hq_card hq_mod)
            grind
          rw [h_clear_denominators]
        _ = χ (u1 * v1 * (u1^2 + 1 / c^2)) := by grind [v_factored]
    calc
      Y2 = Y1 * (χ u1) * χ (u1 * v1) / u1^3 := by
        unfold Y2 Y
        change ((χ v2) * v2)^((q + 1) / 4) * (χ v2) * χ (u2^2 + 1 / c^2)
          = Y1 * (χ u1) * χ (u1 * v1) / u1^3
        rw [first_factor, second_factor, third_factor, χ_mul]
        have h_rearrange :
          ((χ v1) * v1)^((q + 1) / 4) * (χ u1) / u1^3 * (χ v1)
          * (χ (u1 * v1) * (χ (u1^2 + 1 / c^2)))
          = ((χ v1) * v1) ^ ((q + 1) / 4) * (χ v1) * (χ (u1^2 + 1 / c^2))
            * (χ u1) * χ (u1 * v1) / u1^3 := by ring_nf
        rw [h_rearrange]
        rfl
      _ = Y1 / ((χ v1) * u1)^3 := by
        calc
        Y1 * (χ u1) * χ (u1 * v1) / u1^3 = Y1 * (χ v1) / u1^3 := by
          rw [χ_mul, ← mul_assoc, mul_assoc Y1, ← χ_mul, ← pow_two, χ_sq hu1_ne_zero, mul_one]
        _ = Y1 / ((χ v1) * u1)^(2 + 1) := by
          nth_rw 1 [one_div_χ_of_a_eq_χ_a]
          rw [mul_div_assoc, div_div]
          nth_rw 1 [← χ_of_a_pow_n_eq_χ_a v1 ⟨3, by trivial⟩, ← mul_pow]
          ring_nf
      _ = Y1 / X1^3 := by rfl

end Cslib.Crypto.Systems.Elligator.Elligator1
