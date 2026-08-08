/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Cslib.Crypto.Systems.Elligator.Elligator1.Variables
public import Cslib.Crypto.Systems.Elligator.Elligator1.cProperties
public import Cslib.Crypto.Systems.Elligator.Elligator1.rProperties
public import Cslib.Crypto.Systems.Elligator.Elligator1.uProperties

/-!
# v Variable Properties

In this file we introduce some generally helpful lemmas for `v` as introduced in
`Cslib.Crypto.Systems.Elligator.Elligator1.Variables`.

## References

See [bernstein2013a], Section 3.2, Theorem 1.
-/

@[expose] public section

namespace Cslib.Crypto.Systems.Elligator.Elligator1

open Elligator.FiniteFieldBasic
open Elligator.LegendreSymbol

variable {F : Type*} [Field F] [Fintype F]
variable {s : F}
variable {q : ℕ}

lemma v_factored
  (hs_ne_zero : s ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  :
  let v := v t s
  let c := c s
  let u := u t
  v = u * (u^2 + c^2) * (u^2 + 1 / c^2) := by
    intro v c u
    let r := r s
    change u^5 + (r^2 - 2) * u^3 + u = u * (u^2 + c^2) * (u^2 + 1 / c^2)
    have hc_sq_ne_zero : c^2 ≠ 0 := pow_ne_zero 2 (c_ne_zero hs_ne_zero hq_card hq_mod)
    grind [r_sq_sub_two_eq_c_sq_add_inv_c_sq]

lemma v_factored_second_factor_ne_zero
  (hs_ne_zero : s ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  : (u t)^2 + (c s)^2 ≠ 0 := by
    intro h_sum_eq_zero
    let c := c s
    let u := u t
    have h_neg_one_sq : -1 = (u / c)^2 := by
      have hc_sq_ne_zero := pow_ne_zero 2 (c_ne_zero hs_ne_zero hq_card hq_mod)
      grind
    have h_isSquare : IsSquare (-1 : F) := by
      rw [h_neg_one_sq, pow_two]
      apply IsSquare.mul_self (u / c)
    rw [FiniteField.isSquare_neg_one_iff, hq_card] at h_isSquare
    contradiction

lemma v_factored_third_factor_ne_zero
  (hs_ne_zero : s ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  : (u t)^2 + 1 / (c s)^2 ≠ 0 := by
    intro h_sum_eq_zero
    have h_neg_one_sq : -1 = ((u t) * (c s))^2 := by
      grind [pow_ne_zero, c_ne_zero, div_left_inj']
    have h_isSquare : IsSquare (-1 : F) := by
      rw [h_neg_one_sq, pow_two]
      apply IsSquare.mul_self
    rw [FiniteField.isSquare_neg_one_iff, hq_card] at h_isSquare
    contradiction

lemma v_ne_zero
  (hs_ne_zero : s ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  : v t s ≠ (0 : F) := by
    rw [v_factored hs_ne_zero hq_card hq_mod t]
    apply mul_ne_zero
    · apply mul_ne_zero
      · apply u_ne_zero t
      · exact (v_factored_second_factor_ne_zero hs_ne_zero hq_card hq_mod t)
    · exact (v_factored_third_factor_ne_zero hs_ne_zero hq_card hq_mod t)

lemma χ_of_v_mul_v_of_t_pow_q_add_one_div_four_ne_zero
  [DecidableEq F]
  (t : { t : F // t ≠ 1 ∧ t ≠ -1})
  (hs_ne_zero : s ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  :
  let v := v t s
  ((χ v) * v)^((q + 1) / 4) ≠ 0 := by
    intro v
    rw [mul_pow (χ v) v ((q + 1) / 4)]
    apply mul_ne_zero
    · apply pow_ne_zero ((q + 1) / 4) (χ_a_ne_zero (v_ne_zero hs_ne_zero hq_card hq_mod t))
    · apply pow_ne_zero ((q + 1) / 4) (v_ne_zero hs_ne_zero hq_card hq_mod t)

omit [Fintype F] in
lemma v_comparison (t : { t : F // t ≠ 1 ∧ t ≠ -1}) :
  let t1 := t.val
  let t2 := -t1
  let u1 := u t
  let v2 := v ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s
  let r := r s
  v2 = 1 / u1^5 + (r^2 - 2) * 1 / u1^3 + 1 / u1 := by
    intro t1 t2 u1 v2 r_of_s
    let u2 := u ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩
    calc
      v2 = u2^5 + (r_of_s^2 - 2) * u2^3 + u2 := by rfl
      _ = 1 / u1^5 + (r_of_s^2 - 2) * 1/ u1^3 + 1 / u1 := by
        unfold u2 u1 t2 t1
        rw [u_comparison t]
        ring_nf

omit [Fintype F] in
lemma v_comparison_implication1 (t : { t : F // t ≠ 1 ∧ t ≠ -1}) :
  let t1 := t.val
  let t2 := -t1
  let u1 := u t
  let v1 := v t s
  let v2 := v ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s
  v2 * u1^6 = v1 := by
    intro t1 t2 u1 v1 v2
    let r := r s
    calc
      v2 * u1^6 = u1 + (r^2 - 2) * u1^3 + u1^5 := by
        unfold v2
        rw [v_comparison t]
        grind
      _ = v1 := by grind [v]

omit [Fintype F] in
lemma v_comparison_implication2 (t : {n : F // n ≠ 1 ∧ n ≠ -1}) :
  let t1 := t.val
  let t2 := -t1
  let u1 := u t
  let v1 := v t s
  let v2 := v ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s
  v2 = v1 / u1^6 := by
    intro t1 t2 u1 v1 v2
    have hu1_pow6_ne_zero : u1^6 ≠ 0 := pow_ne_zero 6 (u_ne_zero t)
    rw [← mul_right_inj' hu1_pow6_ne_zero]
    unfold v1
    rw [← v_comparison_implication1 t]
    grind

lemma v_comparison_implication3
  [DecidableEq F]
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  : χ ((u t)^6) = 1 := by
    let u := u t
    have h : u^6 = u^2 * u^2 * u^2 := by ring_nf
    rw [h, χ_mul, χ_mul, χ_sq (u_ne_zero t)]
    rw [mul_one, mul_one]

lemma v_comparison_implication4
  [DecidableEq F]
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  :
  let t1 := t.val
  let t2 := -t1
  let v1 := v t s
  let v2 := v ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s
  χ v2 = χ v1 := by
    intro t1 t2 v1 v2
    let u := u t
    unfold v1
    rw [← v_comparison_implication1 t]
    change χ v2= χ (v2 * u^6)
    rw [χ_mul]
    rw [v_comparison_implication3 t]
    simp

omit [Fintype F] in
@[simp]
lemma v_of_zero :
  let v := v ⟨(0 : F), by simp⟩ s
  v = (r s)^2 := by
    intro v_of_t
    unfold v_of_t v
    rw [u_of_zero]
    ring_nf

end Cslib.Crypto.Systems.Elligator.Elligator1
