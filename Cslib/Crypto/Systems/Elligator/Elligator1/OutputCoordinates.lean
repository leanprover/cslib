/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Cslib.Crypto.Systems.Elligator.Elligator1.AuxiliaryCoordinates
public import Cslib.Crypto.Systems.Elligator.Elligator1.EdwardsCurve

/-!
# Output Coordinates

The Edwards curve coordinates `x`, `y` built from the auxiliary quantities of
`AuxiliaryCoordinates.lean`, together with the two conclusions of Theorem 1 —
nonvanishing of `u·v·X·Y·x·(y+1)` and the curve equation `x² + y² = 1 + dx²y²` — and their
behavior under `t ↦ -t`.

## Main Results

* `x`, `y`: the curve coordinates of [bernstein2013a], Section 3.2, Theorem 1.
* `x_ne_zero`, `y_add_one_ne_zero`: nonvanishing facts needed for Definition 2's map `ϕ`.
* `map_fulfills_auxiliary_equation`: the auxiliary coordinates satisfy `Y² = X⁵ + (r² - 2)X³ + X`.
* `curve_equation`: `x² + y² = 1 + dx²y²`, the first conclusion of Theorem 1.
* `variable_mul_ne_zero`: `u·v·X·Y·x·(y+1) ≠ 0`, the second conclusion of Theorem 1.

## References

See [bernstein2013a], Section 3.2, Theorem 1.
-/

@[expose] public section

namespace Cslib.Crypto.Systems.Elligator.Elligator1.OutputCoordinates

open Cslib.Crypto.Systems.Elligator.FiniteFieldBasic
open Cslib.Crypto.Systems.Elligator.LegendreSymbol
open Cslib.Crypto.Systems.Elligator.Elligator1.CurveParameters
open Cslib.Crypto.Systems.Elligator.Elligator1.AuxiliaryCoordinates

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (M : MapData F)

section x

/-- x(t, s) is a function defined in the paper. It is the x-coordinate of the point on the curve.

Original:, Section "3.2 The map": Theorem 1
-/
def x (t : {n : F // n ≠ 1 ∧ n ≠ -1}) (s : F) (q : ℕ) : F :=
    let c := c s
    let X := X t s
    let Y := Y t s q
    (c - 1) * s * X * (1 + X) / Y

/-- MapData wrapper for x. -/
def _root_.Cslib.Crypto.Systems.Elligator.MapData.x (M : MapData F) : F :=
    OutputCoordinates.x M.tSub M.s (Fintype.card F)

lemma x_ne_zero [IsNonzeroParam M.s] [IsRegularParam M.s] [IsCardThreeModFour F] :
    M.x ≠ 0 := by
  change (M.c - 1) * M.s * M.X * (1 + M.X) / M.Y ≠ 0
  apply div_ne_zero
  · apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · intro hc_sub_eq_zero
          exact (c_ne_one M.toParamData) (by linear_combination hc_sub_eq_zero)
        · exact s_ne_zero
      · exact X_ne_zero M
    · exact one_add_X_ne_zero M
  · exact Y_ne_zero M

end x

section y

/-- y(t, s) is a function defined in the paper. It is the y-coordinate of the point on the curve.

Original:, Section "3.2 The map": Theorem 1
-/
def y (t : {n : F // n ≠ 1 ∧ n ≠ -1}) (s : F) : F :=
    let r := r s
    let X := X t s
    (r * X - (1 + X) ^ 2) / (r * X + (1 + X) ^ 2)

/-- MapData wrapper for y. -/
def _root_.Cslib.Crypto.Systems.Elligator.MapData.y (M : MapData F) : F :=
    OutputCoordinates.y M.tSub M.s

/-- The auxiliary coordinates `X` and `Y` satisfy the hyperelliptic equation used in Theorem 1:
`Y² = X⁵ + (r² - 2)X³ + X`. -/
theorem auxiliary_coordinates_fulfill_helper_equation
    [IsNonzeroParam M.s] [IsCardThreeModFour F] :
    M.Y ^ 2 = M.X ^ 5 + (M.r ^ 2 - 2) * M.X ^ 3 + M.X := by
  have hv_ne_zero := v_ne_zero M
  have h_X_expand_eq_χ_v_mul_v : M.X ^ 5 + (M.r ^ 2 - 2) * M.X ^ 3 + M.X = χ M.v * M.v := by
    calc
    M.X ^ 5 + (M.r ^ 2 - 2) * M.X ^ 3 + M.X
        = χ M.v * (M.u ^ 5 + (M.r ^ 2 - 2) * M.u ^ 3 + M.u) := by
      change (χ M.v * M.u) ^ 5 + (M.r ^ 2 - 2) * (χ M.v * M.u) ^ 3 + (χ M.v * M.u)
        = χ M.v * (M.u ^ 5 + (M.r ^ 2 -2 ) * M.u ^ 3 + M.u)
      rw [mul_pow (χ M.v) (M.u) 5, mul_pow (χ M.v) (M.u) 3]
      rw [χ_of_a_pow_n_eq_χ_a M.v ⟨5, by trivial⟩]
      rw [χ_of_a_pow_n_eq_χ_a M.v ⟨3, by trivial⟩]
      ring
    _ = χ M.v * M.v := by rfl
  have hχ_a_mul_a_IsSquare := χ_a_mul_a_IsSquare hv_ne_zero card_mod_four
  have h_χ_v_mul_v_fixed : (χ M.v * M.v) ^ ((Fintype.card F + 1) / 2) = χ M.v * M.v :=
    a_pow_q_add_one_div_two_eq_a hχ_a_mul_a_IsSquare card_mod_four
  let χ_of_sum := χ (M.u ^ 2 + 1 / M.c ^ 2)
  have h_Y_sq_eq_χ_v_mul_v : M.Y ^ 2 = χ M.v * M.v := by
    calc
      M.Y ^ 2 = (χ M.v * M.v) ^ ((Fintype.card F + 1) / 2) * (χ M.v) ^ 2 * χ_of_sum ^ 2 := by
        change ((χ M.v * M.v) ^ ((Fintype.card F + 1) / 4) * χ M.v * χ_of_sum) ^ 2
          = (χ M.v * M.v) ^ ((Fintype.card F + 1) / 2) * (χ M.v) ^ 2 * χ_of_sum ^ 2
        ring_nf
        rw [one_add_q_div_four_mul_two_eq_one_add_q_div_two card_mod_four]
      _ = (χ M.v * M.v) ^ ((Fintype.card F + 1) / 2) * 1 := by
        rw [χ_of_a_even_pow_n_eq_one hv_ne_zero ⟨2, even_two⟩]
        rw [χ_of_a_even_pow_n_eq_one
          (v_factored_third_factor_ne_zero M) ⟨2, even_two⟩]
        rw [mul_one]
      _ = χ M.v * M.v := by rw [h_χ_v_mul_v_fixed, mul_one]
  rw [h_X_expand_eq_χ_v_mul_v]
  exact h_Y_sq_eq_χ_v_mul_v

lemma y_divisor_ne_zero [IsNonzeroParam M.s] [IsRegularParam M.s] [IsCardThreeModFour F] :
    (M.r * M.X + (1 + M.X) ^ 2) ≠ 0 := by
  intro h_contra
  have hr_mul_X_eq_neg_expand : M.r * M.X = -(1 + M.X) ^ 2 :=
    Eq.symm (neg_eq_of_add_eq_zero_left h_contra)
  have hY_sq_eq_neg_expand : M.Y ^ 2 = -(1 + M.X) ^ 2 * M.X ^ 2 * (M.s + 2 / M.s) ^ 2 := by
    calc
      M.Y ^ 2 = M.X * (M.X ^ 4 + (M.r ^ 2 - 2) * M.X ^ 2 + 1) := by
        rw [mul_add, mul_add]
        rw [auxiliary_coordinates_fulfill_helper_equation M]
        ring
      _ = M.X ^ 3 * (2 * M.r ^ 2 + 4 * M.r) := by grind
      _ = M.X ^ 3 * (2 * M.r ^ 2 + 4 * M.r) := by ring
      _ = M.r * M.X * M.X ^ 2 * (2 * M.r + 4) := by ring
      _ = -(1 + M.X) ^ 2 * M.X ^ 2 * (M.s + 2 / M.s) ^ 2 := by
        rw [← hr_mul_X_eq_neg_expand]
        change M.r * M.X * M.X ^ 2 * (2 * (2 / M.s ^ 2 + 1 / (2 / M.s ^ 2)) + 4)
          = M.r * M.X * M.X ^ 2 * (M.s + 2 / M.s) ^ 2
        have h_algebra_identity : (2 * (2 / M.s ^ 2 + 1 / (2 / M.s ^ 2)) + 4)
            = (M.s + 2 / M.s) ^ 2 := by
          ring_nf
          rw [inv_inv, mul_inv_cancel₀ s_ne_zero, one_mul, mul_assoc]
          rw [inv_mul_cancel₀ (FiniteFieldBasic.two_ne_zero card_mod_four)]
          ring
        rw [h_algebra_identity]
  have h_isSquare_neg_one : IsSquare (-1 : F) := by
    have h_ratio_eq_neg_one : M.Y ^ 2 / ((1 + M.X) * M.X * (M.s + 2 / M.s)) ^ 2 = -1 := by
      rw [← neg_one_mul, mul_assoc (-1) ((1 + M.X) ^ 2) (M.X ^ 2)] at hY_sq_eq_neg_expand
      rw [← mul_pow (1 + M.X) (M.X) 2, mul_assoc (-1) _ _] at hY_sq_eq_neg_expand
      rw [← mul_pow (((1 + M.X) * M.X))] at hY_sq_eq_neg_expand
      have h_denom_ne_zero : ((1 + M.X) * M.X * (M.s + 2 / M.s)) ^ 2 ≠ 0 := by
        apply pow_ne_zero 2
        apply mul_ne_zero
        · exact mul_ne_zero (one_add_X_ne_zero M) (X_ne_zero M)
        · intro h_contra'
          have hspow_eq_zero : M.s ^ 2 + 2 = 0 := by
            rw [← div_left_inj' (s_ne_zero (s := M.s))]
            rw [zero_div, add_div, pow_two, mul_div_assoc, div_self s_ne_zero, mul_one]
            exact h_contra'
          have hspow_ne_zero : M.s ^ 2 + 2 ≠ 0 := right_ne_zero_of_mul s_sq_ne_pm_two
          contradiction
      rw [← div_left_inj' h_denom_ne_zero, mul_div_assoc, div_self h_denom_ne_zero, mul_one]
        at hY_sq_eq_neg_expand
      exact hY_sq_eq_neg_expand
    have h_ratio_sq_eq_neg_one : (M.Y / ((1 + M.X) * M.X * (M.s + 2 / M.s))) ^ 2 = -1 := by
      rw [← div_pow] at h_ratio_eq_neg_one
      exact h_ratio_eq_neg_one
    rw [← h_ratio_sq_eq_neg_one, pow_two]
    exact IsSquare.mul_self _
  have h_mod_ne_three : Fintype.card F % 4 ≠ 3 := by
    rw [FiniteField.isSquare_neg_one_iff] at h_isSquare_neg_one
    exact h_isSquare_neg_one
  have h_mod_eq_three : Fintype.card F % 4 = 3 := card_mod_four
  contradiction

lemma y_add_one_ne_zero [IsNonzeroParam M.s] [IsCardThreeModFour F] :
    M.y + 1 ≠ 0 := by
  intro h_contra
  have hy_eq_neg_one : M.y = -1 := Eq.symm (neg_eq_of_add_eq_zero_left h_contra)
  have hy_unfolded_eq_neg_one : (M.r * M.X - (1 + M.X) ^ 2) / (M.r * M.X + (1 + M.X) ^ 2) = -1 := by
    change M.y = -1
    exact hy_eq_neg_one
  have h_num_eq_neg_denom : M.r * M.X - (1 + M.X) ^ 2 = -(M.r * M.X + (1 + M.X) ^ 2) := by
    rw [neg_eq_neg_one_mul, ← hy_unfolded_eq_neg_one]
    have hdiv_ne_zero : M.r * M.X + (1 + M.X) ^ 2 ≠ 0 := by
      intro h_contra'
      rw [h_contra', div_zero, zero_eq_neg] at hy_unfolded_eq_neg_one
      apply one_ne_zero' F at hy_unfolded_eq_neg_one
      contradiction
    rw [div_mul_comm, div_self hdiv_ne_zero, one_mul]
  have hr_mul_X_eq_zero : M.r * M.X = 0 := by
    rw [← add_left_inj (M.r * M.X + (1 + M.X) ^ 2)] at h_num_eq_neg_denom
    ring_nf at h_num_eq_neg_denom
    rw [← div_left_inj' (two_ne_zero card_mod_four), mul_div_assoc] at h_num_eq_neg_denom
    rw [div_self (two_ne_zero card_mod_four)] at h_num_eq_neg_denom
    ring_nf at h_num_eq_neg_denom
    exact h_num_eq_neg_denom
  have hr_mul_X_ne_zero : M.r * M.X ≠ 0 := mul_ne_zero (r_ne_zero M.toParamData) (X_ne_zero M)
  contradiction

/-- The quantities constructed for a nonexceptional input are all nonzero as asserted in
Theorem 1: `u * v * X * Y * x * (y + 1) ≠ 0`. -/
theorem map_variable_mul_ne_zero
    [IsNonzeroParam M.s] [IsRegularParam M.s] [IsCardThreeModFour F] :
    M.u * M.v * M.X  * M.Y * M.x * (M.y + 1) ≠ 0 := by
  apply mul_ne_zero
  · apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · apply mul_ne_zero (u_ne_zero M.toInputData) (v_ne_zero M)
        · exact X_ne_zero M
      · exact Y_ne_zero M
    · exact x_ne_zero M
  · exact y_add_one_ne_zero M

lemma curve_equation [IsNonzeroParam M.s] [IsRegularParam M.s] [IsCardThreeModFour F] :
    M.x ^ 2 + M.y ^ 2 = 1 + M.d * M.x ^ 2 * M.y ^ 2 := by
  have h_c_sub_one_sq_mul_s_sq_eq : (M.c - 1) ^ 2 * M.s ^ 2 = 2 * (M.r - 2) :=
    calc
      (M.c - 1) ^ 2 * M.s ^ 2 = (M.c - 1) ^ 2 * (2 / M.c) := by
        rw [← s_pow_two_eq_two_div_c M.toParamData]
      _ = 2 * (M.r - 2) := by
        rw [sub_pow_two, mul_one, one_pow 2, add_mul, sub_mul]
        rw [← mul_div_assoc, one_mul, mul_comm, pow_two, ← mul_assoc]
        rw [mul_div_assoc, div_self (c_ne_zero M.toParamData), mul_one]
        nth_rw 4 [← mul_one 2]
        rw [add_comm, ← add_sub_assoc, mul_div_assoc, ← mul_add 2 (1 / M.c) M.c, add_comm]
        change 2 * M.r - 2 * M.c * (2 / M.c) = 2 * (M.r - 2)
        ring_nf
        rw [mul_inv_cancel₀ (c_ne_zero M.toParamData)]
        ring
  have h_Y_sq_mul_one_sub_x_sq_eq : M.Y ^ 2 * (1 - M.x ^ 2)
      = M.X * (M.r * M.X - (1 + M.X) ^ 2) ^ 2 := by
    calc
      M.Y ^ 2 * (1 - M.x ^ 2) = M.Y ^ 2 - (M.c - 1) ^ 2 * M.s ^ 2 * M.X ^ 2 * (1 + M.X) ^ 2 := by
        change M.Y ^ 2 * (1 - (((M.c - 1) * M.s * M.X * (1 + M.X)) / M.Y) ^ 2)
          = M.Y ^ 2 - (M.c - 1) ^ 2 * M.s ^ 2 * M.X ^ 2 * (1 + M.X) ^ 2
        have hY_sq_ne_zero : M.Y ^ 2 ≠ 0 := pow_ne_zero 2 (Y_ne_zero M)
        rw [mul_sub, mul_one, ← add_right_inj (-(M.Y ^ 2))]
        repeat rw [← add_sub_assoc, neg_add_cancel, zero_sub]
        nth_rw 2 [← mul_pow, ← mul_pow, ← mul_pow]
        rw [neg_inj, ← div_left_inj' hY_sq_ne_zero, mul_comm, mul_div_assoc, div_self hY_sq_ne_zero]
        ring
    _ = M.X ^ 5 + (M.r ^ 2 - 2) * M.X ^ 3 + M.X - 2 * (M.r - 2) * M.X ^ 2 * (1 + M.X) ^ 2 := by
        rw [h_c_sub_one_sq_mul_s_sq_eq]
        rw [auxiliary_coordinates_fulfill_helper_equation M]
    _ = M.X * (M.r * M.X - (1 + M.X) ^ 2) ^ 2 := by ring
  have h_neg_d_mul_c_sub_one_sq_mul_s_sq_eq : -M.d * (M.c - 1) ^ 2 * M.s ^ 2 = 2 * (M.r + 2) := by
    rw [neg_d_eq_r_add_two_div_r_sub_two M.toParamData, mul_assoc, h_c_sub_one_sq_mul_s_sq_eq]
    rw [mul_comm, ← mul_div_assoc, mul_assoc, mul_comm (M.r - 2) (M.r + 2), ← mul_assoc]
    have hr_sub_two_ne_zero : M.r - 2 ≠ 0 := by
      intro hr_sub_two_eq_zero
      have h_c_sub_one_sq_mul_s_sq_eq_zero : (M.c - 1) ^ 2 * M.s ^ 2 = 0 := by
        rw [hr_sub_two_eq_zero, mul_zero] at h_c_sub_one_sq_mul_s_sq_eq
        exact h_c_sub_one_sq_mul_s_sq_eq
      have h_c_sub_one_sq_mul_s_sq_ne_zero : (M.c - 1) ^ 2 * M.s ^ 2 ≠ 0 := by
        apply mul_ne_zero
        · exact pow_ne_zero 2 (c_sub_one_ne_zero M.toParamData)
        · exact pow_ne_zero 2 s_ne_zero
      contradiction
    rw [mul_div_assoc, div_self hr_sub_two_ne_zero, mul_one]
  have h_Y_sq_mul_one_sub_d_mul_x_sq_eq : M.Y ^ 2 * (1 - M.d * M.x ^ 2)
      = M.X * (M.r * M.X + (1 + M.X) ^ 2) ^ 2 := by
    calc
      M.Y ^ 2 * (1 - M.d * M.x ^ 2)
          = M.Y ^ 2 - M.d * (M.c - 1) ^ 2 * M.s ^ 2 * M.X ^ 2 * (1 + M.X) ^ 2 := by
        change M.Y ^ 2 * (1 - M.d * (((M.c - 1) * M.s * M.X * (1 + M.X)) / M.Y) ^ 2)
          = M.Y ^ 2 - M.d * (M.c - 1) ^ 2 * M.s ^ 2 * M.X ^ 2 * (1 + M.X) ^ 2
        rw [mul_sub, mul_one]
        have hY_sq_ne_zero : M.Y ^ 2 ≠ 0 := pow_ne_zero 2 (Y_ne_zero M)
        rw [div_pow, mul_comm, ← mul_div_assoc, div_mul_comm, div_self hY_sq_ne_zero, one_mul]
        ring
    _ = M.X ^ 5 + (M.r ^ 2 - 2) * M.X ^ 3 + M.X + 2 * (M.r + 2) * M.X ^ 2 * (1 + M.X) ^ 2 := by
      rw [sub_eq_add_neg, neg_eq_neg_one_mul, ← mul_assoc, ← mul_assoc, ← mul_assoc]
      rw [neg_eq_neg_one_mul, mul_assoc (-1)] at h_neg_d_mul_c_sub_one_sq_mul_s_sq_eq
      rw [mul_assoc, h_neg_d_mul_c_sub_one_sq_mul_s_sq_eq]
      rw [auxiliary_coordinates_fulfill_helper_equation M]
      ring
    _ = M.X * (M.r * M.X + (1 + M.X) ^ 2) ^ 2 := by ring
  have h_one_sub_d_mul_x_sq_ne_zero : (1 - M.d * M.x ^ 2) ≠ 0 := by
    intro h_one_sub_d_mul_x_sq_eq_zero
    have hd_isSquare : IsSquare M.d := by
      rw [← add_right_inj (M.d * M.x ^ 2), add_comm] at h_one_sub_d_mul_x_sq_eq_zero
      have h_cancel_identity : 1 - M.d * M.x ^ 2 + M.d * M.x ^ 2 = 1 := by ring
      rw [add_zero, h_cancel_identity] at h_one_sub_d_mul_x_sq_eq_zero
      have hx_sq_ne_zero : M.x ^ 2 ≠ 0 := pow_ne_zero 2 (x_ne_zero M)
      rw [← div_left_inj' hx_sq_ne_zero] at h_one_sub_d_mul_x_sq_eq_zero
      rw [mul_div_assoc, div_self hx_sq_ne_zero, mul_one] at h_one_sub_d_mul_x_sq_eq_zero
      rw [← mul_one 1, ← pow_two, ← div_pow _ _ 2] at h_one_sub_d_mul_x_sq_eq_zero
      rw [← h_one_sub_d_mul_x_sq_eq_zero, pow_two]
      exact IsSquare.mul_self _
    have hd_not_isSquare : ¬IsSquare M.d := d_nonsquare M.toParamData
    contradiction
  have h_Y_sq_mul_one_sub_d_mul_x_sq_ne_zero : M.Y ^ 2 * (1 - M.d * M.x ^ 2) ≠ 0 := by
    apply mul_ne_zero
    · exact pow_ne_zero 2 (Y_ne_zero M)
    · exact h_one_sub_d_mul_x_sq_ne_zero
  have h_ratio_eq_y_sq : (1 - M.x ^ 2) / (1 - M.d * M.x ^ 2) = M.y ^ 2 := by
    calc
      (1 - M.x ^ 2) / (1 - M.d * M.x ^ 2)
          = (M.r * M.X - (1 + M.X) ^ 2) ^ 2 / (M.r * M.X + (1 + M.X) ^ 2) ^ 2 := by
        have h_Y_sq_div_self_eq_one : M.Y ^ 2 / M.Y ^ 2 = 1 := by
          have hY_sq_ne_zero : M.Y ^ 2 ≠ 0 := pow_ne_zero 2 (Y_ne_zero M)
          rw [div_self hY_sq_ne_zero]
        nth_rw 1 [← one_mul (1 - M.x ^ 2), ← h_Y_sq_div_self_eq_one]
        rw [mul_div_assoc, ← mul_div_mul_comm, h_Y_sq_mul_one_sub_x_sq_eq]
        rw [h_Y_sq_mul_one_sub_d_mul_x_sq_eq]
        rw [mul_div_mul_comm M.X _ M.X _, div_self (X_ne_zero M), one_mul]
      _ = M.y ^ 2 := by
        rw [← div_pow _ _ 2]
        rfl
  grind

end y

end Cslib.Crypto.Systems.Elligator.Elligator1.OutputCoordinates
