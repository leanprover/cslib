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

/-!
# X Variable Properties

In this file we introduce some generally helpful lemmas for `X` as introduced in
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

lemma X_pow_two_add_one_div_c_pow_two_ne_zero (hs_ne_zero : s ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (t : {n : F // n ≠ 1 ∧ n ≠ -1}) :
    (X t s) ^ 2 + 1 / (c s) ^ 2 ≠ 0 := by
  let X := X t s
  let c := c s
  intro h_sum_eq_zero
  have h_cleared : X ^ 2 * c ^ 2 + c⁻¹^2 * c ^ 2 = 0 := by grind
  have h_prod_eq_neg_one : X ^ 2 * c ^ 2 = -1 := by grind [c_ne_zero]
  have h_not_isSquare : ¬IsSquare (-1 : F) := neg_one_non_square hq_card hq_mod
  have h_isSquare : IsSquare (-1 : F) := by
    rw [← h_prod_eq_neg_one, ← mul_pow]
    apply IsSquare.sq (X * c)
  contradiction

lemma X_ne_zero (hs_ne_zero : s ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
    (t : {n : F // n ≠ 1 ∧ n ≠ -1}) :
    (X t s) ≠ 0 := by
  apply mul_ne_zero
  · apply χ_a_ne_zero (v_ne_zero hs_ne_zero hq_card hq_mod t)
  · apply u_ne_zero t

lemma X_comparison (t : {n : F // n ≠ 1 ∧ n ≠ -1}) :
    let t1 := t.val
    let t2 := -t1
    let X1 := X t s
    let Xbar := X ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s
    Xbar = 1 / X1 := by
  intro t1 t2 X1 Xbar
  let u1 := u t
  let ubar := u ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩
  let v1 := v t s
  let v2 := v ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s
  calc
    Xbar = (χ v2) * ubar := by rfl
    _ = (χ v1) / u1 := by
      unfold v2 t2
      rw [v_comparison_implication4 t]
      unfold ubar
      rw [u_comparison t]
      change (χ v1) * (1 / u1) = (χ v1) / u1
      ring
    _ = 1 / ((χ v1) * u1) := by
      nth_rw 1 [one_div_χ_of_a_eq_χ_a]
      ring
    _ = 1 / X1 := by rfl

@[simp]
lemma X_of_zero (hs_ne_zero : s ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let X := X ⟨(0 : F), by simp⟩ s
    X = 1 := by
  intro X
  unfold X Elligator1.X
  let χ_of_v := χ (v ⟨(0 : F), by simp⟩ s)
  rw [u_of_zero]
  change χ_of_v * 1 = 1
  unfold χ_of_v
  rw [v_of_zero]
  rw [χ_sq (r_ne_zero hs_ne_zero hq_card hq_mod), mul_one]

end Cslib.Crypto.Systems.Elligator.Elligator1
