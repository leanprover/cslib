/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Cslib.Crypto.Systems.Elligator.Elligator1.Variables
public import Cslib.Crypto.Systems.Elligator.Elligator1.sProperties
public import Cslib.Crypto.Systems.Elligator.Elligator1.cProperties
public import Cslib.Crypto.Systems.Elligator.Elligator1.EdwardsCurve
public import Cslib.Crypto.Systems.Elligator.Elligator1.uProperties
public import Cslib.Crypto.Systems.Elligator.Elligator1.vProperties
public import Cslib.Crypto.Systems.Elligator.Elligator1.XProperties
public import Cslib.Crypto.Systems.Elligator.Elligator1.YProperties

/-!
# x Variable Properties

In this file we introduce some generally helpful lemmas for `x` as introduced in
`Cslib.Crypto.Systems.Elligator.Elligator1.Variables`.

## References

See [bernstein2013a], Section 3.2, Theorem 1.
-/

@[expose] public section

namespace Cslib.Crypto.Systems.Elligator.Elligator1

open Elligator.FiniteFieldBasic

variable {F : Type*} [Field F] [Fintype F]
variable {s : F}
variable {q : ℕ}

lemma x_ne_zero
  [DecidableEq F]
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  :
  let x := x t s q
  x ≠ 0 := by
    let c := c s
    let X := X t s
    let Y := Y t s q
    change (c - 1) * s * X * (1 + X) / Y ≠ 0
    apply div_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · apply mul_ne_zero
          · intro hc_eq_one
            have hc_eq_one' : c = 1 := by grind
            exact (c_ne_one sq_ne_pm_two) hc_eq_one'
          · apply hs_ne_zero
        · apply X_ne_zero hs_ne_zero hq_card hq_mod t
      · apply one_add_X_ne_zero hs_ne_zero hq_card hq_mod t
    · apply Y_ne_zero hs_ne_zero hq_card hq_mod t

lemma x_comparison
  [DecidableEq F]
  (t : { t : F // t ≠ 1 ∧ t ≠ -1})
  (hs_ne_zero : s ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  :
  let t1 := t.val
  let t2 := -t1
  let x1 := x t s q
  let x2 := x ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩ s q
  x2 = x1 := by
    intro t1 t2 x1 x2
    let c := c s
    let t_h := neg_t_ne_one_and_neg_t_ne_neg_one t
    let X1 := X t s
    let X2 := X ⟨t2, t_h⟩ s
    let Y1 := Y t s q
    let Y2 := Y ⟨t2, t_h⟩ s q
    have hX1_pow3_ne_zero : X1^3 ≠ 0 := pow_ne_zero 3 (X_ne_zero hs_ne_zero hq_card hq_mod t)
    calc
      x2 = (c - 1) * s * X2 * (1 + X2) / Y2 := by rfl
      _ = (c - 1) * s * 1 / X1 * (1 + 1 / X1) / (Y1 / X1^3) := by grind [X_comparison, Y_comparison]
      _ = (c - 1) * s * X1 * (1 + X1) / Y1 := by simp_all; grind
      _ = x1 := by rfl

lemma x_y_eq_zero_sign_one
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  (P : {P : F × F // P ∈ EOverF sq_ne_pm_two hq_card hq_mod})
  (hx_eq_zero : P.val.1 = 0)
  : P.val = ((0 : F), (1 : F)) ∨ P.val = ((0 : F), (-1 : F)) := by
    let d := d s
    let x := P.val.1
    let y := P.val.2
    unfold EOverF at P
    change (x, y) = (0, 1) ∨ (x, y) = (0, -1)
    change x = 0 at hx_eq_zero
    rw [← hx_eq_zero]
    have h_curve_eq : x^2 + y^2 = 1 + d * x^2 * y^2 := by
      let hP := P.prop
      simp only [edwardsCurveEquation_iff] at hP
      exact hP
    have hy_eq_pm_one : y = 1 ∨ y = -1 := by grind
    rcases hy_eq_pm_one with h | h
    · rw [← h]; left; rfl
    · rw [← h]; right; rfl

end Cslib.Crypto.Systems.Elligator.Elligator1
