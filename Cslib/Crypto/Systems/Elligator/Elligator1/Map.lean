/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Cslib.Crypto.Systems.Elligator.Elligator1.Variables
public import Cslib.Crypto.Systems.Elligator.Elligator1.sProperties
public import Cslib.Crypto.Systems.Elligator.Elligator1.cProperties
public import Cslib.Crypto.Systems.Elligator.Elligator1.dProperties
public import Cslib.Crypto.Systems.Elligator.Elligator1.EdwardsCurve
public import Cslib.Crypto.Systems.Elligator.Elligator1.uProperties
public import Cslib.Crypto.Systems.Elligator.Elligator1.vProperties
public import Cslib.Crypto.Systems.Elligator.Elligator1.XProperties
public import Cslib.Crypto.Systems.Elligator.Elligator1.YProperties
public import Cslib.Crypto.Systems.Elligator.Elligator1.xProperties
public import Cslib.Crypto.Systems.Elligator.Elligator1.yProperties

/-!
# Map

This file formalizes the construction and well-definedness results in Theorem 1 of the Elligator
paper. For a field input `t ≠ ±1`, the auxiliary quantities `u`, `v`, `X`, and `Y` determine a
point `(x, y)` on the complete Edwards curve. The exceptional inputs `t = ±1` are incorporated by
`ϕ`, which sends both to `(0, 1)`.

## Main results

* `u_defined`, `Y_defined`, `x_defined`, `y_defined`: the denominators in the paper's formulas
  are nonzero, so the displayed expressions are defined.
* `map_fulfills_helper_equation`: the auxiliary coordinates satisfy `Y² = X⁵ + (r² - 2)X³ + X`.
* `variable_mul_ne_zero`: the nonvanishing assertion `u * v * X * Y * x * (y + 1) ≠ 0`
  from Theorem 1.
* `map_fulfills_curve_equation`: the resulting `(x, y)` satisfies the Edwards curve equation.
* `ϕ`: Definition 2's total map from field elements to points on the Edwards curve.

## References

See [bernstein2013a], Section 3.2, Theorem 1 and Definition 2.
-/

@[expose] public section

namespace Cslib.Crypto.Systems.Elligator.Elligator1

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {s : F}
variable {q : ℕ}

omit [Fintype F] [DecidableEq F] in
theorem u_defined (t : {t : F // t ≠ 1 ∧ t ≠ -1}) : 1 + t.val ≠ 0 :=
  FiniteFieldBasic.one_add_t_ne_zero t

omit [DecidableEq F] in
theorem Y_defined (hs_ne_zero : s ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    (c s) ^ 2 ≠ 0 :=
  pow_ne_zero 2 (c_ne_zero hs_ne_zero hq_card hq_mod)

theorem x_defined (t : {t : F // t ≠ 1 ∧ t ≠ -1}) (hs_ne_zero : s ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    (Y t s q) ≠ 0 :=
  Y_ne_zero hs_ne_zero hq_card hq_mod t

theorem y_defined (t : {t : F // t ≠ 1 ∧ t ≠ -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    ((r s) * (X t s) + (1 + (X t s)) ^ 2) ≠ 0 :=
  y_divisor_ne_zero hs_ne_zero sq_ne_pm_two hq_card hq_mod t

/-- The auxiliary coordinates `X` and `Y` satisfy the hyperelliptic equation used in Theorem 1:
`Y² = X⁵ + (r² - 2)X³ + X`. -/
theorem map_fulfills_auxiliary_equation (t : {n : F // n ≠ 1 ∧ n ≠ -1}) (hs_ne_zero : s ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let r := r s
    let X := X t s
    let Y := Y t s q
    Y ^ 2 = X ^ 5 + (r ^ 2 - 2) * X ^ 3 + X :=
  helper_eq t hs_ne_zero hq_card hq_mod

/-- The quantities constructed for a nonexceptional input are all nonzero as asserted in
Theorem 1: `u * v * X * Y * x * (y + 1) ≠ 0`. -/
theorem variable_mul_ne_zero (t : {n : F // n ≠ 1 ∧ n ≠ -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let u := u t
    let v := v t s
    let X := X t s
    let Y := Y t s q
    let x := x t s q
    let y := y t s
    u * v * X  * Y * x * (y + 1) ≠ 0 :=
  variable_mul_ne_zero' t hs_ne_zero sq_ne_pm_two hq_card hq_mod

/-- The coordinates produced from a nonexceptional input satisfy the Edwards curve equation
`x² + y² = 1 + d * x² * y²`. This is the final conclusion of Theorem 1. -/
theorem map_fulfills_curve_equation (t : {n : F // n ≠ 1 ∧ n ≠ -1})
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let x := x t s q
    let y := y t s
    let d := d s
    have d_h : d ≠ 0 ∧ d ≠ 1 := d_ne_zero_and_d_ne_one sq_ne_pm_two hq_card hq_mod
    edwardsCurveEquation x y ⟨d, d_h⟩ := by
  intro x_of_t y_of_t d_of_s
  rw [edwardsCurveEquation_iff]
  exact curve_equation t hs_ne_zero sq_ne_pm_two hq_card hq_mod

/-- The total Elligator map `ϕ : F → E(F)` from Definition 2 of the paper.

For `t ≠ ±1`, it returns the coordinates `x(t)` and `y(t)` constructed in Theorem 1. The two
exceptional inputs `t = ±1` are both mapped to the neutral point `(0, 1)`. The codomain subtype
records that the result satisfies the Edwards curve equation. -/
def ϕ (t : F) (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    EOverF sq_ne_pm_two hq_card hq_mod :=
  let P := if h : t ≠ 1 ∧ t ≠ -1 then (x ⟨t, h⟩ s q, y ⟨t, h⟩ s) else (0, 1)
  have P_in_EOverF : P ∈ (EOverF sq_ne_pm_two hq_card hq_mod) := by
    unfold EOverF
    rw [Set.mem_ofPred_eq]
    unfold P
    by_cases ht : t ≠ 1 ∧ t ≠ -1
    · rw [dite_eq_left ht]
      exact map_fulfills_curve_equation ⟨t, ht⟩ hs_ne_zero sq_ne_pm_two hq_card hq_mod
    · rw [dite_eq_right ht]
      simp
  ⟨P, P_in_EOverF⟩

end Cslib.Crypto.Systems.Elligator.Elligator1
