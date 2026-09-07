/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Cslib.Crypto.Systems.Elligator.Elligator1.OutputCoordinates

/-!
# Map

This file formalizes the construction and well-definedness results in Theorem 1 of the Elligator
paper. For a field input `t ≠ ±1`, the auxiliary quantities `u`, `v`, `X`, and `Y` determine a
point `(x, y)` on the complete Edwards curve. The exceptional inputs `t = ±1` are incorporated by
`ϕ`, which sends both to `(0, 1)`.

## Main results

* `u_defined`, `Y_defined`, `x_defined`, `y_defined`: the denominators in the paper's formulas
  are nonzero, so the displayed expressions are defined.
* `map_fulfills_curve_equation`: the resulting `(x, y)` satisfies the Edwards curve equation.
* `ϕ`: Definition 2's total map from field elements to points on the Edwards curve.

## References

See [Bernstein2013a], Section 3.2, Theorem 1 and Definition 2.
-/

@[expose] public section

namespace Cslib.Crypto.Systems.Elligator.Elligator1

open Cslib.Crypto.Primitives.ECC
open Cslib.Crypto.Systems.Elligator.Elligator1.CurveParameters
open Cslib.Crypto.Systems.Elligator.Elligator1.AuxiliaryCoordinates
open Cslib.Crypto.Systems.Elligator.Elligator1.OutputCoordinates

variable {F : Type*} [Field F]
variable (D : ParamData F)
variable (I : InputData F)
variable (M : MapData F)

theorem u_defined : 1 + I.t ≠ 0 := FiniteFieldBasic.one_add_t_ne_zero I.tSub

variable [Fintype F]

theorem Y_defined [IsNonzeroParam D.s] [IsCardThreeModFour F] : D.c ^ 2 ≠ 0 :=
  pow_ne_zero 2 (c_ne_zero D)

variable [DecidableEq F]

theorem x_defined [IsNonzeroParam M.s] [IsCardThreeModFour F] : M.Y ≠ 0 := Y_ne_zero M

theorem y_defined [IsNonzeroParam M.s] [IsRegularParam M.s] [IsCardThreeModFour F] :
    (M.r * M.X + (1 + M.X) ^ 2) ≠ 0 :=
  y_divisor_ne_zero M

/-- The coordinates produced from a nonexceptional input satisfy the Edwards curve equation
`x² + y² = 1 + d * x² * y²`. This is the final conclusion of Theorem 1. -/
theorem map_fulfills_curve_equation
    [IsNonzeroParam M.s] [IsRegularParam M.s] [IsCardThreeModFour F] :
    M.curve.Equation M.x M.y := by
  rw [curve_equation_iff]
  exact curve_equation M

/-- The total Elligator map `ϕ : F → E(F)` from Definition 2 of the paper.

For `t ≠ ±1`, it returns the coordinates `x(t)` and `y(t)` constructed in Theorem 1. The two
exceptional inputs `t = ±1` are both mapped to the neutral point `(0, 1)`. The codomain subtype
records that the result satisfies the Edwards curve equation. -/
def ϕ (t : F) {s : F}
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_mod : Fintype.card F % 4 = 3) : EOverF s :=
  haveI : IsNonzeroParam s := ⟨hs_ne_zero⟩
  haveI : IsRegularParam s := ⟨sq_ne_pm_two⟩
  haveI : IsCardThreeModFour F := ⟨hq_mod⟩
  let D : ParamData F := ⟨s⟩
  let P := if h : t ≠ 1 ∧ t ≠ -1 then (x ⟨t, h⟩ s (Fintype.card F), y ⟨t, h⟩ s) else (0, 1)
  have P_in_EOverF : P ∈ D.EOverF := by
    rw [mem_EOverF_iff, ← curve_equation_iff]
    unfold P
    by_cases ht : t ≠ 1 ∧ t ≠ -1
    · rw [dite_eq_left ht]
      exact map_fulfills_curve_equation
        {s := s, t := t, t_ne_one := ht.1, t_ne_neg_one := ht.2}
    · rw [dite_eq_right ht]
      exact (curve s).zero_mem_affinePoints
  ⟨P, P_in_EOverF⟩

/-- ParamData wrapper for ϕ. -/
def _root_.Cslib.Crypto.Systems.Elligator.ParamData.ϕ
    [IsNonzeroParam D.s] [IsRegularParam D.s] [IsCardThreeModFour F] (t : F) :
    {P : F × F // P ∈ D.EOverF} :=
  Elligator1.ϕ t s_ne_zero s_sq_ne_pm_two card_mod_four

end Cslib.Crypto.Systems.Elligator.Elligator1
