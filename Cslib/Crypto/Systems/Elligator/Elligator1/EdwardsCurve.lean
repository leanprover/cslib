/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Cslib.Crypto.Primitives.ECC.TwistedEdwardsCurve
public import Cslib.Crypto.Systems.Elligator.Elligator1.CurveParameters

/-!
# The Edwards curve used by Elligator 1

This file specializes the general Edwards curve API of `Elligator.Primitives.ECC.EdwardsCurve` to
the curve and coefficient produced by Cslib.Crypto.Systems.Elligator 1.

## Main results

* `curve`: the Edwards curve with the paper's coefficient `d(s)`.
* `curve_isValid`: the Elligator hypotheses imply that `d(s)` is a valid Edwards coefficient.
* `EOverF s`: the set of affine field-valued points satisfying the Elligator 1 curve equation.
* `EOverF s_eq_affinePoints`: `EOverF s` agrees with the general Edwards affine-point set.

## References

See [Bernstein2013a], Section 3.
-/

@[expose] public section

namespace Cslib.Crypto.Systems.Elligator.Elligator1

open Cslib.Crypto.Primitives.ECC
open Cslib.Crypto.Systems.Elligator.Elligator1.CurveParameters

variable {F : Type*} [Field F]
variable (D : ParamData F)

/-- The Edwards curve selected by the Elligator 1 parameter `s`. -/
def curve (s : F) : TwistedEdwardsCurve F := edwardsCurve (d s)

def _root_.Cslib.Crypto.Systems.Elligator.ParamData.curve : TwistedEdwardsCurve F :=
    Elligator1.curve D.s

/-- The curve equation of the Elligator 1 curve, in explicit form. -/
lemma curve_equation_iff (x y : F) :
    D.curve.Equation x y ↔ x ^ 2 + y ^ 2 = 1 + D.d * x ^ 2 * y ^ 2 :=
  edwardsCurve_equation_iff D.d x y

/-- The Elligator 1 coefficient hypotheses imply that its specialized curve is valid. -/
lemma curve_isValid [Fintype F] [IsRegularParam D.s] [IsCardThreeModFour F] :
    D.curve.IsValid := by
  unfold ParamData.curve curve
  rw [edwardsCurve_isValid_iff]
  exact d_ne_zero_and_d_ne_one D

/-- `EOverF s` is the set of affine points on the Edwards curve selected by Elligator 1. -/
def EOverF (s : F) : Set (F × F) := (curve s).affinePoints

def _root_.Cslib.Crypto.Systems.Elligator.ParamData.EOverF : Set (F × F) :=
    Elligator1.EOverF D.s

/-- The compatibility set `EOverF s` is exactly the affine point set of the general curve model. -/
lemma EOverF_s_eq_affinePoints : D.EOverF = D.curve.affinePoints := by rfl

/-- Membership in `EOverF s`, written out as the Edwards curve equation. -/
lemma mem_EOverF_iff (p : F × F) :
    p ∈ D.EOverF ↔ p.1 ^ 2 + p.2 ^ 2 = 1 + D.d * p.1 ^ 2 * p.2 ^ 2 :=
  curve_equation_iff D p.1 p.2

/-- The neutral point `(0, 1)` lies in `EOverF s`. -/
lemma zero_mem_EOverF : ((0 : F), (1 : F)) ∈ D.EOverF := D.curve.zero_mem_affinePoints

end Cslib.Crypto.Systems.Elligator.Elligator1
