/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Cslib.Crypto.Primitives.ECC.TwistedEdwardsCurve
public import Cslib.Crypto.Systems.Elligator.Elligator1.CurveParameters

/-!
# The Edwards curve used by Cslib.Crypto.Systems.Elligator 1

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
variable {q : ℕ}

/-- The Edwards curve selected by the Cslib.Crypto.Systems.Elligator 1 parameter `s`. -/
def curve (s : F) : TwistedEdwardsCurve F := edwardsCurve (d s)

/-- The curve equation of the Cslib.Crypto.Systems.Elligator 1 curve, in explicit form. -/
lemma curve_equation_iff (s x y : F) :
    (curve s).Equation x y ↔ x ^ 2 + y ^ 2 = 1 + d s * x ^ 2 * y ^ 2 :=
  edwardsCurve_equation_iff (d s) x y

/-- The Elligator 1 coefficient hypotheses imply that its specialized curve is valid. -/
lemma curve_isValid [Fintype F]
    {s : F}
    (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    (curve s).IsValid := by
  rw [curve, edwardsCurve_isValid_iff]
  exact d_ne_zero_and_d_ne_one sq_ne_pm_two hq_card hq_mod

/-- `EOverF s` is the set of affine points on the Edwards curve selected by Elligator 1. -/
def EOverF (s : F) : Set (F × F) := (curve s).affinePoints

/-- The compatibility set `EOverF s` is exactly the affine point set of the general curve model. -/
lemma EOverF_s_eq_affinePoints {s : F} :
    EOverF s = (curve s).affinePoints := by
  rfl

/-- Membership in `EOverF s`, written out as the Edwards curve equation. -/
lemma mem_EOverF_iff {s : F} (p : F × F) :
    p ∈ EOverF s ↔ p.1 ^ 2 + p.2 ^ 2 = 1 + d s * p.1 ^ 2 * p.2 ^ 2 :=
  curve_equation_iff s p.1 p.2

/-- The neutral point `(0, 1)` lies in `EOverF s`; a specialization of
`Elligator.edwardsCurveEquation_zero_one`. -/
lemma zero_mem_EOverF {s : F} :
    ((0 : F), (1 : F)) ∈ EOverF s :=
  (curve s).zero_mem_affinePoints

end Cslib.Crypto.Systems.Elligator.Elligator1
