/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/

module

public import Cslib.Crypto.Primitives.ECC.TwistedEdwardsCurve

/-!
# Complete Edwards curves

This file develops the (untwisted) Edwards curve
`x ^ 2 + y ^ 2 = 1 + d * x ^ 2 * y ^ 2`
as the `a = 1` specialization of `Elligator.TwistedEdwardsCurve`.

Everything here is stated over an arbitrary commutative ring and for an arbitrary coefficient `d`.
No finite field, and no cardinality assumption.

## Main definitions

* `edwardsCurve d`: the Edwards curve with coefficient `d`.
* `edwardsCurveEquation x y d`: the Edwards curve equation for a coefficient `d ∉ {0, 1}`, packaged
  as a subtype argument.

## Main results

* `edwardsCurve_equation_iff`, `edwardsCurveEquation_iff`: unfolding lemmas for the equation.
* `edwardsCurve_isValid_iff`: `edwardsCurve d` is a valid model iff `d ≠ 0` and `d ≠ 1`.
* `edwardsCurveEquation_zero_one`: the neutral point `(0, 1)` lies on every Edwards curve.
-/

@[expose] public section

namespace Cslib.Crypto.Primitives.ECC

variable {R : Type*} [CommRing R]

/-- The Edwards curve with coefficient `d`.
This is an alias for the `a = 1` specialization of a twisted Edwards curve. -/
def edwardsCurve (d : R) : TwistedEdwardsCurve R := TwistedEdwardsCurve.ofD d

@[simp]
theorem edwardsCurve_equation_iff (d x y : R) :
    (edwardsCurve d).Equation x y ↔ x ^ 2 + y ^ 2 = 1 + d * x ^ 2 * y ^ 2 := by
  simp [edwardsCurve]

@[simp]
theorem edwardsCurve_isValid_iff [Nontrivial R] (d : R) :
    (edwardsCurve d).IsValid ↔ d ≠ 0 ∧ d ≠ 1 := by
  simp [edwardsCurve]

/-- `edwardsCurveEquation` is the standard Edwards curve equation, with the coefficient carried as
a subtype element recording `d ≠ 0` and `d ≠ 1`.  New generic developments should normally use
`(edwardsCurve d).Equation x y` and carry coefficient validity separately via
`TwistedEdwardsCurve.IsValid`; see `edwardsCurve_isValid_iff`.
-/
def edwardsCurveEquation (x y : R) (d : {d : R // d ≠ 0 ∧ d ≠ 1}) : Prop :=
  (edwardsCurve d.val).Equation x y

@[simp]
theorem edwardsCurveEquation_iff (x y : R) (d : {d : R // d ≠ 0 ∧ d ≠ 1}) :
    edwardsCurveEquation x y d ↔ x ^ 2 + y ^ 2 = 1 + d * x ^ 2 * y ^ 2 := by
  simp [edwardsCurveEquation]

/-- The set of affine points of the Edwards curve with coefficient `d`. -/
theorem edwardsCurve_affinePoints (d : R) :
    (edwardsCurve d).affinePoints =
      {p : R × R | p.1 ^ 2 + p.2 ^ 2 = 1 + d * p.1 ^ 2 * p.2 ^ 2} := by
  ext p
  simp [TwistedEdwardsCurve.affinePoints]

lemma edwardsCurveEquation_zero_one (d : {d : R // d ≠ 0 ∧ d ≠ 1}) :
    edwardsCurveEquation (0 : R) (1 : R) d := by
  simp

end Cslib.Crypto.Primitives.ECC
