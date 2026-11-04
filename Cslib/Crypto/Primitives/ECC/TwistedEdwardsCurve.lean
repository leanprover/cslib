/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/

module

public import Cslib.Init
public import Mathlib.Algebra.Ring.Commute
public import Mathlib.Data.Set.Defs

/-!
# Twisted Edwards curves

This file contains the curve-level definitions that are independent of any specific Elligator.
A twisted Edwards curve with coefficients `a` and `d` has affine equation
`a * x ^ 2 + y ^ 2 = 1 + d * x ^ 2 * y ^ 2`.

The definitions are made over a commutative ring. Finiteness and the hypotheses used by a
particular cryptographic construction belong in that construction, rather than in the definition
of a curve or its affine points.

Mathlib's elliptic-curve API is currently centred on Weierstrass models. A twisted Edwards model
is not itself a Weierstrass equation, so using `WeierstrassCurve.Affine.Equation` here would require
a birational coordinate conversion and extra invertibility hypotheses.  The API below follows the
same useful separation as that API: coefficients, an affine equation and a set of affine
points.

## Main definitions

* `TwistedEdwardsCurve`: the coefficients `a`, `d` of a twisted Edwards model, with its equation
  `TwistedEdwardsCurve.Equation`, its affine points `TwistedEdwardsCurve.affinePoints` and the
  nonsingularity condition `TwistedEdwardsCurve.IsValid`.
* `edwardsCurve d`: the untwisted Edwards curve `x ^ 2 + y ^ 2 = 1 + d * x ^ 2 * y ^ 2`.

## TODO

- Move into mathlib next to Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

## References

* [Bernstein2007a], Section 2.
* [Bernstein2008a], Section 2, Definition 2.1.

-/

@[expose] public section
namespace Cslib.Crypto.Primitives.ECC

/-- Coefficients of the twisted Edwards equation
`a * x ^ 2 + y ^ 2 = 1 + d * x ^ 2 * y ^ 2`. -/
@[ext]
structure TwistedEdwardsCurve (R : Type*) where
  /-- left hand side coefficient -/
  a : R
  /-- right hand side coefficient -/
  d : R

variable {R : Type*} [CommRing R]

namespace TwistedEdwardsCurve

/-- The proposition that `(x, y)` is an affine point of a twisted Edwards curve. -/
def Equation (E : TwistedEdwardsCurve R) (x y : R) : Prop :=
    E.a * x ^ 2 + y ^ 2 = 1 + E.d * x ^ 2 * y ^ 2

/-- The set of affine coordinate pairs on a twisted Edwards curve. -/
def affinePoints (E : TwistedEdwardsCurve R) : Set (R × R) := {p | E.Equation p.1 p.2}

/-- The neutral point `(0, 1)` lies on every twisted Edwards curve. -/
lemma zero_mem_affinePoints (E : TwistedEdwardsCurve R) : (0, 1) ∈ E.affinePoints := by
  change E.a * 0 ^ 2 + 1 ^ 2 = 1 + E.d * 0 ^ 2 * 1 ^ 2
  simp

/-- The coefficient conditions under which a twisted Edwards model is nonsingular: `2`, `a`, `d`
and `a - d` are units. Over a field this is [Bernstein2008a], Definition 2.1: the characteristic is
not `2` and `a`, `d` are distinct and nonzero. As in Mathlib's `WeierstrassCurve.IsElliptic`, units
rather than nonzero elements keep the condition meaningful over rings. Keeping this predicate
separate from `TwistedEdwardsCurve` permits the equation and its points to be used without it. -/
def IsValid (E : TwistedEdwardsCurve R) : Prop :=
  IsUnit (2 : R) ∧ IsUnit E.a ∧ IsUnit E.d ∧ IsUnit (E.a - E.d)

end TwistedEdwardsCurve

/-- The (untwisted) Edwards curve with coefficient `d`, obtained by setting `a = 1`. -/
def edwardsCurve (d : R) : TwistedEdwardsCurve R where
  a := 1
  d := d

/-- The equation of `edwardsCurve d`, written out. -/
lemma edwardsCurve_equation_iff (d x y : R) :
    (edwardsCurve d).Equation x y ↔ x ^ 2 + y ^ 2 = 1 + d * x ^ 2 * y ^ 2 := by
  simp [TwistedEdwardsCurve.Equation, edwardsCurve]

/-- `edwardsCurve d` is valid exactly when `2`, `d` and `1 - d` are units. -/
lemma edwardsCurve_isValid_iff (d : R) :
    (edwardsCurve d).IsValid ↔ IsUnit (2 : R) ∧ IsUnit d ∧ IsUnit (1 - d) := by
  simp [TwistedEdwardsCurve.IsValid, edwardsCurve]

end Cslib.Crypto.Primitives.ECC
