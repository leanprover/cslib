/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/

module
public import Mathlib.Algebra.Ring.Commute
public import Mathlib.Data.Set.Defs

/-!
# Twisted Edwards curves

This file contains the curve-level definitions that are independent of any specific Elligator.
A twisted Edwards curve with coefficients `a` and `d` has affine equation
`a * x^2 + y^2 = 1 + d * x^2 * y^2`.

The definitions are made over a commutative ring. Finiteness and the hypotheses used by a
particular cryptographic construction belong in that construction, rather than in the definition
of a curve or its affine points.

Mathlib's elliptic-curve API is currently centred on Weierstrass models. A twisted Edwards model
is not itself a Weierstrass equation, so using `WeierstrassCurve.Affine.Equation` here would require
a birational coordinate conversion and extra invertibility hypotheses.  The API below follows the
same useful separation as that API: coefficients, an affine equation, a set of affine points, and
a bundled point type.
-/

@[expose] public section
namespace Cslib.Crypto.Systems.Elligator

/-- Coefficients of the twisted Edwards equation
`a * x^2 + y^2 = 1 + d * x^2 * y^2`. -/
@[ext]
structure TwistedEdwardsCurve (R : Type*) where
  /-- left hand side coefficient -/
  a : R
  /-- right hand side coefficient -/
  d : R

namespace TwistedEdwardsCurve

variable {R : Type*} [CommRing R]

/-- The proposition that `(x, y)` is an affine point of a twisted Edwards curve. -/
def Equation (E : TwistedEdwardsCurve R) (x y : R) : Prop := E.a * x^2 + y^2 = 1 + E.d * x^2 * y^2

/-- The set of affine coordinate pairs on a twisted Edwards curve. -/
def affinePoints (E : TwistedEdwardsCurve R) : Set (R × R) := {p | E.Equation p.1 p.2}

/-- A bundled affine point on a twisted Edwards curve. -/
abbrev Point (E : TwistedEdwardsCurve R) := {p : R × R // p ∈ E.affinePoints}

/-- The neutral affine coordinate pair `(0, 1)`.  It lies on every twisted Edwards equation. -/
def zero : R × R := (0, 1)

@[simp]
theorem zero_mem_affinePoints (E : TwistedEdwardsCurve R) : zero ∈ E.affinePoints := by
  change E.a * 0^2 + 1^2 = 1 + E.d * 0^2 * 1^2
  simp

/-- The neutral point, bundled as an affine point of `E`. -/
def zeroPoint (E : TwistedEdwardsCurve R) : E.Point := ⟨zero, E.zero_mem_affinePoints⟩

/-- Negation of affine coordinates on a twisted Edwards curve. -/
def neg (p : R × R) : R × R := (-p.1, p.2)

@[simp]
theorem neg_mem_affinePoints (E : TwistedEdwardsCurve R) (p : R × R) :
  neg p ∈ E.affinePoints ↔ p ∈ E.affinePoints := by
    change E.a * (-p.1)^2 + p.2^2 = 1 + E.d * (-p.1)^2 * p.2^2 ↔
      E.a * p.1^2 + p.2^2 = 1 + E.d * p.1^2 * p.2^2
    rw [neg_sq]

/-- The usual coefficient conditions for a nonsingular twisted Edwards model over a field.
Keeping this predicate separate from `TwistedEdwardsCurve` permits the equation and its points to
be used over more general rings and also permits partially specified curves during developments.
-/
def IsValid (E : TwistedEdwardsCurve R) : Prop := E.a ≠ 0 ∧ E.d ≠ 0 ∧ E.a ≠ E.d

/-- The (untwisted) Edwards curve with parameter `d`, obtained by setting `a = 1`. -/
def ofD (d : R) : TwistedEdwardsCurve R where
  a := 1
  d := d

@[simp]
theorem ofD_equation (d x y : R) : (ofD d).Equation x y ↔ x^2 + y^2 = 1 + d * x^2 * y^2 := by
  simp [Equation, ofD]

@[simp]
theorem ofD_isValid_iff [Nontrivial R] (d : R) : (ofD d).IsValid ↔ d ≠ 0 ∧ d ≠ 1 := by
  constructor
  · rintro ⟨_, hd, had⟩
    exact ⟨hd, fun h ↦ had h.symm⟩
  · rintro ⟨hd, hd1⟩
    exact ⟨one_ne_zero, hd, fun h ↦ hd1 h.symm⟩

end TwistedEdwardsCurve
end Cslib.Crypto.Systems.Elligator
