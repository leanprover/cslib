/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Cslib.Crypto.Systems.Elligator.LegendreSymbol

/-!
# Elligator 1 Variables

In this file we introduce all the independent variables introduced in the definition of Elligator 1.

## References

See [bernstein2013a], Section 3.
-/

@[expose] public section

namespace Cslib.Crypto.Systems.Elligator.Elligator1

open Elligator.LegendreSymbol

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- c(s) is a function defined in the paper.

Original:, Section "3.2 The map": Theorem 1
-/
def c (s : F) : F := 2 / s^2

/-- r(s) is a function defined in the paper.

Original:, Section "3.2 The map": Theorem 1
-/
def r (s : F) : F :=
  let c := c s;
  c + 1 / c

/-- d(s) is a function defined in the paper.

Original:, Section "3.2 The map": Theorem 1
-/
def d (s : F) : F :=
  let c := c s;
  -(c + 1)^2 / (c - 1)^2

/-- u(t) is a function defined in the paper.

Original:, Section "3.2 The map": Theorem 1
-/
def u (t : {n : F // n ≠ 1 ∧ n ≠ -1}) : F :=
  let t := t.val;
  (1 - t) / (1 + t)

/-- v(t, s) is a function defined in the paper.

Original:, Section "3.2 The map": Theorem 1
-/
def v (t : {n : F // n ≠ 1 ∧ n ≠ -1}) (s : F) : F :=
  let u := u t
  let r := r s
  u^5 + (r^2 - 2) * u^3 + u

/-- X(t, s) is a function defined in the paper.

Original:, Section "3.2 The map": Theorem 1
-/
def X (t : {n : F // n ≠ 1 ∧ n ≠ -1}) (s : F) : F :=
  let u := u t
  let v := v t s
  (χ v) * u

/-- Y(t, s) is a function defined in the paper.

`q` is still unrelated to the cardinality F here by intention. The theorems using
`Y` will build the necessary context to show useful properties of `Y` by creating
the relation of Field cardinality and `q`.

Original:, Section "3.2 The map": Theorem 1
-/
def Y (t : {n : F // n ≠ 1 ∧ n ≠ -1}) (s : F) (q : ℕ) : F :=
  let u := u t
  let c := c s
  let v := v t s
  ((χ v) * v)^((q + 1) / 4) * (χ v) * χ (u^2 + 1 / c^2)

/-- x(t, s) is a function defined in the paper. It is the x-coordinate of the point on the curve.

Original:, Section "3.2 The map": Theorem 1
-/
def x (t : {n : F // n ≠ 1 ∧ n ≠ -1}) (s : F) (q : ℕ) : F :=
  let c := c s
  let X := X t s
  let Y := Y t s q
  (c - 1) * s * X * (1 + X) / Y

/-- y(t, s) is a function defined in the paper. It is the y-coordinate of the point on the curve.

Original:, Section "3.2 The map": Theorem 1
-/
def y (t : {n : F // n ≠ 1 ∧ n ≠ -1}) (s : F) : F :=
  let r := r s
  let X := X t s
  (r * X - (1 + X)^2) / (r * X + (1 + X)^2)

/-- η(s, q, point) is a function defined in the paper.

Original:, Section "3.3 Inverting the map": Theorem 3
-/
def η (P : F × F) : F :=
  let y := P.snd
  (y - 1) / (2 * (y + 1))

/-- X2 is a function defined in the paper.

Original:, Section "3.3 Inverting the map": Theorem 3
-/
def X2 (s : F) (P : F × F) (q : ℕ) : F :=
  let η := η P
  let r := r s
  (-(1 + η * r) + ((1 + η * r)^2 - 1)^((q + 1) / 4))

/-- z is a function defined in the paper.

Original:, Section "3.3 Inverting the map": Theorem 3
-/
def z (s : F) (P : F × F) (q : ℕ) : F :=
  let x := P.fst
  let c := c s
  let X2 := X2 s P q
  let a := (c - 1) * s * X2 * (1 + X2) * x * (X2^2 + 1 / c^2)
  χ a

/-- u2 is a function defined in the paper.

Original:, Section "3.3 Inverting the map": Theorem 3
-/
def u2 (s : F) (P : F × F) (q : ℕ) : F :=
  let X2 := X2 s P q
  let z := z s P q
  z * X2

/-- t2 is a function defined in the paper.

Original:, Section "3.3 Inverting the map": Theorem 3
-/
def t2 (s : F) (P : F × F) (q : ℕ) : F :=
  let u2 := u2 s P q
  (1 - u2) / (1 + u2)

/-- `b q` is `⌊log₂ q⌋`, the number of bits needed.

Original:, Section "3.4 Encoding as strings": Theorem 4
-/
def b (q : ℕ) : ℕ := Nat.log 2 q

/-- Convert a bit vector (τ₀, τ₁, ..., τ_{b-1}) to a natural number via binary
expansion: bitsToNat(τ) = Σᵢ τᵢ · 2^i.
-/
def bitsToNat {n : ℕ} (τ : Fin n → Bool) : ℕ :=
  ∑ i : Fin n, if τ i then 2^(i : ℕ) else 0

/-- `σ` interprets a bit vector `(τ₀, τ₁, …, τ_{b−1})` as the field element
`∑ᵢ τᵢ · 2ⁱ ∈ Fq`. This is the standard binary-to-integer conversion followed by casting into `F`.

Original:, Section "3.4 Encoding as strings": Theorem 4
-/
def σ {q : ℕ} (τ : Fin (@b q) → Bool) : F := (bitsToNat τ : F)

/-- S = σ⁻¹({0, 1, 2, ..., (q-1)/2}), the set of bit vectors whose binary value
falls in the lower half {0, 1, ..., (q-1)/2} of F_q.

Original:, Section "3.4 Encoding as strings": Theorem 4
-/
def S {q : ℕ} : Finset (Fin (@b q) → Bool) :=
  Finset.univ.filter (fun τ => (bitsToNat τ) ≤ (q - 1) / 2)

end Cslib.Crypto.Systems.Elligator.Elligator1
