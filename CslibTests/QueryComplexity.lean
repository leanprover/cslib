/-
Copyright (c) 2026 Vignesh Karri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vignesh Karri
-/

import Cslib.Computability.QueryComplexity.Measures
import Mathlib.Data.Fin.VecNotation

/-! # Query complexity tests

Worked examples of `s(f)`, `bs(f)`, `C(f)` and `D(f)` on some standard Boolean
functions.

`s`, `bs`, and `C` are all decidable and `D(f)` is not. We have proved the chain
`s ≤ bs ≤ C ≤ D`.
-/

namespace CslibTests.QueryComplexity

open Cslib.QueryComplexity

/-! ## The functions -/

/-- `OR` of `n` bits. -/
def orF (n : ℕ) : BoolFunc n := fun x => (List.ofFn x).any id

/-- `AND` of `n` bits. -/
def andF (n : ℕ) : BoolFunc n := fun x => (List.ofFn x).all id

/-- `PARITY` of `n` bits. -/
def parityF (n : ℕ) : BoolFunc n := fun x => (List.ofFn x).foldr xor false

/-- `MAJ` on three bits: at least two of the three inputs are `true`. -/
def maj3 : BoolFunc 3 := fun x => (x 0 && x 1) || (x 1 && x 2) || (x 0 && x 2)

example : orF 3 ![false, false, false] = false := rfl
example : orF 3 ![false, true, false] = true := rfl
example : andF 3 ![true, true, true] = true := rfl
example : andF 3 ![true, false, true] = false := rfl
example : parityF 3 ![true, true, true] = true := rfl
example : parityF 3 ![true, true, false] = false := rfl
example : maj3 ![true, true, false] = true := rfl
example : maj3 ![true, false, false] = false := rfl

/-! ## OR
Every coordinate is sensitive at the all zeroes input, so `s=n`, hence
`D=n` since `s(f) ≤ D(f)`. This also implies `OR` has all four measures equal to `n`.
-/

example : sensitivity (orF 2) = 2 := by decide
example : blockSensitivity (orF 2) = 2 := by decide
example : certificateComplexity (orF 2) = 2 := by decide

example : sensitivity (orF 3) = 3 := by decide
example : blockSensitivity (orF 3) = 3 := by decide
example : certificateComplexity (orF 3) = 3 := by decide

/-- A single `true` bit is a certificate for `OR`. -/
example : pointCertificateComplexity (orF 3) ![true, true, true] = 1 := by decide

/-- The size of the smallest certificate at the all zeroes input is the size of the
whole string. -/
example : pointCertificateComplexity (orF 3) ![false, false, false] = 3 := by decide

/-! ## AND

The all-`true` input is sensitive
-/

example : sensitivity (andF 3) = 3 := by decide
example : blockSensitivity (andF 3) = 3 := by decide
example : certificateComplexity (andF 3) = 3 := by decide

/-! ## PARITY

Every coordinate is sensitive at every input, which is the extreme case.
-/

example : sensitivity (parityF 2) = 2 := by decide
example : blockSensitivity (parityF 2) = 2 := by decide
example : certificateComplexity (parityF 2) = 2 := by decide

example : sensitivity (parityF 3) = 3 := by decide
example : blockSensitivity (parityF 3) = 3 := by decide
example : certificateComplexity (parityF 3) = 3 := by decide

/-- No short certificate at any input. -/
example : pointCertificateComplexity (parityF 3) ![true, true, true] = 3 := by decide

/-! ## MAJ₃

Here the measures come apart: `s = bs = C = 2`, `D = 3`.
-/

example : sensitivity maj3 = 2 := by decide
example : blockSensitivity maj3 = 2 := by decide
example : certificateComplexity maj3 = 2 := by decide

/-- An all-`true` has no sensitive bits. -/
example : pointSensitivity maj3 ![true, true, true] = 0 := by decide

/-- A split input is sensitive in the two agreeing coordinates, but not the third. -/
example : sensitiveCoords maj3 ![true, true, false] = {0, 1} := by decide

/-- Two agreeing bits are a certificate, so `C(f, x) = 2` everywhere. -/
example : pointCertificateComplexity maj3 ![true, true, false] = 2 := by decide

/-! ## Constant functions

No bit is sensitive. The empty assignment is a certificate and the trivial tree computes
the function.
-/

example : sensitivity (fun _ => true : BoolFunc 3) = 0 := by decide
example : blockSensitivity (fun _ => true : BoolFunc 3) = 0 := by decide
example : certificateComplexity (fun _ => true : BoolFunc 3) = 0 := by decide

end CslibTests.QueryComplexity
