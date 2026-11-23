/-
Copyright (c) 2026 Vignesh Karri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vignesh Karri
-/

import Cslib.Computability.QueryComplexity.DecisionTree
import Mathlib.Data.Fin.VecNotation

/-! # Query complexity tests

Worked examples of `s(f)`, `bs(f)`, `C(f)` and `D(f)` on some standard Boolean functions. The
first three are decidable, so their values are checked by `decide`. `D(f)` is not, so its values
come from the chain `s(f, x) ≤ s(f) ≤ bs(f) ≤ C(f) ≤ D(f) ≤ n`: an input sensitive to every
coordinate forces `D(f) = n`.
-/

namespace CslibTests.QueryComplexity

open Cslib Cslib.BitString Cslib.QueryComplexity

/-! ## The functions -/

/-- `OR` of `n` bits. -/
def orF (n : ℕ) : BooleanFunction n := fun x => (List.ofFn x).any id

/-- `AND` of `n` bits. -/
def andF (n : ℕ) : BooleanFunction n := fun x => (List.ofFn x).all id

/-- `PARITY` of `n` bits. -/
def parityF (n : ℕ) : BooleanFunction n := fun x => (List.ofFn x).foldr xor false

/-- `MAJ` on three bits: at least two of the three inputs are `true`. -/
def maj3 : BooleanFunction 3 := fun x => (x 0 && x 1) || (x 1 && x 2) || (x 0 && x 2)

example : orF 3 ![false, false, false] = false := rfl
example : orF 3 ![false, true, false] = true := rfl
example : andF 3 ![true, true, true] = true := rfl
example : andF 3 ![true, false, true] = false := rfl
example : parityF 3 ![true, true, true] = true := rfl
example : parityF 3 ![true, true, false] = false := rfl
example : maj3 ![true, true, false] = true := rfl
example : maj3 ![true, false, false] = false := rfl

/-! ## OR

Every coordinate is sensitive at the all-zeroes input, so `s = n`, and `s ≤ bs ≤ C ≤ D ≤ n`
forces all four measures to equal `n`.
-/

example : sensitivity (orF 2) = 2 := by decide
example : blockSensitivity (orF 2) = 2 := by decide
example : certificateComplexity (orF 2) = 2 := by decide

example : sensitivity (orF 3) = 3 := by decide
example : blockSensitivity (orF 3) = 3 := by decide
example : certificateComplexity (orF 3) = 3 := by decide

/-- A single `true` bit is a certificate for `OR`. -/
example : certificateComplexityAt (orF 3) ![true, true, true] = 1 := by decide

/-- The size of the smallest certificate at the all zeroes input is the size of the
whole string. -/
example : certificateComplexityAt (orF 3) ![false, false, false] = 3 := by decide

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
example : certificateComplexityAt (parityF 3) ![true, true, true] = 3 := by decide

/-! ## MAJ₃

Here `s = bs = C = 2`, one less than the number of input bits.
-/

example : sensitivity maj3 = 2 := by decide
example : blockSensitivity maj3 = 2 := by decide
example : certificateComplexity maj3 = 2 := by decide

/-- An all-`true` has no sensitive bits. -/
example : sensitivityAt maj3 ![true, true, true] = 0 := by decide

/-- A split input is sensitive in the two agreeing coordinates, but not the third. -/
example : sensitiveCoords maj3 ![true, true, false] = {0, 1} := by decide

/-- Two agreeing bits are a certificate, so `C(f, x) = 2` everywhere. -/
example : certificateComplexityAt maj3 ![true, true, false] = 2 := by decide

/-! ## Decision tree complexity

`D(f) = n` whenever some input is sensitive to every coordinate, and `D(f) = 0` exactly for the
constants. `D(MAJ₃) = 3` is also true but needs an adversary argument, since `s(MAJ₃) = 2`.
-/

example : DecisionTree.complexity (orF 3) = 3 :=
  DecisionTree.complexity_eq_card_of_sensitivityAt_eq_card (x := ![false, false, false])
    (by decide)

example : DecisionTree.complexity (andF 3) = 3 :=
  DecisionTree.complexity_eq_card_of_sensitivityAt_eq_card (x := ![true, true, true]) (by decide)

example : DecisionTree.complexity (parityF 3) = 3 :=
  DecisionTree.complexity_eq_card_of_sensitivityAt_eq_card (x := ![false, false, false])
    (by decide)

example : DecisionTree.complexity (fun _ => true : BooleanFunction 3) = 0 :=
  DecisionTree.complexity_eq_zero_iff.2 fun _ _ => rfl

/-! ## Constant functions

No bit is sensitive, and the empty set is a certificate.
-/

example : sensitivity (fun _ => true : BooleanFunction 3) = 0 := by decide
example : blockSensitivity (fun _ => true : BooleanFunction 3) = 0 := by decide
example : certificateComplexity (fun _ => true : BooleanFunction 3) = 0 := by decide

end CslibTests.QueryComplexity
