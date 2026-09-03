/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Finite

namespace CslibTests

open Cslib Turing MultiTapeTM

/-- Regardless of the encoding, the Boolean `and` function is computable in constant time
and zero space. -/
example : ∀ encIn encOut, ∃ c, EncodedComputableInTimeAndSpace
    (encIn := encIn)
    (encOut := encOut)
    (Function.uncurry Bool.and)
    (fun _ => c) (fun _ => 0) := by
  intro encIn encOut
  apply encodedComputableInTimeAndSpace_of_finite

def fullAdder (a b carry : Bool) : Bool × Bool :=
  let sum := (a != b) != carry
  let newCarry := (a && b) || (carry && (a != b))
  (sum, newCarry)

/-- Regardless of the encoding, the binary full adder is computable in constant time and zero
space. -/
example : ∀ encIn encOut, ∃ c, EncodedComputableInTimeAndSpace
    (encIn := encIn)
    (encOut := encOut)
    (Function.uncurry fullAdder)
    (fun _ => c) (fun _ => 0) := by
  intro encIn encOut
  apply encodedComputableInTimeAndSpace_of_finite


end CslibTests
