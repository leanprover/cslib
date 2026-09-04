/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant

namespace CslibTests

open Cslib Turing MultiTapeTM

/-- The Boolean `and` function is computable in constant time and zero space. -/
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

/-- The binary full adder is computable in constant time and zero space. -/
example : ∀ encIn encOut, ∃ c, EncodedComputableInTimeAndSpace
    (encIn := encIn)
    (encOut := encOut)
    (Function.uncurry fullAdder)
    (fun _ => c) (fun _ => 0) := by
  intro encIn encOut
  apply encodedComputableInTimeAndSpace_of_finite

/-- Equality comparison to a constant is computable in constant time and zero space,
also for infinite domains. -/
example {α : Type*} [DecidableEq α] : ∀ encIn encOut out, ∃ c, EncodedComputableInTimeAndSpace
    (encIn := encIn)
    (encOut := encOut)
    (fun a : α => a == out)
    (fun _ => c) (fun _ => 0) := by
  intro encIn encOut out
  refine encodedComputableInTimeAndSpace_of_exists_finite_ne ⟨false, ?_⟩
  exact Set.Finite.subset (Set.finite_singleton out) (by intro a ha; simp_all)

end CslibTests
