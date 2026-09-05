/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Comp

namespace CslibTests.MultiTapeComplexity

open Turing.MultiTapeTM

private def finish (move : SignType) (symbol : Bool) : Turing.MultiTapeTM 0 Bool Unit where
  q₀ := ()
  tr _ _ _ := ⟨move, Fin.elim0, some symbol, none⟩

private def bit : Bool ↪ List Bool := ⟨fun b => [b], by intro a b h; simpa using h⟩

-- Bounds can differ for inputs of the same encoded length; the public combinator needs no
-- monotonicity premise and hides the machine witnesses.
private lemma constant_computable :
    ComputableInTimeAndSpace (fun _ : Bool => true) bit bit
      (fun b => if b then 1 else 2) (fun _ => 0) := by
  refine ⟨0, Unit, inferInstance, finish 0 true, fun b => ⟨1, ?_, 0, le_rfl, ?_⟩⟩
  · cases b <;> decide
  · exact ⟨rfl, rfl, spaceUsed_zero_tapes_eq_zero _ _ rfl⟩

example : ComputableInTimeAndSpace (fun _ : Bool => true) bit bit
    (fun b => (if b then 1 else 2) + 6) (fun _ => 3) := by
  have hbit (b : Bool) : bit b = [b] := rfl
  simpa [hbit, Nat.add_assoc] using
    computableInTimeAndSpace_comp constant_computable constant_computable

end CslibTests.MultiTapeComplexity
