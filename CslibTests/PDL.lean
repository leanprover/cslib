/-
Copyright (c) 2026 Malvin Gattinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Malvin Gattinger
-/

import Cslib.Logics.PDL.Basic
import Cslib.Logics.Modal.LogicalEquivalence

namespace CslibTests

open Cslib Logic Modal PDL Model Proposition Satisfies
open scoped InferenceSystem

-- ⟨(?p ; a)*⟩q
def exampleFormula : @Formula Nat Nat :=
  diamond (star (seq (test (.atom 0)) (action 0))) (.atom 1)

def sameExampleFormula (p q : Nat) (a : Nat) : @Formula Nat Nat :=
  d⟨ (?' p ;' a)*⟩ q

example : exampleFormula = sameExampleFormula 0 1 0 := by rfl

end CslibTests
