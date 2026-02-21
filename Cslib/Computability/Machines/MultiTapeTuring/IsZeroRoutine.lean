/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Basic
public import Cslib.Computability.Machines.MultiTapeTuring.ListEncoding
public import Cslib.Computability.Machines.MultiTapeTuring.PushRoutine
public import Cslib.Computability.Machines.MultiTapeTuring.PopRoutine
public import Cslib.Computability.Machines.MultiTapeTuring.SequentialCombinator
public import Cslib.Computability.Machines.MultiTapeTuring.IteCombinator

namespace Turing

variable {k : ℕ}

namespace Routines

/--
A Turing machine that computes the logical negation: It replaces an empty (or non-existing) head
on tape `i` by the word "1" and everything else by the empty word. -/
public def isZero (i : Fin k) := ite i (pop i <;> push i []) (pop i <;> push i [OneTwo.one])

@[simp, grind =]
public theorem isZero_eval_list {i : Fin k} {tapes : Fin k → List (List OneTwo)} :
  (isZero i).eval_list tapes = .some (Function.update tapes i (
    (if (tapes i).headD [] = [] then [OneTwo.one] else []) :: (tapes i).tail)) := by
  simp [isZero]
  grind

end Routines
end Turing
