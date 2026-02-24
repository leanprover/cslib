/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import Cslib.Foundations.Data.BiTape
import Cslib.Foundations.Data.RelatesInSteps

public import Cslib.Computability.Machines.MultiTapeTuring.Basic
public import Cslib.Computability.Machines.MultiTapeTuring.ListEncoding
public import Cslib.Computability.Machines.MultiTapeTuring.HeadStats

namespace Turing

namespace Routines

variable [Inhabited α] [Fintype α]
variable {k : ℕ}

/--
Repeatedly run a sub routine as long as a condition on the symbol
at the head of tape `i` is true.
-/
public def doWhileSymbol (cond : Option α → Bool) (i : Fin k) (tm : MultiTapeTM k α) :
    MultiTapeTM k α where
  Λ := PUnit
  q₀ := 0
  M _ syms := sorry

@[simp]
public theorem doWhileSymbol_eval
  (cond : Option α → Bool)
  (i : Fin k)
  (tm : MultiTapeTM k α)
  (tapes_seq : ℕ → Fin k → BiTape α)
  (h_transform : ∀ j, tm.eval (tapes_seq j) = .some (tapes_seq j.succ))
  (h_stops : ∃ m, cond (tapes_seq m i).head = false) :
  (doWhileSymbol cond i tm).eval (tapes_seq 0) = .some (tapes_seq (Nat.find h_stops)) := by
  sorry

/-- Repeatedly run a sub routine as long as the first word on tape `i` is non-empty.
-/
public def doWhile (i : Fin k) (tm : MultiTapeTM k (WithSep α)) :
    MultiTapeTM k (WithSep α) where
  Λ := PUnit
  q₀ := 0
  M _ syms := sorry

@[simp]
public theorem doWhile_eval_list
  {i : Fin k}
  {tm : MultiTapeTM k (WithSep α)}
  {tapes : Fin k → List (List α)}
  (h_halts : ∀ tapes', tm.HaltsOnLists tapes') :
  (doWhile i tm).eval_list tapes =
    ⟨∃ n, ((tm.eval_list_tot h_halts)^[n] tapes i).head?.getD [] = [],
      fun h_loopEnds => (tm.eval_list_tot h_halts)^[Nat.find h_loopEnds] tapes⟩ := by
  sorry

end Routines

end Turing
