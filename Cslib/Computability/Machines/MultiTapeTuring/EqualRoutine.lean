/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Basic
public import Cslib.Computability.Machines.MultiTapeTuring.ListEncoding
public import Cslib.Computability.Machines.MultiTapeTuring.WithTapes

import Mathlib.Logic.Function.Basic

namespace Turing

namespace Routines

/--
A 3-tape Turing machine that pushes the new word "1"
to the third tape if the first words on the first and second tape are the same
and otherwise pushes the empty word to the third tape.
If one of the first two tapes is empty, uses the empty word for comparison.
-/
def eq₀ : MultiTapeTM 3 (WithSep OneTwo) where
  Λ := PUnit
  q₀ := 0
  M _ syms := sorry

@[simp]
theorem eq₀_eval_list {tapes : Fin 3 → List (List OneTwo)} :
  eq₀.eval_list tapes =
    Part.some (Function.update tapes 2 ((if (tapes 0).headD [] = (tapes 1).headD [] then
      [.one]
    else
      []) :: (tapes 2))) := by
  sorry

/--
A Turing machine that pushes the new word "1"
to tape `t` if the first words on tape `q` and tape `s` are the same
and otherwise pushes the empty word to tape `t`.
If one of the tapes `q` or `s` are empty, uses the empty word for comparison.
-/
public def eq {k : ℕ} (q s t : Fin k)
  (h_inj : [q, s, t].get.Injective := by intro x y; grind) :
  MultiTapeTM k (WithSep OneTwo) :=
  eq₀.with_tapes [q, s, t].get h_inj

@[grind =]
public theorem eq_eval_list {k : ℕ} {q s t : Fin k}
  (h_inj : [q, s, t].get.Injective)
  {tapes : Fin k → List (List OneTwo)} :
  (eq q s t).eval_list tapes =
    Part.some (Function.update tapes t ((if (tapes q).headD [] = (tapes s).headD [] then
      [.one]
    else
      []) :: (tapes t))) := by
  simp [eq]
  grind

end Routines

end Turing
