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
public import Cslib.Computability.Machines.MultiTapeTuring.WithTapes

import Mathlib.Data.Nat.Bits

namespace Turing

namespace Routines

def succ₀ : MultiTapeTM 1 (WithSep OneTwo) where
  Λ := PUnit
  q₀ := 0
  M _ syms := sorry

@[simp]
lemma succ₀_eval_list {tapes : Fin 1 → List (List OneTwo)} :
  succ₀.eval_list tapes = .some (Function.update tapes 0
    ((dya (dya_inv ((tapes 0).headD [])).succ) :: (tapes 0).tail)) := by
  sorry

/--
A Turing machine that increments the head of tape `i` by one (in dyadic encoding).
Pushes zero if the tape is empty. -/
public def succ {k : ℕ} (i : Fin k) : MultiTapeTM k (WithSep OneTwo) :=
  succ₀.with_tapes [i].get (by intro x y; grind)

@[simp]
public theorem succ_eval_list {k : ℕ} {i : Fin k} {tapes : Fin k → List (List OneTwo)} :
  (succ i).eval_list tapes = .some (Function.update tapes i
    ((dya (dya_inv ((tapes i).headD [])).succ) :: (tapes i).tail)) := by
  simpa [succ] using apply_updates_function_update (by intro x y; grind)

lemma succ₀_evalWithStats_list {n : ℕ} {ls : List (List OneTwo)} :
  succ₀.evalWithStats_list [(dya n) :: ls].get =
    .some (
      [(dya n.succ) :: ls].get,
      -- this depends on if we have overflow on the highest dyadic character or not.
      if (dya n.succ).length = (dya n).length then
        [⟨0, (dya n).length, 0, by omega⟩].get
      else
        [⟨-1, (dya n).length, -1, by omega⟩].get) := by
  sorry


end Routines

end Turing
