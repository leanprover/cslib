/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Basic
public import Cslib.Computability.Machines.MultiTapeTuring.ListEncoding
public import Cslib.Computability.Machines.MultiTapeTuring.WithTapes

namespace Turing

namespace Routines

variable [Inhabited α] [Fintype α]

def pop₁ : MultiTapeTM 1 (WithSep α) where
  Λ := PUnit
  q₀ := 0
  M _ syms := sorry

@[simp]
lemma pop₁_eval_list {tapes : Fin 1 → List (List α)} :
  pop₁.eval_list tapes = .some (Function.update tapes 0 (tapes 0).tail) := by
  sorry

/--
A Turing machine that removes the first word on tape `i`. If the tape is empty, does nothing.
-/
public def pop {k : ℕ} (i : Fin k) : MultiTapeTM k (WithSep α) :=
  pop₁.with_tapes [i].get (by intro x y; grind)

@[simp, grind =]
public theorem pop_eval_list {k : ℕ} {i : Fin k}
  {tapes : Fin k → List (List α)} :
  (pop i).eval_list tapes = .some (Function.update tapes i (tapes i).tail) := by
  have h_inj : [i].get.Injective := by intro x y; grind
  simp_all [pop]

end Routines

end Turing
