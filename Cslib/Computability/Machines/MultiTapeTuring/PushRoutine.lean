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

def push₁ (w : List α) : MultiTapeTM 1 (WithSep α) where
  Λ := PUnit
  q₀ := 0
  M _ syms := sorry

@[simp]
lemma push₁_eval_list {w : List α} {tapes : Fin 1 → List (List α)} :
  (push₁ w).eval_list tapes = .some (Function.update tapes 0 (w :: (tapes 0))) := by
  sorry

/--
A Turing machine that pushes the word `w` to tape `i`.
-/
public def push {k : ℕ} (i : Fin k) (w : List α) : MultiTapeTM k (WithSep α) :=
  (push₁ w).with_tapes [i].get (by intro x y; grind)

@[simp, grind =]
public theorem push_eval_list {k : ℕ}
  {i : Fin k} {w : List α} {tapes : Fin k → List (List α)} :
  (push i w).eval_list tapes =
    .some (Function.update tapes i (w :: (tapes i))) := by
  have h_inj : [i].get.Injective := by intro x y; grind
  simp_all [push]

end Routines

end Turing
