/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Basic
public import Cslib.Computability.Machines.MultiTapeTuring.ListEncoding
public import Cslib.Computability.Machines.MultiTapeTuring.SuccRoutine
public import Cslib.Computability.Machines.MultiTapeTuring.CopyRoutine
public import Cslib.Computability.Machines.MultiTapeTuring.PushRoutine
public import Cslib.Computability.Machines.MultiTapeTuring.PopRoutine
public import Cslib.Computability.Machines.MultiTapeTuring.LoopCombinator
public import Cslib.Computability.Machines.MultiTapeTuring.SequentialCombinator
public import Cslib.Computability.Machines.MultiTapeTuring.WithTapes

namespace Turing

variable {k : ℕ}

namespace Routines

@[simp]
lemma succ_iter {k r : ℕ} {i : Fin k.succ} {tapes : Fin k.succ → List (List OneTwo)} :
  (Part.bind · (succ i).eval_list)^[r] (.some tapes) = Part.some (Function.update tapes i (
    if r ≠ 0 then
      (dya ((dya_inv ((tapes i).headD [])) + r)) :: (tapes i).tail
    else
      tapes i)) := by
  induction r with
    | zero => simp
    | succ r ih =>
      rw [Function.iterate_succ_apply']
      simp [ih]
      grind

--- Add 0 and 1 and store the result in 2.
--- Assumes zero for an empty tape.
def add₀ : MultiTapeTM 6 (WithSep OneTwo) :=
  (copy 1 2) <;> loop (h_i := by decide) 0 (succ 2)

@[simp, grind =]
theorem add₀_eval_list {tapes : Fin 6 → List (List OneTwo)} :
  add₀.eval_list tapes = .some
    (Function.update tapes 2 ((dya (dya_inv ((tapes 0).headD []) +
      dya_inv ((tapes 1).headD [])) :: (tapes 2)))) := by
  simp [add₀]
  by_cases h : dya_inv ((tapes 0).head?.getD []) = 0
  · simp [h]; grind
  · grind

/--
A Turing machine that adds the heads of tapes i and j (in dyadic encoding) and pushes the result
to tape l.
Assumes zero for an empty tape. -/
public def add (i j l : Fin (k + 6)) (aux : Fin (k + 6) := ⟨k + 3, by omega⟩)
  (h_inj : [i, j, l, aux, aux + 1, aux + 2].get.Injective := by decide) :
  MultiTapeTM (k + 6) (WithSep OneTwo) :=
  add₀.with_tapes [i, j, l, aux, aux + 1, aux + 2].get h_inj

@[simp, grind =]
public theorem add_eval_list (i j l aux : Fin (k + 6))
  {h_inj : [i, j, l, aux, aux + 1, aux + 2].get.Injective}
  {tapes : Fin (k + 6) → List (List OneTwo)} :
  (add i j l aux h_inj).eval_list tapes =
      .some (Function.update tapes l (
        (dya (dya_inv ((tapes i).headD []) + dya_inv ((tapes j).headD [])) :: (tapes l)))) := by
  simp [add]
  grind

-- Add head of 0 to head of 1 (and store it in head of 1).
def add_assign₀ : MultiTapeTM 6 (WithSep OneTwo) :=
  add 0 1 2 (h_inj := by decide) <;> pop 1 <;> copy 2 1 <;> pop 2

@[simp]
lemma add_assign₀_eval_list {tapes : Fin 6 → List (List OneTwo)} :
  add_assign₀.eval_list tapes = .some
    (Function.update tapes 1 ((dya (dya_inv ((tapes 0).headD []) +
      dya_inv ((tapes 1).headD [])) :: (tapes 1).tail))) := by
  simp [add_assign₀]
  grind

/--
A Turing machine that adds the head of tape `i` to the head of tape `j` (and updates the
head of tape `j` with the result). -/
public def add_assign
  (i j : Fin (k + 6))
  (aux : Fin (k + 6) := ⟨k + 2, by omega⟩)
  (h_inj : [i, j, aux, aux + 1, aux + 2, aux + 3].get.Injective := by decide) :
  MultiTapeTM (k + 6) (WithSep OneTwo) :=
  add_assign₀.with_tapes [i, j, aux, aux + 1, aux + 2, aux + 3].get h_inj

@[simp]
public theorem add_assign_eval_list {i j aux : Fin (k + 6)}
  {h_inj : [i, j, aux, aux + 1, aux + 2, aux + 3].get.Injective}
  {tapes : Fin (k + 6) → List (List OneTwo)} :
  (add_assign i j aux h_inj).eval_list tapes =
      .some (Function.update tapes j (
        (dya (dya_inv ((tapes i).headD []) +
          dya_inv ((tapes j).headD [])) :: (tapes j).tail))) := by
  simpa [add_assign] using apply_updates_function_update h_inj

end Routines

end Turing
