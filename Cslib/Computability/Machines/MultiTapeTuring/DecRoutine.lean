/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Basic
public import Cslib.Computability.Machines.MultiTapeTuring.ListEncoding
public import Cslib.Computability.Machines.MultiTapeTuring.WithTapes
public import Cslib.Computability.Machines.MultiTapeTuring.CopyRoutine
public import Cslib.Computability.Machines.MultiTapeTuring.SuccRoutine
public import Cslib.Computability.Machines.MultiTapeTuring.PushRoutine
public import Cslib.Computability.Machines.MultiTapeTuring.PopRoutine
public import Cslib.Computability.Machines.MultiTapeTuring.SequentialCombinator
public import Cslib.Computability.Machines.MultiTapeTuring.LoopCombinator

namespace Turing

namespace Routines

def dec₀ : MultiTapeTM 6 (WithSep OneTwo) :=
  push 1 [] ;ₜ push 2 [] ;ₜ
  loop 0 (pop 2 ;ₜ copy 1 2 ;ₜ succ 1) ;ₜ
  pop 0 ;ₜ
  copy 2 0 ;ₜ
  pop 2 ;ₜ
  pop 1


@[simp]
lemma inner_eval_iter {r : ℕ} {tapes : Fin 3 → List (List OneTwo)} :
  (Part.bind · (pop 2 ;ₜ copy 1 2 ;ₜ succ 1).eval_list)^[r] (.some tapes) = Part.some (
    if r = 0 then
      tapes
    else
      Function.update (Function.update tapes
        2 ((dya ((dya_inv ((tapes 1).headD [])) + (r - 1))) :: (tapes 2).tail))
        1 ((dya ((dya_inv ((tapes 1).headD [])) + r)) :: (tapes 1).tail)) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    simp [ih]
    grind

@[simp, grind =]
lemma dec₀_eval_list {tapes : Fin 6 → List (List OneTwo)} :
  dec₀.eval_list tapes = .some (Function.update tapes 0
    ((dya ((dya_inv ((tapes 0).headD [])) - 1)) :: (tapes 0).tail)) := by
  by_cases h : dya_inv ((tapes 0).head?.getD []) = 0
  <;> simp [dec₀, h] <;> grind

/--
A Turing machine that decrements the dyadic value at the head of tape `i`.
If the value is zero already, keeps it at zero. If the tape is empty, pushes zero.
-/
public def dec {k : ℕ} (i : Fin (k + 6))
  (aux : Fin (k + 6) := ⟨k + 1, by omega⟩)
  (h_inj : [i, aux, aux + 1, aux + 2, aux + 3, aux + 4].get.Injective :=
    by intro x y; grind) :
  MultiTapeTM (k + 6) (WithSep OneTwo) :=
  dec₀.with_tapes [i, aux, aux + 1, aux + 2, aux + 3, aux + 4].get h_inj

@[simp, grind =]
public theorem dec_eval_list {k : ℕ} (i aux : Fin (k + 6))
  (h_inj : [i, aux, aux + 1, aux + 2, aux + 3, aux + 4].get.Injective)
  (tapes : Fin (k + 6) → List (List OneTwo)) :
  (dec i aux h_inj).eval_list tapes = .some (Function.update tapes i
    ((dya ((dya_inv ((tapes i).headD [])) - 1)) :: (tapes i).tail)) := by
  simpa [dec] using apply_updates_function_update h_inj

end Routines

end Turing
