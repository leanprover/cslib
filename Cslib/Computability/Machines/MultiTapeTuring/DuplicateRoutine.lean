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
public import Cslib.Computability.Machines.MultiTapeTuring.PopRoutine
public import Cslib.Computability.Machines.MultiTapeTuring.SequentialCombinator

namespace Turing

namespace Routines

variable [Inhabited α] [Fintype α]

def duplicate₀ : MultiTapeTM 2 (WithSep α) := copy 0 1 ;ₜ copy 1 0 ;ₜ pop 1

@[simp]
lemma duplicate₀_eval_list {tapes : Fin 2 → List (List α)} :
  duplicate₀.eval_list tapes = .some (Function.update tapes 0
    (((tapes 0).headD []) :: (tapes 0))) := by
  simp [duplicate₀]
  grind

/--
A Turing machine that duplicates the head of tape `i` (or pushes the empty word
if the tape is empty.
-/
public def duplicate {k : ℕ} (i : Fin k.succ)
  (aux : Fin k.succ := ⟨k, by omega⟩)
  (h_inj : [i, aux].get.Injective := by intro x y; grind) :
  MultiTapeTM k.succ (WithSep α) :=
  duplicate₀.with_tapes [i, aux].get h_inj

@[simp, grind =]
public theorem duplicate_eval_list {k : ℕ} {i : Fin k.succ}
  (aux : Fin k.succ := ⟨k, by omega⟩)
  (h_inj : [i, aux].get.Injective)
  {tapes : Fin k.succ → List (List OneTwo)} :
  (duplicate i aux h_inj).eval_list tapes = Part.some (Function.update tapes i
    (((tapes i).headD []) :: (tapes i))) := by
  simp [duplicate]
  grind

end Routines

end Turing
