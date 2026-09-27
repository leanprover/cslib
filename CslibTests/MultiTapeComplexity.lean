/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

namespace CslibTests.MultiTapeComplexity

open Turing.MultiTapeTM

private def finish (move : SignType) (symbol : Bool) : Turing.MultiTapeTM 0 Bool Unit :=
  ofTr () fun _ _ _ => ⟨move, Fin.elim0, some symbol, none⟩

private def bit : Bool ↪ List Bool := ⟨fun b => [b], by intro a b h; simpa using h⟩

-- Bounds can differ for inputs of the same encoded length.
private lemma constant_computable :
    ComputableInTimeAndSpace (fun _ : Bool => true) bit bit
      (fun b => if b then 1 else 2) (fun _ => 0) := by
  refine ⟨0, Unit, inferInstance, (finish 0 true).toMultiTapeNTM,
    (finish 0 true).deterministic, fun b => ⟨1, ?_, 0, le_rfl, ?_⟩⟩
  · cases b <;> decide
  · refine computesInExactTimeAndSpace_of_runFrom ?_ ?_ (by simp)
    · rw [runFrom, Function.iterate_one, step_of_state rfl]
      simp [finish, Turing.Cfg.Halted]
    · rw [runFrom, Function.iterate_one, step_of_state rfl]
      simp [finish]; rfl

-- A theorem about nondeterministic steps applies directly to a deterministic machine.
example {tm : Turing.MultiTapeTM k Symbol State} {input : List Symbol}
    {c c' : Turing.Cfg k Symbol State input} (h : c.Halted) :
    tm.Step c c' ↔ c' = c :=
  Turing.MultiTapeNTM.step_of_halt h

-- Deterministic computability uses the shared monotonicity theorem through its abbreviation.
example {α β : Type*} {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    {t s t' s' : α → ℕ} (h : ComputableInTimeAndSpace f encIn encOut t s)
    (ht : ∀ a, t a ≤ t' a) (hs : ∀ a, s a ≤ s' a) :
    ComputableInTimeAndSpace f encIn encOut t' s' :=
  h.mono ht hs

end CslibTests.MultiTapeComplexity
