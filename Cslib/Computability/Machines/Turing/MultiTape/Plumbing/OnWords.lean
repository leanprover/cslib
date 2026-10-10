/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Mathlib.Basic.Finite.Sum
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.OutputToTape
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.InputFromTape
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Tidy

/-!
# Running a tidy computation on work tapes

`onWords tm mark` reads its input as a word on one work tape and writes the output of `tm` as a
word on another, leaving every other tape alone. It is `tm` with its output redirected to a new
work tape (`Turing.MultiTapeTM.outputToWord`) and its input read from another new work tape
(`Turing.MultiTapeTM.inputFromWord`).

## Main results

* `Turing.MultiTapeTM.onWords`: the composed machine.
* `Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace.onWords`: if `tm` computes `output` from `input`
  tidily, then `onWords tm mark` takes `input` on its input work tape to `output` on its output
  work tape.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.exists_onWords`: a tidily computable function
  is computed by a machine that reads its input from one work tape and writes its output to
  another.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*}

/-- `tm`, with its output written to the work tape `(Fin.last k).castAdd 2` and its input read
from the work tape `Fin.natAdd (k + 1) 0`, using `mark` to flag the left end of the input. -/
noncomputable def onWords (tm : MultiTapeTM k Symbol State) (mark : Symbol) :
    MultiTapeTM (k + 1 + 2) Symbol (MarkWorkState ⊕ (State ⊕ RewindWorkState) ⊕ MarkWorkState) :=
  tm.outputToWord.inputFromWord mark

/-- The work tapes in which `onWords` starts, as seen by `inputFromWord`. -/
private lemma onWords_pre (input : List Symbol) :
    Fin.append (fun _ : Fin (k + 1) => ([] : List Symbol)) ![input, []] =
      Function.update (fun _ => []) (Fin.natAdd (k + 1) 0) input := by
  rw [← Fin.append_const (m := k + 1) (n := 2) [], ← Fin.append_update_right]
  congr 1
  simp [funext_iff, Fin.forall_fin_two]

/-- The work tapes in which `onWords` halts, as seen by `inputFromWord`. -/
private lemma onWords_post (input output : List Symbol) :
    Fin.append (Function.update (fun _ : Fin (k + 1) => ([] : List Symbol)) (Fin.last k) output)
        ![input, []] =
      Function.update (Function.update (fun _ => []) (Fin.natAdd (k + 1) 0) input)
        ((Fin.last k).castAdd 2) output := by
  rw [Fin.append_update_left, onWords_pre]

/-- If `tm` computes `output` from `input` tidily, then `onWords tm mark`, started with `input` on
the work tape `Fin.natAdd (k + 1) 0` and all other work tapes blank, halts with `output` on the
work tape `(Fin.last k).castAdd 2`, every other work tape unchanged, and nothing emitted. -/
theorem ComputesTidilyInTimeAndSpace.onWords {tm : MultiTapeTM k Symbol State}
    {input output : List Symbol} {t s : ℕ} (mark : Symbol)
    (h : tm.ComputesTidilyInTimeAndSpace input output t s) :
    TransformsTapes (tm.onWords mark)
      (fun _ ws => ws = Function.update (fun _ => []) (Fin.natAdd (k + 1) 0) input)
      (fun _ ws ws' emitted =>
        ws' = Function.update ws ((Fin.last k).castAdd 2) output ∧ emitted = [])
      (t + output.length + 6) (s + 2 * input.length + 2 * output.length + 3 * k + 15) := by
  -- the run of `outputToWord tm` on `input` with blank work tapes
  obtain ⟨ws', emitted, hrun, ⟨rfl, rfl⟩, hspace⟩ :=
    h.outputToWord input (fun _ => []) [] ⟨rfl, rfl⟩
  rw [List.append_nil] at hrun
  have key := transformsTapes_inputFromWord_of_runFrom mark (M := tm.outputToWord)
    (w := input) (ws₀ := fun _ => [])
    (ws₁ := Function.update (fun _ => []) (Fin.last k) output) (e := []) hrun hspace
  refine key.imp (fun _ ws hws => ?_) (fun _ ws ws' em hws ⟨hws', hem⟩ => ⟨?_, hem⟩)
    (by omega) (by omega)
  · rw [hws, onWords_pre]
  · rw [hws, hws', onWords_post]

/-- A tidily computable function is computed by a machine with binary alphabet and finitely many
states that reads its input from a work tape `i` and writes its output to a different work tape
`o`, leaving every other work tape unchanged and emitting nothing. -/
theorem ComputableTidilyInTimeAndSpace.exists_onWords {α β : Type*}
    {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {t s : α → ℕ}
    (h : ComputableTidilyInTimeAndSpace f encIn encOut t s) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM (k + 1 + 2) Bool State)
      (i o : Fin (k + 1 + 2)), i ≠ o ∧ ∀ a, TransformsTapes tm
        (fun _ ws => ws = Function.update (fun _ => []) i (encIn a))
        (fun _ ws ws' emitted => ws' = Function.update ws o (encOut (f a)) ∧ emitted = [])
        (t a + (encOut (f a)).length + 6)
        (s a + 2 * (encIn a).length + 2 * (encOut (f a)).length + 3 * k + 15) := by
  obtain ⟨k, State, _, tm, htm⟩ := h
  exact ⟨k, _, inferInstance, tm.onWords true, Fin.natAdd (k + 1) 0, (Fin.last k).castAdd 2,
    (Fin.castAdd_ne_natAdd _ _).symm,
    fun a => (htm a).onWords true⟩

end Turing.MultiTapeTM
