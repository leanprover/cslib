/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Mathlib.Basic.Finite.Sum
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.OutputToWord
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.InputFromWord
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Tidy

/-!
# A tidy computation as a work-tape-to-work-tape transformation

`onWords tm mark` is the capstone of the word plumbing: it turns a machine computing *tidily* into a
machine that reads its input as a word on one work tape and writes the result as a word on another,
touching nothing else. It is the composition of the two halves built separately — first
`Turing.MultiTapeTM.outputToWord` redirects `tm`'s output onto a fresh last work tape (and rewinds
that head), then `Turing.MultiTapeTM.inputFromWord` feeds that machine its input from a virtual
input word on an added tape. The result is a genuine `wordsCfg → wordsCfg` transformer: blank tapes
except the virtual input word go to blank tapes except the output word, emitting nothing.

## Main results

* `Turing.MultiTapeTM.onWords`: the composed machine.
* `Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace.onWords`: a tidy computation becomes a tape
  transformation placing the output on a designated tape, reading the input from another.
* `Turing.MultiTapeTM.ComputesFunTidilyInTimeAndSpace.onWords`: the same for a computed function.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.exists_onWords`: the conversion theorem — a
  tidily computable function is computed by some machine as a word-to-word tape transformer, with an
  input tape distinct from the output tape.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*}

/-- `tm`, converted into a word-to-word tape transformer: its output redirected onto a fresh work
tape by `Turing.MultiTapeTM.outputToWord`, then its input read from a virtual input word on an
added tape by `Turing.MultiTapeTM.inputFromWord`. -/
noncomputable def onWords (tm : MultiTapeTM k Symbol State) (mark : Symbol) :
    MultiTapeTM (k + 1 + 2) Symbol (MarkWorkState ⊕ (State ⊕ RewindWorkState) ⊕ MarkWorkState) :=
  tm.outputToWord.inputFromWord mark

/-- **Glue (precondition).** The blank inner tapes appended with the virtual input word `input` and
the empty flag word is the family that is blank everywhere except the virtual input tape. -/
private lemma onWords_pre {k : ℕ} {Symbol : Type*} (input : List Symbol) :
    Fin.append (fun _ : Fin (k + 1) => ([] : List Symbol)) ![input, []] =
      Function.update (fun _ => []) (Fin.natAdd (k + 1) 0) input := by
  funext l
  refine Fin.addCases (fun j => ?_) (fun i => ?_) l
  · have hne : Fin.castAdd 2 j ≠ Fin.natAdd (k + 1) 0 :=
      Fin.ne_of_val_ne (by simp only [Fin.val_castAdd, Fin.val_natAdd]; omega)
    rw [Fin.append_left, Function.update_of_ne hne]
  · rw [Fin.append_right]
    refine i.cases ?_ (fun i' => ?_)
    · rw [Matrix.cons_val_zero, Function.update_self]
    · have hne : Fin.natAdd (k + 1) i'.succ ≠ Fin.natAdd (k + 1) 0 :=
        Fin.ne_of_val_ne (by simp only [Fin.val_natAdd, Fin.val_succ, Fin.val_zero]; omega)
      rw [Function.update_of_ne hne]
      simp

/-- Updating the left-hand part of an appended family commutes with appending. -/
private lemma append_update_left {α : Type*} {m n : ℕ} (a : Fin m → α) (b : Fin n → α)
    (j : Fin m) (x : α) :
    Fin.append (Function.update a j x) b = Function.update (Fin.append a b) (j.castAdd n) x := by
  funext l
  refine Fin.addCases (fun j' => ?_) (fun i => ?_) l
  · rcases eq_or_ne j' j with rfl | hne
    · rw [Fin.append_left, Function.update_self, Function.update_self]
    · rw [Fin.append_left, Function.update_of_ne hne, Function.update_of_ne (by simpa using hne),
        Fin.append_left]
  · rw [Fin.append_right, Function.update_of_ne
      (Fin.ne_of_val_ne (by simp only [Fin.val_natAdd, Fin.val_castAdd]; omega)), Fin.append_right]

/-- **Glue (postcondition).** The inner tapes holding `output` on the last tape, appended with the
virtual input word `input` and the empty flag word, is the blank family updated with `input` on the
virtual input tape and `output` on the output tape. -/
private lemma onWords_post {k : ℕ} {Symbol : Type*} (input output : List Symbol) :
    Fin.append (Function.update (fun _ : Fin (k + 1) => ([] : List Symbol)) (Fin.last k) output)
        ![input, []] =
      Function.update (Function.update (fun _ => []) (Fin.natAdd (k + 1) 0) input)
        ((Fin.last k).castAdd 2) output := by
  rw [append_update_left, onWords_pre]

/-- **A tidy computation becomes a word-to-word tape transformation.** Started on tapes blank except
for the virtual input word on tape `Fin.natAdd (k + 1) 0`, `tm.onWords mark` halts leaving every
tape as it was except the output tape `(Fin.last k).castAdd 2`, which holds the emitted word, and
emits nothing. -/
theorem ComputesTidilyInTimeAndSpace.onWords {k : ℕ} {Symbol State : Type*}
    {tm : MultiTapeTM k Symbol State} {input output : List Symbol} {t s : ℕ} (mark : Symbol)
    (h : tm.ComputesTidilyInTimeAndSpace input output t s) :
    TransformsTapes (tm.onWords mark)
      (fun _ ws => ws = Function.update (fun _ => []) (Fin.natAdd (k + 1) 0) input)
      (fun _ ws ws' emitted =>
        ws' = Function.update ws ((Fin.last k).castAdd 2) output ∧ emitted = [])
      (t + output.length + 6) (s + 2 * input.length + 2 * output.length + 3 * k + 15) := by
  -- extract `outputToWord`'s single run, instantiated at the real input and blank tapes
  obtain ⟨ws', emitted, hrun, ⟨rfl, rfl⟩, hspace⟩ :=
    h.outputToWord input (fun _ => []) [] ⟨rfl, rfl⟩
  rw [List.append_nil] at hrun
  -- feed it to `inputFromWord`, giving a `TransformsTapes` for `tm.onWords mark`
  have key := transformsTapes_inputFromWord_of_runFrom mark (M := tm.outputToWord)
    (w := input) (ws₀ := fun _ => [])
    (ws₁ := Function.update (fun _ => []) (Fin.last k) output) (e := []) hrun hspace
  refine key.imp (fun _ ws hws => ?_) (fun _ ws ws' em hws ⟨hws', hem⟩ => ⟨?_, hem⟩)
    (by omega) (by omega)
  · rw [hws, onWords_pre]
  · rw [hws, hws', onWords_post]

/-- **A tidily computed function becomes a word-to-word tape transformation**, pointwise on every
input: reading `encIn a` from the virtual input tape and leaving `encOut (f a)` on the output tape,
emitting nothing. -/
theorem ComputesFunTidilyInTimeAndSpace.onWords {k : ℕ} {Symbol State α β : Type*}
    {tm : MultiTapeTM k Symbol State} {encIn : α ↪ List Symbol} {encOut : β ↪ List Symbol}
    {f : α → β} {t s : α → ℕ} (mark : Symbol)
    (h : ComputesFunTidilyInTimeAndSpace tm encIn encOut f t s) (a : α) :
    TransformsTapes (tm.onWords mark)
      (fun _ ws => ws = Function.update (fun _ => []) (Fin.natAdd (k + 1) 0) (encIn a))
      (fun _ ws ws' emitted =>
        ws' = Function.update ws ((Fin.last k).castAdd 2) (encOut (f a)) ∧ emitted = [])
      (t a + (encOut (f a)).length + 6)
      (s a + 2 * (encIn a).length + 2 * (encOut (f a)).length + 3 * k + 15) :=
  (h a).onWords mark

/-- **The conversion theorem.** A tidily computable function is computed by some machine with binary
alphabet and finitely many states as a word-to-word tape transformer: it reads its input as a word
on some tape `i` and leaves the result as a word on a distinct tape `o`, leaving every other tape
blank and emitting nothing. -/
theorem ComputableTidilyInTimeAndSpace.exists_onWords {α β : Type*}
    {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {t s : α → ℕ}
    (h : ComputableTidilyInTimeAndSpace f encIn encOut t s) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM (k + 1 + 2) Bool State)
      (i o : Fin (k + 1 + 2)), i ≠ o ∧ ∀ a, TransformsTapes tm
        (fun _ ws => ws = Function.update (fun _ => []) i (encIn a))
        (fun _ ws ws' emitted => ws' = Function.update ws o (encOut (f a)) ∧ emitted = [])
        (t a + (encOut (f a)).length + 6)
        (s a + 2 * (encIn a).length + 2 * (encOut (f a)).length + 3 * k + 15) := by
  obtain ⟨k, State, hfin, tm, htm⟩ := h
  have : Finite State := hfin
  exact ⟨k, _, inferInstance, tm.onWords true, Fin.natAdd (k + 1) 0, (Fin.last k).castAdd 2,
    Fin.ne_of_val_ne (by simp only [Fin.val_natAdd, Fin.val_castAdd, Fin.val_last]; omega),
    fun a => (htm a).onWords true⟩

end Turing.MultiTapeTM
