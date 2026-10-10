/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.TransformsTapes

/-!
# Tidy computations

A machine computes *tidily* if it halts with its tapes as it found them: every work tape blank,
every work head and the input head back at its starting cell. Only the output has grown, by the
computed word. A combinator can therefore run a tidy machine as a subroutine and rely on nothing
but the word it emits.

A tidy computation is defined as a `Turing.MultiTapeTM.TransformsTapes` from blank work tapes to
blank work tapes, so the lemmas about tape transformations apply to it directly. The three
notions below add tidiness to `Turing.MultiTapeTM.ComputesInTimeAndSpace`,
`Turing.MultiTapeTM.ComputesFunInTimeAndSpace` and `Turing.MultiTapeTM.ComputableInTimeAndSpace`.

## Main definitions

* `Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace`: a machine computes an output tidily.
* `Turing.MultiTapeTM.ComputesFunTidilyInTimeAndSpace`: a machine computes a function tidily.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace`: some machine with binary alphabet and
  finitely many states computes a function tidily.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpaceOfLength`: the same, with bounds on the length
  of the encoded input.

## Main results

* `Turing.MultiTapeTM.computesTidily_iff`: a tidy computation is a single run between
  `Turing.MultiTapeTM.wordsCfg` configurations, together with a space bound.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.computableInTimeAndSpace`: a tidily
  computable function is computable, within the same bounds.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {tm : MultiTapeTM k Symbol State} {t s : ℕ}

/-! ### Tidy computations -/

/-- `ComputesTidilyInTimeAndSpace tm input output t s`: started on `input` with blank work tapes,
`tm` halts within `t` steps and `s` work-tape cells, having emitted `output`, with every work tape
blank and every head back at its starting cell. -/
abbrev ComputesTidilyInTimeAndSpace (tm : MultiTapeTM k Symbol State)
    (input output : List Symbol) (t s : ℕ) : Prop :=
  TransformsTapes tm (fun inp ws => inp = input ∧ ws = fun _ => [])
    (fun _ _ ws' emitted => ws' = (fun _ => []) ∧ emitted = output) t s

/-- A tidy computation is a single run between `Turing.MultiTapeTM.wordsCfg` configurations with
blank work tapes, which emits the output, together with the space bound. -/
theorem computesTidily_iff {input output : List Symbol} :
    tm.ComputesTidilyInTimeAndSpace input output t s ↔
      tm.runFrom (wordsCfg input (some tm.q₀) (fun _ => []) []) t =
          wordsCfg input none (fun _ => []) output ∧
        tm.spaceUsed (wordsCfg input (some tm.q₀) (fun _ => []) []) t ≤ s := by
  rw [ComputesTidilyInTimeAndSpace, transformsTapes_iff_nil_output]
  constructor
  · intro h
    obtain ⟨ws', emitted, hrun, ⟨rfl, rfl⟩, hspace⟩ := h input (fun _ => []) ⟨rfl, rfl⟩
    exact ⟨hrun, hspace⟩
  · rintro ⟨hrun, hspace⟩ inp ws ⟨rfl, rfl⟩
    exact ⟨fun _ => [], output, hrun, ⟨rfl, rfl⟩, hspace⟩

/-- A tidy computation is a computation in the sense of
`Turing.MultiTapeTM.ComputesInTimeAndSpace`. -/
theorem ComputesTidilyInTimeAndSpace.computesInTimeAndSpace {input output : List Symbol}
    (h : tm.ComputesTidilyInTimeAndSpace input output t s) :
    tm.ComputesInTimeAndSpace input output t s := by
  obtain ⟨hrun, hspace⟩ := computesTidily_iff.mp h
  rw [← Cfg.init_eq_wordsCfg] at hrun hspace
  have hhalt : (tm.runFrom (tm.initCfg input) t).Halted := by rw [MultiTapeNTM.initCfg, hrun]; rfl
  exact ⟨⟨t, hhalt, by rw [MultiTapeNTM.initCfg, hrun]; rfl⟩, runsInTime_iff_halted.mpr hhalt,
    runsInSpace_of_halted hhalt hspace⟩

/-! ### Tidily computing a function -/

variable {α β : Type*}

/-- `ComputesFunTidilyInTimeAndSpace tm encIn encOut f t s`: for every `a`, the machine computes
`encOut (f a)` from `encIn a` tidily, within `t a` steps and `s a` cells. -/
def ComputesFunTidilyInTimeAndSpace (tm : MultiTapeTM k Symbol State)
    (encIn : α ↪ List Symbol) (encOut : β ↪ List Symbol) (f : α → β) (t s : α → ℕ) : Prop :=
  ∀ a, tm.ComputesTidilyInTimeAndSpace (encIn a) (encOut (f a)) (t a) (s a)

namespace ComputesFunTidilyInTimeAndSpace

variable {encIn : α ↪ List Symbol} {encOut : β ↪ List Symbol} {f : α → β} {t s : α → ℕ}

/-- Resource bounds can be weakened independently on every input. -/
theorem mono (h : ComputesFunTidilyInTimeAndSpace tm encIn encOut f t s) {t' s' : α → ℕ}
    (ht : ∀ a, t a ≤ t' a) (hs : ∀ a, s a ≤ s' a) :
    ComputesFunTidilyInTimeAndSpace tm encIn encOut f t' s' :=
  fun a => (h a).mono (ht a) (hs a)

/-- A tidy computation of a function is a computation of it. -/
theorem computesFunInTimeAndSpace (h : ComputesFunTidilyInTimeAndSpace tm encIn encOut f t s) :
    tm.ComputesFunInTimeAndSpace encIn encOut f t s :=
  fun a => (h a).computesInTimeAndSpace

end ComputesFunTidilyInTimeAndSpace

/-! ### Tidy computability -/

/-- Some machine with binary alphabet and finitely many states computes `f` tidily within the
bounds `t` and `s`. Unlike `Turing.MultiTapeTM.ComputableInTimeAndSpace`, the cost of restoring the
tapes is included in the bounds. -/
def ComputableTidilyInTimeAndSpace (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool)
    (t s : α → ℕ) : Prop :=
  ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State),
    ComputesFunTidilyInTimeAndSpace tm encIn encOut f t s

/-- `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace` with the bounds `t` and `s` evaluated at the
length of the encoded input: the tidy analog of
`Turing.MultiTapeTM.ComputableInTimeAndSpaceOfLength`. -/
abbrev ComputableTidilyInTimeAndSpaceOfLength (f : α → β) (encIn : α ↪ List Bool)
    (encOut : β ↪ List Bool) (t s : ℕ → ℕ) : Prop :=
  ComputableTidilyInTimeAndSpace f encIn encOut
    (fun a => t (encIn a).length) (fun a => s (encIn a).length)

namespace ComputableTidilyInTimeAndSpace

variable {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {t s : α → ℕ}

/-- Tidy computability is monotone in the resource bounds. -/
theorem mono (h : ComputableTidilyInTimeAndSpace f encIn encOut t s) {t' s' : α → ℕ}
    (ht : ∀ a, t a ≤ t' a) (hs : ∀ a, s a ≤ s' a) :
    ComputableTidilyInTimeAndSpace f encIn encOut t' s' := by
  obtain ⟨k, State, hfinite, tm, htm⟩ := h
  exact ⟨k, State, hfinite, tm, htm.mono ht hs⟩

/-- A tidily computable function is computable. -/
theorem computableInTimeAndSpace (h : ComputableTidilyInTimeAndSpace f encIn encOut t s) :
    ComputableInTimeAndSpace f encIn encOut t s := by
  obtain ⟨k, State, hfinite, tm, htm⟩ := h
  exact ⟨k, State, hfinite, tm, htm.computesFunInTimeAndSpace⟩

end ComputableTidilyInTimeAndSpace

end Turing.MultiTapeTM
