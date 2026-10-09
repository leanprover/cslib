/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.TransformsTapes

/-!
# Tidy computations

A machine runs *tidily* when it halts having given its tapes back as it found them: every work
tape blank again, every head — work heads and the input head — back at its starting cell, only the
output grown by the emitted word. This is exactly the hypothesis that lets a combinator call a
machine without tracking anything beyond the word it emits.

Each tidy notion is *literally* a `Turing.MultiTapeTM.TransformsTapes` — the transformation taking
blank words to blank words, emitting the output — so the plumbing combinators (`imp`, `mono`,
`transformsTapes_seq`, `tapeEmb`) apply with no proof of its own. The three notions mirror
`Turing.MultiTapeTM.ComputesInTimeAndSpace`, `Turing.MultiTapeTM.ComputesFunInTimeAndSpace` and
`Turing.MultiTapeTM.ComputableInTimeAndSpace`, each the ordinary notion plus that cleanup
requirement.

## Main definitions

* `Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace`: a machine computes an output tidily.
* `Turing.MultiTapeTM.ComputesFunTidilyInTimeAndSpace`: a machine computes a function tidily.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace`: such a machine exists, with binary alphabet
  and finitely many states.

## Main results

* `Turing.MultiTapeTM.computesTidily_iff` and `Turing.MultiTapeTM.computesTidily_of_runFrom`: the
  equation form and how a concrete machine enters.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {tm : MultiTapeTM k Symbol State} {t s : ℕ}

/-! ### Tidy computations -/

/-- `ComputesTidilyInTimeAndSpace tm input output t s`: started on blank tapes, the machine halts
*tidily* — every work tape blank again, every work head back at cell `0` and the input head back
at the start of the input — having emitted `output`, within `t` steps and `s` work-tape cells.

An instance of `Turing.MultiTapeTM.TransformsTapes`; `Turing.MultiTapeTM.computesTidily_iff` is
the equation form. -/
abbrev ComputesTidilyInTimeAndSpace (tm : MultiTapeTM k Symbol State)
    (input output : List Symbol) (t s : ℕ) : Prop :=
  TransformsTapes tm (fun inp ws => inp = input ∧ ws = fun _ => [])
    (fun _ _ ws' emitted => ws' = (fun _ => []) ∧ emitted = output) t s

/-- **A tidy computation is an equation between word configurations.** Unfolding leaves the run on
blank tapes, the demand that it halt on blank tapes again with the input head back at the start,
and the space bound; the ambient output of `Turing.MultiTapeTM.TransformsTapes` is discharged by
`Turing.MultiTapeTM.transformsTapes_iff_nil_output`. -/
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

/-- **A single tidy run is a tape transformation.** This is how a concrete machine enters the
interface. -/
theorem computesTidily_of_runFrom {input output : List Symbol}
    (hrun : tm.runFrom (wordsCfg input (some tm.q₀) (fun _ => []) []) t =
      wordsCfg input none (fun _ => []) output)
    (hspace : tm.spaceUsed (wordsCfg input (some tm.q₀) (fun _ => []) []) t ≤ s) :
    tm.ComputesTidilyInTimeAndSpace input output t s :=
  computesTidily_iff.mpr ⟨hrun, hspace⟩

/-! ### Tidily computing a function -/

variable {α β : Type*}

/-- `ComputesFunTidilyInTimeAndSpace tm encIn encOut f t s`: for every `a`, the machine computes
`encOut (f a)` from `encIn a` tidily, within the bounds `t a` and `s a` —
`Turing.MultiTapeTM.ComputesFunInTimeAndSpace` plus the cleanup requirement. -/
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

end ComputesFunTidilyInTimeAndSpace

/-! ### Tidy computability -/

/-- A function is computable *tidily* within the input-indexed bounds by a machine with binary
alphabet and finitely many states: `Turing.MultiTapeTM.ComputableInTimeAndSpace` plus the cleanup
requirement. The two are *not* known to agree — recovering the tapes costs time and space that
this definition still charges to `t` and `s`. -/
def ComputableTidilyInTimeAndSpace (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool)
    (t s : α → ℕ) : Prop :=
  ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State),
    ComputesFunTidilyInTimeAndSpace tm encIn encOut f t s

namespace ComputableTidilyInTimeAndSpace

variable {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {t s : α → ℕ}

/-- Tidy computability is monotone in the resource bounds. -/
theorem mono (h : ComputableTidilyInTimeAndSpace f encIn encOut t s) {t' s' : α → ℕ}
    (ht : ∀ a, t a ≤ t' a) (hs : ∀ a, s a ≤ s' a) :
    ComputableTidilyInTimeAndSpace f encIn encOut t' s' := by
  obtain ⟨k, State, hfinite, tm, htm⟩ := h
  exact ⟨k, State, hfinite, tm, htm.mono ht hs⟩

end ComputableTidilyInTimeAndSpace

end Turing.MultiTapeTM
