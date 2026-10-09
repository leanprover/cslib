/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Sequential

/-!
# Tidy computations

A machine runs *tidily* when it halts having given its tapes back as it found them: every work
tape blank again, every work head returned to cell `0` and the input head returned to the start of
the input. Only the output has changed, by the word the machine appended to it.

"Tidy" is about the heads as much as about the contents: a machine that erases its work tapes but
leaves a head at the far end of the scratch it used is not tidy, and a combinator that calls it
twice would have to say where the heads ended up. Tidiness is exactly the hypothesis that lets a
combinator call a machine without tracking anything beyond the word it emits — which is why it is
the right shape for the body of a loop, or for either half of a sequence.

## The two readings

Tidiness is said once, as a tape transformation, and then read at two levels:

* `Turing.MultiTapeTM.TransformsTidy` is the *specification*: the tape transformation that takes
  blank words to blank words and emits a word related to the input by `R`, on the inputs
  satisfying `P`. Being an instance of `Turing.MultiTapeTM.TransformsTapes`, it inherits
  `Turing.MultiTapeTM.TransformsTapes.imp`, `Turing.MultiTapeTM.transformsTapes_seq` and
  `Turing.MultiTapeTM.TransformsTapes.tapeEmb` with no proof of its own.
* `Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace` and the two abstractions above it are the
  *computational* reading, mirroring `Turing.MultiTapeTM.ComputesInTimeAndSpace`,
  `Turing.MultiTapeTM.ComputesFunInTimeAndSpace` and
  `Turing.MultiTapeTM.ComputableInTimeAndSpace` rung for rung. Each is the ordinary notion plus
  the requirement that the machine clean up after itself.

Saying the computational notions *as* tape transformations is what lets the combinators of the
plumbing layer consume a whole computation directly, with no change of vocabulary. The equation
forms are `Turing.MultiTapeTM.transformsTidy_iff` and
`Turing.MultiTapeTM.computesTidily_iff`; a concrete machine enters through
`Turing.MultiTapeTM.computesTidily_of_runFrom`.

## Emission is what makes this a notion

A tidy transformation would be vacuous if it could not emit. Blank words on both sides and an
input head back at the start pin down every component of the halting configuration except the
output, so without the output a tidy specification could describe only *that* the machine halts in
the bounds, never *what* it computed. This is why
`Turing.MultiTapeTM.TransformsTapes` describes the word a machine appends rather than requiring
the output to be untouched.

## What a loop still needs

A tidy machine is not yet a loop body: with every work tape blank at both ends and the input tape
read-only, nothing can pass from one round to the next, and a loop that inspects a tape to decide
whether to stop would always read a blank. Two further pieces turn a tidy computation into a loop
body, neither of them in this file:

* the adapters `Turing.MultiTapeTM.inputFromTape` and `Turing.MultiTapeTM.outputToTape`, which
  make a machine read its input from a work tape and write its output to one. Neither yet lands in
  the `Turing.MultiTapeTM.wordsCfg` normal form — `inputFromTape` wants its flag tape marked at
  cell `-1`, and `outputToTape` leaves its head at the write frontier rather than at `0` — so a
  flag-setting and a rewinding variant of the two are needed to state the composite tidily;
* a branching primitive, to decide from a tape symbol whether to run another round, and bounds
  given as families rather than numbers.

## Main definitions

* `Turing.MultiTapeTM.TransformsTidy`: the tidy tape transformation.
* `Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace`: a machine computes an output tidily.
* `Turing.MultiTapeTM.ComputesFunTidilyInTimeAndSpace`: a machine computes a function tidily.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace`: such a machine exists, with binary alphabet
  and finitely many states.

## Main results

* `Turing.MultiTapeTM.transformsTidy_iff`, `Turing.MultiTapeTM.computesTidily_iff`: the equation
  forms, and with them `Turing.MultiTapeTM.computesTidily_of_runFrom`, how a concrete machine
  enters.
* `Turing.MultiTapeTM.transformsTidy_seq`, `Turing.MultiTapeTM.computesTidily_seq`: two tidy
  machines compose, and their emitted words concatenate.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {tm : MultiTapeTM k Symbol State} {t s : ℕ}

/-! ### Tidy tape transformations -/

/-- `TransformsTidy tm P R t s`: on every input satisfying `P`, the machine started on blank tapes
halts *tidily* — every work tape blank again, every work head back at cell `0` and the input head
back at the start of the input — having emitted a word related to the input by `R`, within `t`
steps and `s` work-tape cells.

This is not a notion of its own: it is literally the tape transformation that takes blank words to
blank words, so every combinator of the plumbing layer applies to it unchanged. -/
abbrev TransformsTidy (tm : MultiTapeTM k Symbol State) (P : List Symbol → Prop)
    (R : List Symbol → List Symbol → Prop) (t s : ℕ) : Prop :=
  TransformsTapes tm (fun input ws => P input ∧ ws = fun _ => [])
    (fun input _ ws' emitted => ws' = (fun _ => []) ∧ R input emitted) t s

/-- **Tidiness is an equation between word configurations.** Unfolding the specification leaves
the run of the machine on blank tapes, the demand that it halt on blank tapes again, and the space
bound. The ambient output of `Turing.MultiTapeTM.TransformsTapes` has already been discharged by
`Turing.MultiTapeTM.transformsTapes_iff_nil_output`, so nothing of it survives here. -/
theorem transformsTidy_iff {P : List Symbol → Prop} {R : List Symbol → List Symbol → Prop} :
    TransformsTidy tm P R t s ↔
      ∀ input, P input → ∃ emitted, R input emitted ∧
        tm.runFrom (wordsCfg input (some tm.q₀) (fun _ => []) []) t =
          wordsCfg input none (fun _ => []) emitted ∧
        tm.spaceUsed (wordsCfg input (some tm.q₀) (fun _ => []) []) t ≤ s := by
  rw [TransformsTidy, transformsTapes_iff_nil_output]
  constructor
  · rintro h input hP
    obtain ⟨ws', emitted, hrun, ⟨rfl, hR⟩, hspace⟩ := h input (fun _ => []) ⟨hP, rfl⟩
    exact ⟨emitted, hR, hrun, hspace⟩
  · rintro h input ws ⟨hP, rfl⟩
    obtain ⟨emitted, hR, hrun, hspace⟩ := h input hP
    exact ⟨fun _ => [], emitted, hrun, ⟨rfl, hR⟩, hspace⟩

variable {State₀ State₁ : Type*} {tm₀ : MultiTapeTM k Symbol State₀}
  {tm₁ : MultiTapeTM k Symbol State₁}

/-- **Two tidy machines compose, and their emitted words concatenate.** The whole proof is a
reading of `Turing.MultiTapeTM.transformsTapes_seq`: the first machine hands the second exactly
the blank tapes its precondition asks for. This is the payoff of stating tidiness as a tape
transformation — the combinator layer needs to know nothing about tidiness. -/
theorem transformsTidy_seq {P₀ P₁ : List Symbol → Prop}
    {R₀ R₁ : List Symbol → List Symbol → Prop} {t₀ s₀ t₁ s₁ : ℕ}
    (h₀ : TransformsTidy tm₀ P₀ R₀ t₀ s₀) (h₁ : TransformsTidy tm₁ P₁ R₁ t₁ s₁)
    (hmid : ∀ input, P₀ input → P₁ input) :
    TransformsTidy (tm₀.seq tm₁) P₀
      (fun input emitted => ∃ e₀ e₁, R₀ input e₀ ∧ R₁ input e₁ ∧ emitted = e₀ ++ e₁)
      (t₀ + t₁) (s₀ + s₁) := by
  refine (transformsTapes_seq h₀ h₁ ?_).imp (fun _ _ => id) ?_ le_rfl le_rfl
  · rintro input ws ws' emitted ⟨hP, -⟩ ⟨rfl, -⟩
    exact ⟨hmid input hP, rfl⟩
  · rintro input ws ws'' emitted - ⟨ws', e₀, e₁, ⟨rfl, hR₀⟩, ⟨rfl, hR₁⟩, rfl⟩
    exact ⟨rfl, e₀, e₁, hR₀, hR₁, rfl⟩

/-! ### Tidy computations -/

/-- `ComputesTidilyInTimeAndSpace tm input output t s`: started on blank tapes, the machine halts
*tidily* — every work tape blank again, every work head back at cell `0` and the input head back
at the start of the input — having emitted `output`, within `t` steps and `s` work-tape cells.

This is `Turing.MultiTapeTM.ComputesInTimeAndSpace` plus the requirement that the machine clean up
after itself, said as the tape transformation it is: the one about a single input.
`Turing.MultiTapeTM.computesTidily_iff` is the equation form. -/
abbrev ComputesTidilyInTimeAndSpace (tm : MultiTapeTM k Symbol State)
    (input output : List Symbol) (t s : ℕ) : Prop :=
  TransformsTidy tm (fun inp => inp = input) (fun _ emitted => emitted = output) t s

/-- **A tidy computation is an equation between word configurations.** -/
theorem computesTidily_iff {input output : List Symbol} :
    tm.ComputesTidilyInTimeAndSpace input output t s ↔
      tm.runFrom (wordsCfg input (some tm.q₀) (fun _ => []) []) t =
          wordsCfg input none (fun _ => []) output ∧
        tm.spaceUsed (wordsCfg input (some tm.q₀) (fun _ => []) []) t ≤ s := by
  rw [ComputesTidilyInTimeAndSpace, transformsTidy_iff]
  constructor
  · intro h
    obtain ⟨emitted, rfl, hrun, hspace⟩ := h input rfl
    exact ⟨hrun, hspace⟩
  · rintro ⟨hrun, hspace⟩ inp rfl
    exact ⟨output, rfl, hrun, hspace⟩

/-- **A single tidy run is a tape transformation.** This is how a concrete machine enters the
interface. -/
theorem computesTidily_of_runFrom {input output : List Symbol}
    (hrun : tm.runFrom (wordsCfg input (some tm.q₀) (fun _ => []) []) t =
      wordsCfg input none (fun _ => []) output)
    (hspace : tm.spaceUsed (wordsCfg input (some tm.q₀) (fun _ => []) []) t ≤ s) :
    tm.ComputesTidilyInTimeAndSpace input output t s :=
  computesTidily_iff.mpr ⟨hrun, hspace⟩

/-- **Two tidy computations compose, and their outputs concatenate.** -/
theorem computesTidily_seq {input output₀ output₁ : List Symbol} {t₀ s₀ t₁ s₁ : ℕ}
    (h₀ : tm₀.ComputesTidilyInTimeAndSpace input output₀ t₀ s₀)
    (h₁ : tm₁.ComputesTidilyInTimeAndSpace input output₁ t₁ s₁) :
    (tm₀.seq tm₁).ComputesTidilyInTimeAndSpace input (output₀ ++ output₁) (t₀ + t₁) (s₀ + s₁) :=
  (transformsTidy_seq h₀ h₁ fun _ => id).imp (fun _ _ => id)
    (by rintro _ _ _ _ - ⟨rfl, _, _, rfl, rfl, rfl⟩; exact ⟨rfl, rfl⟩) le_rfl le_rfl

/-- **The machine that does nothing computes nothing, tidily.** Its heads never move, so it is
tidy for the reason that it never disturbs anything, and it checks that the notion is inhabited
exactly as intended. -/
theorem computesTidily_nop (k : ℕ) (Symbol : Type*) (input : List Symbol) :
    (nop k Symbol).ComputesTidilyInTimeAndSpace input [] 1 k :=
  (transformsTapes_nop k Symbol).imp (fun _ _ _ => trivial)
    (by rintro _ _ _ _ ⟨-, rfl⟩ ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩) le_rfl le_rfl

/-! ### Tidily computing a function -/

variable {α β : Type*}

/-- `ComputesFunTidilyInTimeAndSpace tm encIn encOut f t s`: for every `a`, the machine computes
`encOut (f a)` from `encIn a` tidily, within the bounds `t a` and `s a`.

This is `Turing.MultiTapeTM.ComputesFunInTimeAndSpace` plus the requirement that the machine clean
up after itself. It is a *family* of tape transformations over one fixed machine, exactly as the
bounds of the plumbing layer are families whenever they depend on the data. -/
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
alphabet and finitely many states: the machine cleans up after itself, so a combinator may call it
and then go on using the tapes.

This is `Turing.MultiTapeTM.ComputableInTimeAndSpace` plus that requirement; the two are *not*
known to agree, because recovering the tapes costs time and space that this definition still
charges to `t` and `s`. -/
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
