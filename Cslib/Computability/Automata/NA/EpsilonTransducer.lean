/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Computability.Automata.NA.Basic
public import Cslib.Computability.Automata.Transducers.Transducer
public import Cslib.Foundations.Semantics.LTS.HasTau

/-! # Nondeterministic finite ε-transducers

Transducers based on `NA` with an invisible symbol in their input and output alphabets.
-/

@[expose] public section

namespace Cslib.Automata.NA

/-- A nondeterministic ε-transducer of finite strings where the input and output alphabets include
an invisible symbol, modelled as `HasTau.τ` (typically called `ε`). -/
structure εTransducer (State InSymbol OutSymbol : Type*)
    extends NA State (InSymbol × OutSymbol) where
  /-- The set of accepting states. -/
  accept : Set State

/-- Removes all `τ`s from a list. -/
@[scoped grind =]
def _root_.List.dropTaus [HasTau α] [DecidableEqTau α] (l : List α) : List α :=
  l.filter (· ≠ HasTau.τ)

variable [HasTau InSymbol] [HasTau OutSymbol]

namespace εTransducer

/-- An `εTransducer` translates `xs` into `ys` from state `s` to state `s'` if there is a
multistep transition from `s` to `s'` whose visible projection is `(xs, ys)`.
`MTransl` is short for Multistep Translation relation.
-/
def MTransl [DecidableEqTau InSymbol] [DecidableEqTau OutSymbol]
    (a : εTransducer State InSymbol OutSymbol) (s : State)
    (xs : List InSymbol) (ys : List OutSymbol) (s' : State) : Prop :=
  ∃ μs, a.MTr s μs s' ∧ (μs.map Prod.fst |>.dropTaus) = xs ∧ (μs.map Prod.snd |>.dropTaus) = ys

/-- An `NA.εTransducer` translates a finite string `xs` into a finite string `ys` if it has
a multistep transition whose visible projection is `(xs, ys)`.

This is the standard string translation performed by nondeterministic transducers, where
`HasTau.τ` symbols (epsilon transitions) are ignored in the input and output. -/
instance [DecidableEqTau InSymbol] [DecidableEqTau OutSymbol] :
    Transducer (εTransducer State InSymbol OutSymbol) InSymbol OutSymbol where
  Translates a xs ys := ∃ s ∈ a.start, ∃ s' ∈ a.accept, a.MTransl s xs ys s'

/-- Composition of multistep translations. -/
theorem MTransl.comp [DecidableEqTau InSymbol] [DecidableEqTau OutSymbol]
    {a : εTransducer State InSymbol OutSymbol}
    {s₁ s₂ s₃ : State} {xs xs' : List InSymbol} {ys ys' : List OutSymbol} :
    a.MTransl s₁ xs ys s₂ → a.MTransl s₂ xs' ys' s₃ →
    a.MTransl s₁ (xs ++ xs') (ys ++ ys') s₃ := by
  intro ⟨μs₁, h₁, e₁⟩ ⟨μs₂, h₂, e₂⟩
  refine ⟨μs₁ ++ μs₂, LTS.MTr.comp a.toLTS h₁ h₂, ?_⟩
  grind

end εTransducer

end Cslib.Automata.NA
