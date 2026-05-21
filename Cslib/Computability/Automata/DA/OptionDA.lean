/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Computability.Automata.DA.Basic
public import Cslib.Computability.Automata.EpsilonNA.Basic
public import Cslib.Computability.Automata.EpsilonNA.ToNA
public import Cslib.Computability.Automata.NA.ToDA

/-! # OptionDA: DA with a single halting accept state

An `OptionDA` is a deterministic automaton with a unique accepting and halting state, codified as
`none : Option State`. Any `DA.FinAcc` can be converted into an `OptionDA` by (i) adding an
ε-transition from every accepting state to the `none` halting state, and then (ii) by transforming
the resulting `εNA` into an `OptionDA`.
-/

@[expose] public section

namespace Cslib.Automata

/-- A deterministic automaton with a single accepting, halting state, modelled as the `none` value
of `Option Symbol`. -/
structure OptionDA (State Symbol : Type*) where
  /-- The transition function of the automaton. -/
  tr : State → Symbol → Option State
  /-- The initial state of the automaton. -/
  start : State

variable {State Symbol : Type*}

namespace OptionDA

/-- Multistep transition function. -/
def mtr (a : OptionDA State Symbol) : State → List Symbol → Option State
  | s, [] => s
  | s, x :: xs => a.tr s x >>= (a.mtr · xs)

/-- An `OptionDA` accepts a string if its multistep transition function maps the start state and
the string to an accept state.

This is the standard string recognition performed by DFAs in the literature. -/
@[simp, scoped grind =]
instance : Acceptor (OptionDA State Symbol) Symbol where
  Accepts (a : OptionDA State Symbol) (xs : List Symbol) := a.mtr a.start xs = .none

end OptionDA

/-- Converts a `DA.FinAcc` into an `εNA` with an additional `none` state that acts as the unique
accepting and halting state. Every accepting state of the original automaton gains an ε-transition
to `none`, and all other transitions are lifted by `some`. -/
@[scoped grind =]
def DA.FinAcc.toOptionεNA (a : DA.FinAcc State Symbol) : εNA.FinAcc (Option State) Symbol where
  start := {some a.start}
  accept := {none}
  Tr
    -- Lift of original transitions
    | some s, some x, some s' => s' = a.tr s x
    -- Additional ε-transitions to the halting state.
    | some s, none, none => s ∈ a.accept
    | _, _, _ => False

/-- The `none` state in `DA.toOptionεNA` is the only accept state. -/
@[simp]
lemma DA.FinAcc.toOptionεNA_none_accept (a : DA.FinAcc State Symbol) :
    a.toOptionεNA.accept = {none} := rfl

/-- The `none` state in `DA.toOptionεNA` has no outgoing transitions. -/
@[scoped grind .]
lemma DA.FinAcc.toOptionεNA_none_tr (a : DA.FinAcc State Symbol)
    (μ : Option Symbol) (s : Option State) : ¬a.toOptionεNA.Tr none μ s := by grind

/-- The `none` state in `DA.toOptionεNA` has no outgoing transitions. -/
@[scoped grind .]
lemma DA.FinAcc.toOptionεNA_tr_none_iff {a : DA.FinAcc State Symbol}
    (h : a.toOptionεNA.Tr s μ s') : μ = none ↔ s' = none := by cases hμ : μ <;> grind

/-- The `none` state in `DA.toOptionεNA` has no outgoing transitions. -/
@[scoped grind .]
lemma DA.FinAcc.toOptionεNA_ε_τSTr_none {a : DA.FinAcc State Symbol}
    (h : a.toOptionεNA.τSTr s s') : s' = s ∨ s' = none := by
  cases h with
    | refl => simp
    | tail s₁ h =>
      apply toOptionεNA_tr_none_iff at h
      simp only [HasTau.τ, true_iff] at h
      simp [h]

/-- The `none` state in `DA.toOptionεNA` has no outgoing transitions. -/
@[scoped grind .]
lemma DA.FinAcc.toOptionεNA_ε_sTr_none {a : DA.FinAcc State Symbol}
    (h : a.toOptionεNA.STr s none s') : s' = s ∨ s' = none := by cases h <;> grind

lemma DA.FinAcc.toOptionεNA_start_εClosure {a : DA.FinAcc State Symbol} (h : a.start ∈ a.accept) :
    a.toOptionεNA.εClosure a.toOptionεNA.start = {some a.start, none} := by
  rw [show a.toOptionεNA.start = {some a.start} by rfl]
  simp [εNA.εClosure, LTS.τClosure, LTS.saturate, LTS.setImage, LTS.image, HasTau.τ]
  ext s
  apply Iff.intro <;> intro h
  · grind
  · simp only [Set.mem_setOf_eq]
    simp at h
    cases h with
      | inl h' =>
        rw [h']
        apply LTS.STr.refl
      | inr h' =>
        rw [h']
        simp [toOptionεNA]
        sorry

open Acceptor in
open scoped LTS εNA εNA.FinAcc in
/-- `DA.toOptionεNA` preserves the automaton's language. -/
theorem DA.FinAcc.toOptionεNA_language_eq {a : DA.FinAcc State Symbol} :
    language a.toOptionεNA = language a := by
  ext xs
  simp only [Acceptor.mem_language]
  simp only [Accepts]
  apply Iff.intro <;> intro h
  case mp =>
    sorry
  case mpr =>
    induction xs
    case nil =>
      exists a.start
      apply And.intro
      case left =>
        grind
      case right =>

        sorry
    case cons x xs =>
      sorry

namespace NA.FinAcc

def ofOptionFinAcc (a : NA.FinAcc (Option State) Symbol) : NA.FinAcc State Symbol where
  start := { s | some s ∈ a.start }
  Tr s x s' := a.Tr (some s) x (some s')
  accept := { s | ∃ x, a.Tr (some s) x none }

noncomputable def toOptionDA (a : NA.FinAcc State Symbol) : OptionDA (Set State) Symbol :=
  let da := a.toDAFinAcc
  { start := da.start
    tr S x :=
      let S' := da.tr S x
      open Classical in if S' ∈ da.accept then none else some S' }

end NA.FinAcc

noncomputable def DA.FinAcc.toOptionDA (a : DA.FinAcc State Symbol) :
    OptionDA (Set State) Symbol :=
  a.toOptionεNA.toNAFinAcc.ofOptionFinAcc.toOptionDA

open Acceptor in
-- open scoped NA.FinAcc in
theorem DA.FinAcc.toOptionDA_language_eq {a : DA.FinAcc State Symbol} :
    language a.toOptionDA = language a := by
  simp [toOptionDA]
  sorry

end Cslib.Automata
