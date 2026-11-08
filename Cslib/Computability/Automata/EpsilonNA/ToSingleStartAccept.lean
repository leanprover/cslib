/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Yusuf Demir
-/

module

public import Cslib.Computability.Automata.EpsilonNA.Basic
public import Cslib.Foundations.Semantics.LTS.Simulation

/-! # Translation of εNA into εNA with a single start and a single accept state

Defines the transformation `toSingleStartAccept` for `εNA.FinAcc`, which adds a start state with
ε-transitions to the original start states and no incoming transitions, and an accept state with
ε-transitions from the original accept states and no outgoing transitions. The transformation
preserves the language of the automaton.
-/

@[expose] public section

namespace Cslib.Automata.εNA.FinAcc

variable {State Symbol : Type*}

/-- Any `εNA.FinAcc` can be converted into an `εNA.FinAcc` with a single start state and a single
accept state. The original states are wrapped in `inr`, and the fresh state `inl b` is accepting
exactly when `b`: the start state `inl false` has ε-transitions to the original start states, and
the original accept states have ε-transitions to the accept state `inl true`. -/
def toSingleStartAccept (a : εNA.FinAcc State Symbol) : εNA.FinAcc (Bool ⊕ State) Symbol where
  start := {.inl false}
  accept := {.inl true}
  Tr
    | .inr s, μ, .inr s' => a.Tr s μ s'
    | .inl false, none, .inr s => s ∈ a.start
    | .inr s, none, .inl true => s ∈ a.accept
    | _, _, _ => False

variable {a : εNA.FinAcc State Symbol}

theorem toSingleStartAccept_start : a.toSingleStartAccept.start = {.inl false} := rfl

theorem toSingleStartAccept_accept : a.toSingleStartAccept.accept = {.inl true} := rfl

theorem toSingleStartAccept_tr_inr_inr {s s' : State} {μ : Option Symbol} :
    a.toSingleStartAccept.Tr (.inr s) μ (.inr s') ↔ a.Tr s μ s' := Iff.rfl

theorem toSingleStartAccept_tr_start {s : State} (hs : s ∈ a.start) :
    a.toSingleStartAccept.Tr (.inl false) none (.inr s) := hs

theorem toSingleStartAccept_tr_accept {s : State} (hs : s ∈ a.accept) :
    a.toSingleStartAccept.Tr (.inr s) none (.inl true) := hs

/-- The transitions from the start state are ε-transitions to the original start states. -/
theorem toSingleStartAccept_tr_inl_false {μ : Option Symbol} {y : Bool ⊕ State}
    (h : a.toSingleStartAccept.Tr (.inl false) μ y) :
    μ = none ∧ ∃ s, y = .inr s ∧ s ∈ a.start := by
  rcases y with (_ | _) | s <;> cases μ <;> simp_all [toSingleStartAccept]

/-- No transition leads to the start state. -/
theorem toSingleStartAccept_not_tr_inl_false {x : Bool ⊕ State} {μ : Option Symbol} :
    ¬a.toSingleStartAccept.Tr x μ (.inl false) := by
  rcases x with (_ | _) | s <;> cases μ <;> simp [toSingleStartAccept]

/-- No transition leaves the accept state. -/
theorem toSingleStartAccept_not_tr_inl_true {μ : Option Symbol} {y : Bool ⊕ State} :
    ¬a.toSingleStartAccept.Tr (.inl true) μ y := by
  rcases y with (_ | _) | s <;> cases μ <;> simp [toSingleStartAccept]

/-- A run from an original state to the accept state is a run of the original automaton to an
original accept state, followed by the ε-transition to the accept state. -/
theorem toSingleStartAccept_mTr_inr_inl_true {s : State} {μs : List (Option Symbol)}
    (h : a.toSingleStartAccept.MTr (.inr s) μs (.inl true)) :
    ∃ t ∈ a.accept, ∃ μs', μs = μs' ++ [none] ∧ a.MTr s μs' t := by
  induction μs generalizing s with
  | nil => cases h
  | cons μ μs ih =>
    obtain ⟨z, htr, h'⟩ := LTS.MTr.cons_iff.mp h
    rcases z with (_ | _) | s''
    · exact absurd htr toSingleStartAccept_not_tr_inl_false
    · cases μs with
      | nil =>
        cases μ with
        | none => exact ⟨s, htr, [], rfl, .refl⟩
        | some x => exact absurd htr (by simp [toSingleStartAccept])
      | cons μ' μs' =>
        obtain ⟨z', htr', -⟩ := LTS.MTr.cons_iff.mp h'
        exact absurd htr' toSingleStartAccept_not_tr_inl_true
    · obtain ⟨t, ht, μs', rfl, hrun⟩ := ih h'
      exact ⟨t, ht, μ :: μs', rfl, .stepL (toSingleStartAccept_tr_inr_inr.mp htr) hrun⟩

open Acceptor in
/-- `toSingleStartAccept` preserves the language of the input automaton. -/
@[scoped grind =]
theorem toSingleStartAccept_language_eq : language a.toSingleStartAccept = language a := by
  ext xs
  rw [mem_language_iff, mem_language_iff]
  constructor
  · rintro ⟨_, hs', _, ht', μs, rfl, h⟩
    obtain rfl := Set.mem_singleton_iff.mp hs'
    obtain rfl := Set.mem_singleton_iff.mp ht'
    cases μs with
    | nil => cases h
    | cons μ μs =>
      obtain ⟨y, htr, h'⟩ := LTS.MTr.cons_iff.mp h
      obtain ⟨rfl, s, rfl, hs⟩ := toSingleStartAccept_tr_inl_false htr
      obtain ⟨t, ht, μs', rfl, hrun⟩ := toSingleStartAccept_mTr_inr_inl_true h'
      exact ⟨s, hs, t, ht, μs', by simp [List.reduceOption_append], hrun⟩
  · rintro ⟨s, hs, t, ht, μs, rfl, h⟩
    refine ⟨.inl false, Set.mem_singleton _, .inl true, Set.mem_singleton _,
      none :: (μs ++ [none]), by simp [List.reduceOption_append], ?_⟩
    have hinr : LTS.IsSimulationMap a.toLTS a.toSingleStartAccept.toLTS Sum.inr :=
      fun _ _ _ => toSingleStartAccept_tr_inr_inr.mpr
    exact .stepL (toSingleStartAccept_tr_start hs)
      ((hinr.sim_trace h).comp _ (.single _ (toSingleStartAccept_tr_accept ht)))

end Cslib.Automata.εNA.FinAcc
