/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Ching-Tsun Chou
-/

import Cslib.Computability.Automata.DA
import Cslib.Computability.Languages.Language

/-! # Deterministic Finite-State Automata

A Deterministic Finite Automaton (DFA) is a finite-state machine that accepts or rejects
a finite string.
-/

namespace Cslib

open List Prod
open scoped DA Language

/-- A Deterministic Finite Automaton (DFA) consists of a labelled transition function
`tr` over finite sets of states and labels (called symbols), a starting state `start` and a finite
set of accepting states `accept`. -/
structure DFA (State : Type _) (Symbol : Type _) extends DA State Symbol where
  /-- The set of accepting states of the automaton. -/
  accept : Set State
  /-- The automaton is finite-state. -/
  finite_state : Finite State
  /-- The type of symbols (also called 'alphabet') is finite. -/
  finite_symbol : Finite Symbol

namespace DFA

variable {State State1 State2 : Type _} {Symbol : Type _}

/-- A DFA accepts a string if there is a multi-step accepting derivative with that trace from
the start state. -/
@[scoped grind →]
def Accepts (dfa : DFA State Symbol) (xs : List Symbol) :=
  dfa.mtr dfa.start xs ∈ dfa.accept

/-- The language of a DFA is the set of strings that it accepts. -/
@[scoped grind =]
def language (dfa : DFA State Symbol) : Language Symbol :=
  { xs | dfa.Accepts xs }

/-- A string is in the language of a DFA iff it is accepted by the DFA. -/
@[scoped grind =]
theorem mem_language (dfa : DFA State Symbol) (xs : List Symbol) :
  xs ∈ dfa.language ↔ dfa.Accepts xs := Iff.rfl

@[scoped grind =]
def zero [Finite Symbol] : DFA Unit Symbol where
  start := ()
  tr := fun _ _ ↦ ()
  accept := ∅
  finite_state := by infer_instance
  finite_symbol := by infer_instance

@[simp, scoped grind =]
theorem zero_lang [Finite Symbol] : zero.language = (0 : Language Symbol) := by
  grind

@[scoped grind =]
def one [Finite Symbol] : DFA (Fin 2) Symbol where
  start := 0
  tr := fun _ _ ↦ 1
  accept := {0}
  finite_state := by infer_instance
  finite_symbol := by infer_instance

@[simp, scoped grind =]
theorem one_lang [Finite Symbol] : one.language = (1 : Language Symbol) := by
  ext xs ; constructor
  · intro h ; by_contra h'
    have := dropLast_append_getLast h'
    grind
  · rw [Language.mem_one]
    grind

@[scoped grind =]
def compl (dfa : DFA State Symbol) : DFA State Symbol :=
  { dfa with accept := (dfa.accept)ᶜ }

@[simp, scoped grind =]
theorem compl_lang (dfa : DFA State Symbol) : dfa.compl.language = (dfa.language)ᶜ := by
  grind

@[scoped grind =]
def prod (dfa1 : DFA State1 Symbol) (dfa2 : DFA State2 Symbol) (acc : Set (State1 × State2))
  : DFA (State1 × State2) Symbol where
  toDA := DA.prod dfa1.toDA dfa2.toDA
  accept := acc
  finite_state := by
    have := dfa1.finite_state
    have := dfa2.finite_state
    infer_instance
  finite_symbol := dfa1.finite_symbol

@[scoped grind =]
def inf (dfa1 : DFA State1 Symbol) (dfa2 : DFA State2 Symbol) :=
    dfa1.prod dfa2 (fst ⁻¹' dfa1.accept ∩ snd ⁻¹' dfa2.accept)

@[scoped grind =]
def add (dfa1 : DFA State1 Symbol) (dfa2 : DFA State2 Symbol) :=
    dfa1.prod dfa2 (fst ⁻¹' dfa1.accept ∪ snd ⁻¹' dfa2.accept)

@[simp, scoped grind =]
theorem inf_lang (dfa1 : DFA State1 Symbol) (dfa2 : DFA State2 Symbol) :
    (dfa1.inf dfa2).language = dfa1.language ⊓ dfa2.language := by
  ext xs ; grind

@[simp, scoped grind =]
theorem add_lang (dfa1 : DFA State1 Symbol) (dfa2 : DFA State2 Symbol) :
    (dfa1.add dfa2).language = dfa1.language + dfa2.language := by
  ext xs ; grind [Language.mem_add]

end DFA

end Cslib
