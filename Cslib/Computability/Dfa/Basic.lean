/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Foundations.Semantics.Lts.Basic

/-- A Deterministic Finite-State Automaton (DFA) consists of a labelled transition function
`tr` over a finite set of states. It has a starting state `start` and a finite
set of accepting states `accept`. -/
structure Dfa (State : Type _) (Label : Type _) where
  -- The transition function of the automaton
  tr : State → Label → State
  -- Start state
  start : State
  -- Accept states
  accept : Finset State
  -- The automaton is finite-state
  finite_state : Finite State

namespace Dfa

/-- `Dfa` is a special case of `Lts`. -/
@[grind]
def toLts (dfa : Dfa State Label) : Lts State Label :=
  Lts.mk (fun s1 μ s2 => dfa.tr s1 μ = s2)

instance : Coe (Dfa State Label) (Lts State Label) where
  coe := toLts

/-- The LTS induced by a DFA is deterministic. -/
@[grind]
theorem toLts_deterministic (dfa : Dfa State Label) : dfa.toLts.Deterministic := by
  intro s1 μ s2 s3 htr2 htr3
  by_cases heq : s2 = s3
  case pos => exact heq
  case neg =>
    cases htr2
    cases htr3
    rfl

/-- The LTS induced by a DFA is finite-state. -/
@[grind]
theorem toLts_finiteState (dfa : Dfa State Label) : dfa.toLts.FiniteState :=
  dfa.finite_state

/-- A DFA accepts a trace if there is a multi-step accepting derivative with that trace from
the start state. -/
@[grind]
def Accepts (dfa : Dfa State Label) (μs : List Label) :=
  ∃ s ∈ dfa.accept, dfa.toLts.MTr dfa.start μs s

/-- The language of a DFA is the set of traces that it accepts. -/
@[grind]
def language (dfa : Dfa State Label) : Set (List Label) :=
  fun μs => dfa.Accepts μs

/-- A trace is accepted by a DFA iff it is in the language of the DFA. -/
@[grind]
theorem accepts_mem_language (dfa : Dfa State Label) (μs : List Label) :
  dfa.Accepts μs ↔ μs ∈ dfa.language := by
  constructor <;> intro h
  case mp =>
    exact h
  case mpr =>
    rcases h with ⟨s, h1, h2⟩
    exists s

end Dfa
