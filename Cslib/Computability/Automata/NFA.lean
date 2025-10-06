/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Computability.Automata.NA

/-- A Nondeterministic Finite Automaton (NFA) is a nondeterministic automaton (NA)
over finite sets of states and symbols. -/
structure NFA (State : Type _) (Symbol : Type _) extends NA State Symbol where
  /-- The set of accepting states of the automaton. -/
  accept : Set State
  /-- The automaton is finite-state. -/
  finite_state : Finite State
  /-- The type of symbols (also called 'alphabet') is finite. -/
  finite_symbol : Finite Symbol

namespace NFA

/-- An NFA accepts a string if there is a multi-step accepting derivative with that trace from
the start state. -/
@[scoped grind]
def Accepts (nfa : NFA State Symbol) (xs : List Symbol) :=
  ∃ s ∈ nfa.start, ∃ s' ∈ nfa.accept, nfa.MTr s xs s'

/-- The language of an NFA is the set of strings that it accepts. -/
@[scoped grind]
def language (nfa : NFA State Symbol) : Set (List Symbol) :=
  { xs | nfa.Accepts xs }

/-- A string is accepted by an NFA iff it is in the language of the NFA. -/
@[scoped grind]
theorem accepts_mem_language (nfa : NFA State Symbol) (xs : List Symbol) :
  nfa.Accepts xs ↔ xs ∈ nfa.language := by rfl

end NFA
