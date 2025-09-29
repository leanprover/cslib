/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Computability.Automata.DA
import Cslib.Foundations.Semantics.LTS.Basic

set_option linter.style.longLine false in
/-! # Deterministic Finite-State Automata

A Deterministic Finite Automaton (DFA) is a finite-state machine that accepts or rejects
a finite string.

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman, *Introduction to Automata Theory, Languages, and Computation*][Hopcroft2006]
-/

/-- A Deterministic Finite-State Automaton (DFA) consists of a labelled transition function
`tr` over finite sets of states and labels (called symbols), a starting state `start` and a finite
set of accepting states `accept`. -/
structure DFA (State : Type _) (Symbol : Type _) extends DA State Symbol where
  /-- Accept states. -/
  accept : Finset State
  /-- The automaton is finite-state. -/
  finite_state : Finite State
  /-- The type of symbols (also called 'alphabet') is finite. -/
  finite_symbol : Finite Symbol

namespace DFA

/-- A DA accepts a trace if there is a multi-step accepting derivative with that trace from
the start state. -/
@[grind]
def Accepts (dfa : DFA State Symbol) (μs : List Symbol) :=
  (dfa.mtr dfa.start μs) ∈ dfa.accept

/-- The language of a DA is the set of traces that it accepts. -/
@[grind]
def language (dfa : DFA State Symbol) : Set (List Symbol) :=
  { μs | dfa.Accepts μs }

/-- A trace is accepted by a DA iff it is in the language of the DA. -/
@[grind]
theorem accepts_mem_language (dfa : DFA State Symbol) (μs : List Symbol) :
  dfa.Accepts μs ↔ μs ∈ dfa.language := by rfl

section LTS

/-- The LTS induced by a DFA is finite-state. -/
@[grind]
theorem toLTS_finiteState (dfa : DFA State Symbol) : dfa.toLTS.FiniteState :=
  dfa.finite_state

end LTS

end DFA
