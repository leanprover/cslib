/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Computability.Automata.DA
import Cslib.Computability.Languages.Language

/-! # Deterministic Finite-State Automata

A Deterministic Finite Automaton (DFA) is a finite-state machine that accepts or rejects
a finite string.

This is the bundled version of `DA` with an exact acceptor and finiteness assumptions.
It is provided as a utility for applications and as a reference to the established terminology in
the literature. To prove results about this kind of machines, please use the unbundled version `DA`
and be precise with the required assumptions.

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][Hopcroft2006]
-/

namespace Cslib

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

variable {State : Type _} {Symbol : Type _}

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

end DFA

end Cslib
