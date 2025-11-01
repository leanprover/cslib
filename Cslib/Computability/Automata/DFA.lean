/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Computability.Automata.Deterministic.DA
import Cslib.Computability.Automata.Deterministic.ExactAcceptor
import Cslib.Computability.Automata.Acceptor
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

namespace Cslib.Automata

/-- A Deterministic Finite Automaton (DFA) consists of a `DA` with finite sets of states and symbols
equipped with a finite set of accepting states `accept`. -/
structure DFA (State : Type _) (Symbol : Type _) where
  /-- The underlying `DA`. -/
  da : DA State Symbol
  /-- The set of accepting states of the automaton. -/
  accept : Set State
  /-- The automaton is finite-state. -/
  finite_state : Finite State
  /-- The type of symbols (also called 'alphabet') is finite. -/
  finite_symbol : Finite Symbol

/-- Returns the `Acceptor` based on a `DFA`. -/
def DFA.acceptor {State : Type _} {Symbol : Type _} (dfa : DFA State Symbol) : Acceptor Symbol :=
  dfa.da.exactAcceptor dfa.accept

end Cslib.Automata
