/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Computability.Automata.Acceptor
import Cslib.Foundations.Semantics.LTS.FLTS

/-! # Deterministic Automaton

A Deterministic Automaton (DA) is an automaton defined by a transition function equipped with an
initial state and a set of accept states.

This is the generalisation of DFAs found in the literature, without finiteness assumptions.

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][Hopcroft2006]
-/

namespace Cslib.Automata

structure DA (State : Type _) (Symbol : Type _) extends FLTS State Symbol where
  /-- The initial state of the automaton. -/
  start : State
  /-- The accept states of the automaton. -/
  accept : Set State

namespace DA

variable {State : Type _} {Symbol : Type _}

/-- A `DA` accepts a string if the multistep transition function of the `DA` maps the start state
and the string to an accept state.

This is the standard string recognition performed by DFAs in the literature. -/
@[scoped grind =]
instance : Acceptor (DA State Symbol) Symbol where
  Accepts (da : DA State Symbol) (xs : List Symbol) := da.mtr da.start xs ∈ da.accept

end DA

end Cslib.Automata
