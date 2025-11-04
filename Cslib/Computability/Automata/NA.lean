/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Foundations.Semantics.LTS.Basic
import Cslib.Foundations.Semantics.LTS.FLTS
import Cslib.Computability.Automata.Acceptor

/-! # Nondeterministic Automaton

A Nondeterministic Automaton (NA) is a transition relation equipped with sets of initial and accept
states.

This definition extends `LTS` and thus stores the transition system as a relation `Tr` of the form
`State → Symbol → State → Prop`. Note that you can also instantiate `Tr` by passing an argument of
type `State → Symbol → Set State`; it gets automatically expanded to the former shape.

This definition is a generalisation of NFAs found in the literature, without finiteness assumptions.

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][Hopcroft2006]
-/

namespace Cslib.Automata

structure NA (State : Type _) (Symbol : Type _) extends LTS State Symbol where
  /-- The set of initial states of the automaton. -/
  start : Set State
  /-- The set of accept states of the automaton. -/
  accept : Set State

namespace NA

variable {State : Type _} {Symbol : Type _}

/-- An `NA` accepts a string if there is a multistep transition from a start state to an accept
state.

This is the standard string recognition performed by NFAs in the literature. -/
@[scoped grind =]
instance : Acceptor (NA State Symbol) Symbol where
  Accepts (na : NA State Symbol) (xs : List Symbol) :=
    ∃ s ∈ na.start, ∃ s' ∈ na.accept, na.MTr s xs s'

end NA

end Cslib.Automata
