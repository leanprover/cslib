/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Foundations.Semantics.LTS.Basic
import Cslib.Foundations.Semantics.LTS.FLTS
import Cslib.Computability.Automata.Acceptor

/-! # Nondeterministic Automaton

A Nondeterministic Automaton (NA) is an automaton with a set of initial states.

This definition extends `LTS` and thus stores the transition system as a relation `Tr` of the form
`State → Symbol → State → Prop`. Note that you can also instantiate `Tr` by passing an argument of
type `State → Symbol → Set State`; it gets automatically expanded to the former shape.
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
state. -/
@[scoped grind =]
def acceptor (na : NA State Symbol) : Acceptor Symbol where
  Accepts (xs : List Symbol) := ∃ s ∈ na.start, ∃ s' ∈ na.accept, na.MTr s xs s'

end NA

end Cslib.Automata
