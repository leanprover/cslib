/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Computability.Automata.Acceptor
import Cslib.Foundations.Semantics.LTS.FLTS

/-! # Deterministic Automaton

A Deterministic Automaton (DA) is an automaton defined by a transition function.
-/

namespace Cslib.Automata

structure DA (State : Type _) (Symbol : Type _) extends FLTS State Symbol where
  /-- The initial state of the automaton. -/
  start : State
  /-- The accept states of the automaton. -/
  accept : Set State

namespace DA

variable {State : Type _} {Symbol : Type _}

/-- Returns the acceptor that matches exactly the sequence of symbols in a string.
That is, a string is accepted if the multistep transition function of the `DA` maps the start state
and the string to an accept state.

This is the standard string recognition performed by DFAs in the literature. -/
@[scoped grind =]
def acceptor (da : DA State Symbol) : Acceptor Symbol where
  Accepts (xs : List Symbol) := da.mtr da.start xs ∈ da.accept

end DA

end Cslib.Automata
