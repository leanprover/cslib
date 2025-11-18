/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Ching-Tsun Chou
-/

import Cslib.Foundations.Data.OmegaSequence.InfOcc
import Cslib.Foundations.Semantics.LTS.Basic
import Cslib.Computability.Automata.Acceptor
import Cslib.Computability.Automata.OmegaAcceptor

/-! # Nondeterministic Automaton

A Nondeterministic Automaton (NA) is a transition relation equipped with a set of initial states.

Automata with different accepting conditions are then defined as extensions of `NA`.
These include, for example, a generalised version of NFA as found in the literature (without
finiteness assumptions), nondeterministic Buchi automata, and nondeterministic Muller automata.

This definition extends `LTS` and thus stores the transition system as a relation `Tr` of the form
`State → Symbol → State → Prop`. Note that you can also instantiate `Tr` by passing an argument of
type `State → Symbol → Set State`; it gets automatically expanded to the former shape.

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][Hopcroft2006]
-/

open Filter

namespace Cslib.Automata

structure NA (State Symbol : Type*) extends LTS State Symbol where
  /-- The set of initial states of the automaton. -/
  start : Set State

namespace NA

variable {State : Type _} {Symbol : Type _}

/-- Infinite run. -/
@[scoped grind =]
def Run (na : NA State Symbol) (xs : ωSequence Symbol) (ss : ωSequence State) :=
  ss 0 ∈ na.start ∧ ∀ n, na.Tr (ss n) (xs n) (ss (n + 1))

/-- A nondeterministic automaton that accepts finite strings (lists of symbols). -/
structure FinAcc (State Symbol : Type*) extends NA State Symbol where
  /-- The accept states. -/
  accept : Set State

namespace FinAcc

/-- An `NA.FinAcc` accepts a string if there is a multistep transition from a start state to an
accept state.

This is the standard string recognition performed by NFAs in the literature. -/
@[simp, scoped grind =]
instance : Acceptor (FinAcc State Symbol) Symbol where
  Accepts (a : FinAcc State Symbol) (xs : List Symbol) :=
    ∃ s ∈ a.start, ∃ s' ∈ a.accept, a.MTr s xs s'

end FinAcc

/-- Nondeterministic Buchi automaton. -/
structure Buchi (State Symbol : Type*) extends NA State Symbol where
  accept : Set State

namespace Buchi

@[simp, scoped grind =]
instance : ωAcceptor (Buchi State Symbol) Symbol where
  Accepts (a : Buchi State Symbol) (xs : ωSequence Symbol) :=
    ∃ ss, a.Run xs ss ∧ ∃ᶠ k in atTop, ss k ∈ a.accept

end Buchi

/-- Nondeterministic Muller automaton. -/
structure Muller (State Symbol : Type*) extends NA State Symbol where
  accept : Set (Set State)

namespace Muller

@[simp, scoped grind =]
instance : ωAcceptor (Muller State Symbol) Symbol where
  Accepts (a : Muller State Symbol) (xs : ωSequence Symbol) :=
    ∃ ss, a.Run xs ss ∧ ss.infOcc ∈ a.accept

end Muller

end NA

end Cslib.Automata
