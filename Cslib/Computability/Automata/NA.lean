/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Foundations.Semantics.LTS.Basic

/-! # Nondeterministic Automaton

A Nondeterministic Automaton (NA) is an automaton with a set of initial states.
-/
structure NA (State : Type _) (Symbol : Type _) extends LTS State Symbol where
  /-- The set of initial states of the automaton. -/
  start : Set State
  /-- The set of accepting states of the automaton. -/
  accept : Set State

namespace NA

/-- An NA accepts a string if there is a multi-step accepting derivative with that trace from
the start state. -/
@[grind]
def Accepts (na : NA State Symbol) (xs : List Symbol) :=
  ∃ s ∈ na.start, ∃ s' ∈ na.accept, na.MTr s xs s'

/-- The language of a DA is the set of strings that it accepts. -/
@[grind]
def language (na : NA State Symbol) : Set (List Symbol) :=
  { xs | na.Accepts xs }

/-- A string is accepted by an NA iff it is in the language of the NA. -/
@[grind]
theorem accepts_mem_language (na : NA State Symbol) (xs : List Symbol) :
  na.Accepts xs ↔ xs ∈ na.language := by rfl

end NA
