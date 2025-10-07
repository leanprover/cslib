/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import Cslib.Computability.Automata.NA
import Mathlib.Order.Filter.AtTopBot.Defs

open Filter

/-- Nondeterministic Büchi automaton is a nondeterministic automaton over
finite sets of states and symbols together with a finite set of accepting states. -/
structure BuchiNA (State : Type _) (Symbol : Type _) extends NA State Symbol where
  /-- The set of accepting states of the automaton. -/
  accept : Set State
  /-- The automaton is finite-state. -/
  finite_state : Finite State
  /-- The type of symbols (also called 'alphabet') is finite. -/
  finite_symbol : Finite Symbol

namespace BuchiNA

variable {State : Type _} {Symbol : Type _}

/-- A nondeterministic Büchi automaton accepts an ω-word `xs` iff it has an infinite run
on `xs` which passes through accepting states infinitely often.
-/
@[scoped grind]
def Accepts (nba : BuchiNA State Symbol) (xs : ωList Symbol) :=
  ∃ ss, nba.InfRun xs ss ∧ ∃ᶠ k in atTop, ss k ∈ nba.accept

/-- The language of a nondeterministic Büchi automaton is the set of ω-words that it accepts. -/
@[scoped grind]
def language (nba : BuchiNA State Symbol) : Set (ωList Symbol) :=
  { xs | nba.Accepts xs }

/-- A string is accepted by a a nondeterministic Büchi automaton iff it is in its language. -/
@[scoped grind]
theorem accepts_mem_language (nba : BuchiNA State Symbol) (xs : ωList Symbol) :
  nba.Accepts xs ↔ xs ∈ nba.language := by rfl

end BuchiNA
