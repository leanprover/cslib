/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Computability.Automata.NA

/-- A Nondeterministic Finite-State Automaton (NFA) is a nondeterministic automaton (NA)
over finite sets of states and symbols. -/
structure NFA (State : Type _) (Symbol : Type _) extends NA State Symbol where
  /-- The automaton is finite-state. -/
  finite_state : Finite State
  /-- The type of symbols (also called 'alphabet') is finite. -/
  finite_symbol : Finite Symbol
