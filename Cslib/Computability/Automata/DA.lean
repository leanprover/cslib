/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Computability.Automata.NA



/-! # Deterministic Automaton

A Deterministic Automaton (DA) is an automaton defined by a transition function.
-/

namespace Cslib

structure DA (State : Type _) (Symbol : Type _) where
  /-- The initial state of the automaton. -/
  start : State
  /-- The transition function of the automaton. -/
  tr : State → Symbol → State

end Cslib
