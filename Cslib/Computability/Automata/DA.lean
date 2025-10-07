/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Computability.Automata.NA
import Cslib.Foundations.Data.OmegaList.Init

/-! # Deterministic Automaton

A Deterministic Automaton (DA) is an automaton defined by a transition function.
-/
structure DA (State : Type _) (Symbol : Type _) where
  /-- The initial state of the automaton. -/
  start : State
  /-- The transition function of the automaton. -/
  tr : State → Symbol → State

variable {State : Type _} {Symbol : Type _}

/-- The (unique) infinite run of a DA on an infinite input `xs`.
-/
def DA.infRun (da : DA State Symbol) (xs : ωList Symbol) : ωList State
  | 0 => da.start
  | k + 1 => da.tr (da.infRun xs k) (xs k)
