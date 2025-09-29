/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

/-! # Deterministic Automaton

A Deterministic Automaton (DA) is a deterministic labelled transition system with an initial state.
For convenience, it is expressed by giving a transition function.
-/
structure DA (State : Type _) (Symbol : Type _) where
  /-- The initial state of the automaton. -/
  start : State
  /-- The transition function of the automaton. -/
  tr : State → Symbol → State
