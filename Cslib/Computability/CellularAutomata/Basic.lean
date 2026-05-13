/-
Copyright (c) 2026 Henning Dieterichs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henning Dieterichs
-/

module

public import Cslib.Init

@[expose] public section

/-! # Cellular Automata: Basic Definitions

This file defines the core structure of a one-dimensional cellular automaton with radius 1,
along with configurations and traces.

A `CellAutomaton α β Q` has:
- An input alphabet `α`, an output alphabet `β`, and an internal state type `Q`.
- A local transition function `δ` that maps a triple (left neighbor, cell, right neighbor) to a
  new cell state.
- An embedding `embed : α → Q` of input symbols into internal states.
- A projection `project : Q → β` of internal states to output symbols.

## References

* [A. R. Smith III, *Real-Time Language Recognition by One-Dimensional Cellular Automata*][Smith1972]
* [M. Kutrib, *Cellular Automata and Language Theory*][Kutrib2009]
-/

namespace Cslib.CellularAutomata

/-- A one-dimensional cellular automaton with input alphabet `α`, output alphabet `β`,
and internal state type `Q`. The transition function `δ` takes the left neighbor,
the cell itself, and the right neighbor, and produces the new cell state. -/
structure CellAutomaton (α β Q : Type*) where
  /-- The local transition function: given the left neighbor, the cell, and the right neighbor,
  produce the new cell state. -/
  δ : Q → Q → Q → Q
  /-- Embed an input symbol into the internal state space. -/
  embed : α → Q
  /-- Project an internal state to an output symbol. -/
  project : Q → β

/-- A configuration assigns a cell state to each integer position. -/
def Config (α : Type*) := Int → α

/-- A trace assigns a value to each time step. -/
def Trace (α : Type*) := ℕ → α

end Cslib.CellularAutomata
