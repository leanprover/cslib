/-
Copyright (c) 2026 Henning Dieterichs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henning Dieterichs
-/

module

public import Cslib.Computability.CellularAutomata.Basic

@[expose] public section

/-! # Cellular Automata: State Predicates

This file defines predicates on the states of a cellular automaton.

## Main definitions

* `CellAutomaton.Quiescent` — a state that stays the same when surrounded by itself.
* `CellAutomaton.Dead` — a state that never changes regardless of neighbors.
-/

namespace Cslib.CellularAutomata

namespace CellAutomaton

variable {α β Q : Type*} (C : CellAutomaton α β Q)

/-- A state is quiescent if it stays the same when surrounded by itself. -/
def Quiescent (q : Q) : Prop := C.δ q q q = q

/-- A state is dead if it never changes regardless of neighbors. -/
def Dead (q : Q) : Prop := ∀ a c, C.δ a q c = q

theorem Dead.quiescent {q : Q} (h : C.Dead q) : C.Quiescent q := h q q

end CellAutomaton

end Cslib.CellularAutomata
