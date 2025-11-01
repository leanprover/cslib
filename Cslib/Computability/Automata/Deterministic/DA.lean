/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Init

/-! # Deterministic Automaton

A Deterministic Automaton (DA) is an automaton defined by a transition function.
-/

namespace Cslib.Automata

structure DA (State : Type _) (Symbol : Type _) where
  /-- The initial state of the automaton. -/
  start : State
  /-- The transition function of the automaton. -/
  tr : State → Symbol → State

namespace DA

variable {State : Type _} {Symbol : Type _}

/-- Extended transition function.

Implementation note: compared to [Hopcroft2006], the definition consumes the input list of symbols
from the left (instead of the right), in order to match the way lists are constructed.
-/
@[scoped grind =]
def mtr (da : DA State Symbol) (s : State) (xs : List Symbol) := xs.foldl da.tr s

@[scoped grind =]
theorem mtr_nil_eq {da : DA State Symbol} {s : State} : da.mtr s [] = s := rfl

end DA

end Cslib.Automata
