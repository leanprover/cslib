/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import Cslib.Computability.Automata.DA.Basic
import Cslib.Foundations.Semantics.FLTS.Prod

/-! # Product of deterministic automata. -/

namespace Cslib.Automata

open List
open scoped FLTS

variable {State1 State2 Symbol : Type*}

namespace DA

/-- The product of two deterministic automata. -/
@[scoped grind =]
def prod (da1 : DA State1 Symbol) (da2 : DA State2 Symbol) : DA (State1 × State2) Symbol where
  toFLTS := da1.toFLTS.prod da2.toFLTS
  start := (da1.start, da2.start)

/-- A state is reachable by the product automaton iff its components are reachable by
the respective automaton components. -/
@[simp, scoped grind =]
theorem prod_mtr_eq (da1 : DA State1 Symbol) (da2 : DA State2 Symbol)
    (s : State1 × State2) (xs : List Symbol) :
    (da1.prod da2).mtr s xs = (da1.mtr s.fst xs, da2.mtr s.snd xs) :=
  FLTS.prod_mtr_eq da1.toFLTS da2.toFLTS s xs

end DA

end Cslib.Automata
