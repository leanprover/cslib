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
def prod (da1 : DA State1 Symbol) (da2 : DA State2 Symbol) : DA (State1 × State2) Symbol :=
  {
    (da1.toFLTS.prod da2.toFLTS) with
    start := (da1.start, da2.start)
  }

end DA

end Cslib.Automata
