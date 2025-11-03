/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Computability.Automata.Deterministic.DA
import Cslib.Computability.Automata.Nondeterministic.NA
import Cslib.Foundations.Semantics.LTS.LTSToFLTS

/-! # Translation of NFA into DFA (subset construction) -/

namespace Cslib.Automata.NA

variable {State : Type _} {Symbol : Type _}

section SubsetConstruction

/-- Converts an `NA` into a `DA` using the subset construction. -/
@[scoped grind =]
def toDA (na : NA State Symbol) : DA (Set State) Symbol := {
  start := na.start
  accept := { S | ∃ s ∈ S, s ∈ na.accept }
  tr := na.toFLTS.tr
}

/-- The `DA` constructed from an `NA` has the same language. -/
@[scoped grind =]
theorem toDA_language_eq {na : NA State Symbol} :
  na.toDA.acceptor.language = na.acceptor.language := by
  ext xs
  -- simp [toDA, NA.acceptor, DA.acceptor]
  rw [Acceptor.mem_language]
  rw [Acceptor.mem_language]
  -- simp [LTS.toFLTS]
  #adaptation_note
  /--
  Moving from `nightly-2025-09-15` to `nightly-2025-10-19` required
  increasing the number of allowed splits.
  -/
  open DA NA Acceptor FLTS LTS in grind (splits := 12)

end SubsetConstruction

end Cslib.Automata.NA
