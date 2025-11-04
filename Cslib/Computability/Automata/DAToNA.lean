/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Computability.Automata.DA
import Cslib.Computability.Automata.NA
import Cslib.Foundations.Semantics.LTS.FLTSToLTS

/-! # Translation of Deterministic Automata into Nonodeterministic Automata.

This is the general version of the standard translation of DFAs into NFAs. -/

namespace Cslib.Automata.DA

variable {State : Type _} {Symbol : Type _}

section NA

/-- `DA` is a special case of `NA`. -/
@[scoped grind =]
def toNA (da : DA State Symbol) : NA State Symbol where
  start := {da.start}
  accept := da.accept
  Tr := da.toLTS.Tr

instance : Coe (DA State Symbol) (NA State Symbol) where
  coe := toNA

/-- The `NA` constructed from a `DA` has the same language. -/
@[scoped grind =]
theorem toNA_language_eq {da : DA State Symbol} :
    Acceptor.language da = Acceptor.language da.toNA := by
  ext xs
  refine ⟨?_, ?_⟩
  · refine fun h => ⟨da.start, ?_⟩
    open NA Acceptor FLTS in grind
  · open NA Acceptor FLTS in grind

end NA

end Cslib.Automata.DA
