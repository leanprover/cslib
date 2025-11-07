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
def toNA (a : DA State Symbol) : NA State Symbol :=
  { a.toLTS with start := {a.start} }

instance : Coe (DA State Symbol) (NA State Symbol) where
  coe := toNA

namespace Finite

/-- `DA.Finite` is a special case of `NA.Finite`. -/
@[scoped grind =]
def toNAFinite (a : DA.Finite State Symbol) : NA.Finite State Symbol :=
  { a.toNA with accept := a.accept }

open scoped Acceptor FLTS NA.Finite in
/-- The `NA` constructed from a `DA` has the same language. -/
@[scoped grind =]
theorem toNAFinite_language_eq {a : DA.Finite State Symbol} :
    Acceptor.language a = Acceptor.language a.toNAFinite := by
  ext xs
  constructor
  · intro _
    use a.start
    grind
  · grind

end Finite

end NA

end Cslib.Automata.DA
