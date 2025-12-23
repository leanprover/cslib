/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Computability.Automata.DA.Basic
import Cslib.Computability.Automata.NA.Basic
import Cslib.Foundations.Semantics.FLTS.LTSToFLTS

/-! # Translation of Nondeterministic Automata for finite strings into Deterministic Automata

This file implements the standard subset construction.
-/

namespace Cslib.Automata.NA

variable {State Symbol : Type*}

section SubsetConstruction

/-- Converts an `NA` into a `DA` using the subset construction. -/
@[scoped grind =]
def toDA (a : NA State Symbol) : DA (Set State) Symbol :=
  { a.toFLTS with start := a.start }

namespace FinAcc

/-- Converts an `NA.FinAcc` into a `DA.FinAcc` using the subset construction. -/
@[scoped grind =]
def toDAFinAcc (a : NA.FinAcc State Symbol) : DA.FinAcc (Set State) Symbol :=
  { a.toDA with accept := { S | ∃ s ∈ S, s ∈ a.accept } }

open Acceptor in
open scoped DA.FinAcc LTS in
/-- The `DA` constructed from an `NA` has the same language. -/
@[scoped grind _=_]
theorem toDAFinAcc_language_eq {na : NA.FinAcc State Symbol} :
  language na.toDAFinAcc = language na := by
  ext xs
  grind

end FinAcc

end SubsetConstruction

end Cslib.Automata.NA
