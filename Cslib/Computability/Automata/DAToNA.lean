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

open scoped FLTS NA NA.Run in
@[simp, scoped grind =]
theorem toNA_run {a : DA State Symbol} {xs : ωSequence Symbol} {ss : ωSequence State} :
    a.toNA.Run xs ss ↔ a.run xs = ss := by
  constructor
  · rintro _
    ext n
    induction n <;> grind [NA.Run]
  · grind

namespace FinAcc

/-- `DA.FinAcc` is a special case of `NA.FinAcc`. -/
@[scoped grind =]
def toNAFinAcc (a : DA.FinAcc State Symbol) : NA.FinAcc State Symbol :=
  { a.toNA with accept := a.accept }

open Acceptor in
open scoped FLTS NA.FinAcc in
/-- The `NA.FinAcc` constructed from a `DA.FinAcc` has the same language. -/
@[simp, scoped grind _=_]
theorem toNAFinAcc_language_eq {a : DA.FinAcc State Symbol} :
    language a.toNAFinAcc = language a := by
  ext xs
  constructor
  · grind
  · intro _
    use a.start
    grind

end FinAcc

namespace Buchi

/-- `DA.Buchi` is a special case of `NA.Buchi`. -/
@[scoped grind =]
def toNABuchi (a : DA.Buchi State Symbol) : NA.Buchi State Symbol :=
  { a.toNA with accept := a.accept }

open ωAcceptor in
open scoped NA.Buchi in
/-- The `NA.Buchi` constructed from a `DA.Buchi` has the same ω-language. -/
@[simp, scoped grind _=_]
theorem toNABuchi_language_eq {a : DA.Buchi State Symbol} :
    language a.toNABuchi = language a := by
  ext xs; constructor
  · grind
  · intro _
    use (a.run xs)
    grind

end Buchi

end NA

end Cslib.Automata.DA
