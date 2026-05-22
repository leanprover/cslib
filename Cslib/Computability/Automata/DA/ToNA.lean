/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Computability.Automata.DA.Basic
public import Cslib.Computability.Automata.NA.Basic
public import Cslib.Foundations.Semantics.FLTS.FLTSToLTS

/-! # Translation of Deterministic Automata into Nonodeterministic Automata.

This is the general version of the standard translation of DFAs into NFAs. -/

@[expose] public section

namespace Cslib.Automata.DA

variable {State Symbol : Type*}

section NA

/-- `DA` is a special case of `NA`. -/
@[scoped grind =]
def toNA (a : DA State Symbol) : NA State Symbol :=
  { a.toLTS with start := {a.start} }

instance : Coe (DA State Symbol) (NA State Symbol) where
  coe := toNA

open scoped FLTS NA NA.Run LTS in
@[simp, scoped grind =]
theorem toNA_run {a : DA State Symbol} {xs : ωSequence Symbol} {ss : ωSequence State} :
    a.toNA.Run xs ss ↔ a.run xs = ss := by
  constructor
  · rintro _
    ext n
    induction n <;> grind [NA.Run]
  · grind [NA.Run]

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
  #adaptation_note
  /-- A grind regression found moving to nightly-2026-03-31 (changes from lean#13166) -/
  constructor
  · simp_all [mem_language a xs, Accepts, toNAFinAcc, toNA, FLTS.toLTS_mtr]
  · intro _
    use a.start
    simp_all [Accepts, toNAFinAcc, toNA, FLTS.toLTS_mtr]

end FinAcc

namespace Buchi

/-- `DA.Buchi` is a special case of `NA.Buchi`. -/
@[scoped grind =]
def toNABuchi (a : DA.Buchi State Symbol) : NA.Buchi State Symbol :=
  { a.toNA with accept := a.accept }

open ωAcceptor in
/-- The `NA.Buchi` constructed from a `DA.Buchi` has the same ω-language. -/
@[simp, scoped grind _=_]
theorem toNABuchi_language_eq {a : DA.Buchi State Symbol} :
    language a.toNABuchi = language a := by
  ext xs; constructor
  #adaptation_note
  /-- A grind regression found moving to nightly-2026-03-31 (changes from lean#13166) -/
  · simp_all [Accepts, language, toNABuchi]
  · intro h
    use (a.run xs)
    split_ands
    · grind
    · exact Filter.frequently_map.mp h

end Buchi

end NA

end Cslib.Automata.DA
