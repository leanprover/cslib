/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Computability.Automata.EpsilonNA.Basic
public import Cslib.Foundations.Semantics.LTS.MapLabel

/-! # Translation of εNA into NA -/

@[expose] public section

namespace Cslib.Automata.εNA.FinAcc

variable {State Symbol : Type*}

/-- Any `εNA.FinAcc` can be converted into an `NA.FinAcc` that does not use ε-transitions. -/
@[scoped grind]
def toNAFinAcc (a : εNA.FinAcc State Symbol) : NA.FinAcc State Symbol where
  start := a.εClosure a.start
  accept := a.accept
  toLTS := a.saturate.mapLabel Option.some

open Acceptor in
open scoped NA.FinAcc LTS LTS.MTr LTS.STr LTS.SMTr in
/-- Correctness of `toNAFinAcc`. -/
@[scoped grind =]
theorem toNAFinAcc_language_eq {a : εNA.FinAcc State Symbol} :
    language a.toNAFinAcc = language a := by
  ext xs
  constructor <;> intro ⟨s, hs, s', hs', h⟩
  · have ⟨sStart, h_sStart, hs⟩ : ∃ i ∈ a.start, s ∈ a.saturate.image i HasTau.τ := by
      simpa [toNAFinAcc, LTS.τClosure, LTS.setImage] using hs
    use sStart, h_sStart, s', hs'
    have h_start := (LTS.sTr_τSTr_iff a.toLTS).mp hs
    exact LTS.SMTr.comp (LTS.sMTr_τSTr_iff.mp h_start) (by grind)
  · cases xs with
    | nil => cases h with | τ tau => exact ⟨s', LTS.tr_setImage hs tau, by grind⟩
    | cons x xs => exact ⟨s, by grind [Set.mem_of_mem_of_subset]⟩

end Cslib.Automata.εNA.FinAcc
