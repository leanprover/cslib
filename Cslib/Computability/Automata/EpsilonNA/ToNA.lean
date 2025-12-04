/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Computability.Automata.EpsilonNA.Basic

/-! # Translation of εNA into NA -/

namespace Cslib

/-- Converts an `LTS` with Option labels into an `LTS` on the carried label type, by removing all
ε-transitions. -/
@[local grind =]
private def LTS.noε (lts : LTS State (Option Label)) : LTS State Label where
  Tr s μ s' := lts.Tr s (some μ) s'

@[local grind .]
private lemma LTS.noε_saturate_tr
  {lts : LTS State (Option Label)} {h : μ = some μ'} :
  lts.saturate.Tr s μ s' ↔ lts.saturate.noε.Tr s μ' s' := by
  simp only [LTS.noε]
  grind

@[scoped grind =]
lemma LTS.noε_saturate_mTr {lts : LTS State (Option Label)} :
  lts.saturate.MTr s (μs.map some) = lts.saturate.noε.MTr s μs := by
  ext s'
  induction μs generalizing s <;> grind [<= LTS.MTr.stepL]

namespace Automata.εNA.FinAcc

variable {State Symbol : Type*}

/-- Any `εNA.FinAcc` can be converted into an `NA.FinAcc` that does not use ε-transitions. -/
@[scoped grind]
def toNAFinAcc (a : εNA.FinAcc State Symbol) : NA.FinAcc State Symbol where
  start := a.εClosure a.start
  accept := a.accept
  Tr := a.saturate.noε.Tr

open Acceptor in
open scoped NA.FinAcc in
/-- Correctness of `toNAFinAcc`. -/
@[scoped grind _=_]
theorem toNAFinAcc_language_eq {ena : εNA.FinAcc State Symbol} :
    language ena.toNAFinAcc = language ena := by
  ext xs
  have : ∀ s s', ena.saturate.MTr s (xs.map some) s' = ena.saturate.noε.MTr s xs s' := by
    simp [LTS.noε_saturate_mTr]
  grind

end Automata.εNA.FinAcc

end Cslib
