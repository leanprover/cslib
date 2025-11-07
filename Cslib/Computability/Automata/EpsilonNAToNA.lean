/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Computability.Automata.EpsilonNA

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
  lts.saturate.MTr s (μs.map (some ·)) = lts.saturate.noε.MTr s μs := by
  ext s'
  induction μs generalizing s <;> grind [<= LTS.MTr.stepL]

namespace Automata.εNA.Finite

variable {State Symbol : Type*}

/-- Any `εNA.Finite` can be converted into an `NA.Finite` that does not use ε-transitions. -/
@[scoped grind]
def toNAFinite (a : εNA.Finite State Symbol) : NA.Finite State Symbol where
  start := a.εClosure a.start
  accept := a.accept
  Tr := a.saturate.noε.Tr

/-- Correctness of `toNAFinite`. -/
@[scoped grind =]
theorem toNAFinite_language_eq {ena : εNA.Finite State Symbol} :
    Acceptor.language ena.toNAFinite = Acceptor.language ena := by
  ext xs
  have : ∀ s s', ena.saturate.MTr s (xs.map (some ·)) s' = ena.saturate.noε.MTr s xs s' := by
    simp [LTS.noε_saturate_mTr]
  open NA.Finite Acceptor in grind

end Automata.εNA.Finite

end Cslib
