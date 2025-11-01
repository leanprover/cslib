/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Ching-Tsun Chou
-/

import Cslib.Computability.Automata.EpsilonNA
import Cslib.Computability.Automata.NA

/-! # Translation of εNA into NA -/

namespace Cslib

open Cslib
/-- Converts an `LTS` with Option labels into an `LTS` on the carried label type, by removing all
ε-transitions. -/
@[grind]
private def LTS.noε (lts : LTS State (Option Label)) : LTS State Label where
  Tr := fun s μ s' => lts.Tr s (some μ) s'

@[local grind .]
private lemma LTS.noε_saturate_tr
  {lts : LTS State (Option Label)} {h : μ = some μ'} :
  lts.saturate.Tr s μ s' ↔ lts.saturate.noε.Tr s μ' s' := by
  simp only [LTS.noε]
  grind

namespace εNA

variable {State : Type*} {Symbol : Type*}

section NA

/-- Any εNA can be converted into an NA that does not use ε-transitions. -/
@[scoped grind]
def toNA (ena : εNA State Symbol) : NA State Symbol where
  start := ena.εClosure ena.start
  Tr := ena.saturate.noε.Tr

@[scoped grind =]
lemma LTS.noε_saturate_mTr {s : State} {Label : Type*} {μs : List Label}
  {lts : LTS State (Option Label)} :
  lts.saturate.MTr s (μs.map (some ·)) = lts.saturate.noε.MTr s μs := by
  ext s'
  induction μs generalizing s <;> grind [<= LTS.MTr.stepL]

/-- Correctness of `toNA`. -/
@[scoped grind =]
theorem toNA_language_eq {ena : εNA State Symbol} {acc : Set State} :
  ena.toNA.language acc = ena.language acc := by
  ext xs
  have : ∀ s s', ena.saturate.MTr s (xs.map (some ·)) s' = ena.saturate.noε.MTr s xs s' := by
    simp [LTS.noε_saturate_mTr]
  open NA in grind

end NA
end εNA

end Cslib
