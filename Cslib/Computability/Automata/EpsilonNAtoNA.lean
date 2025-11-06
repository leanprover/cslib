/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Ching-Tsun Chou
-/

import Cslib.Computability.Automata.EpsilonNA

/-! # Translation of εNA into NA -/

namespace Cslib

open Cslib

open scoped NA εNA

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

variable {State Symbol : Type*}

/-- Any εNA can be converted into an NA that does not use ε-transitions. -/
@[scoped grind]
def toClosedNA (ena : εNA State Symbol) : NA State Symbol where
  start := ena.εClosure ena.start
  Tr := ena.saturate.noε.Tr

@[scoped grind =]
lemma LTS.noε_saturate_mTr {s : State} {Label : Type*} {μs : List Label}
  {lts : LTS State (Option Label)} :
  lts.saturate.MTr s (μs.map (some ·)) = lts.saturate.noε.MTr s μs := by
  ext s'
  induction μs generalizing s <;> grind [<= LTS.MTr.stepL]

/-- Correctness of `toClosedNA`. -/
@[scoped grind =]
theorem toClosedNA_language_eq {ena : εNA State Symbol} {acc : Set State} :
    (NA.FinAcc.mk ena.toClosedNA acc).language = (εNA.FinAcc.mk ena acc).language := by
  ext xs
  rw [NA.FinAcc.mem_language, εNA.FinAcc.mem_language]
  have : ∀ s s', ena.saturate.MTr s (xs.map (some ·)) s' = ena.saturate.noε.MTr s xs s' := by
    simp [LTS.noε_saturate_mTr]
  grind

end εNA

end Cslib
