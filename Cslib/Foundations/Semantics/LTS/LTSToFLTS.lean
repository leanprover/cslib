/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Foundations.Semantics.LTS.FLTS
import Cslib.Foundations.Semantics.LTS.Basic

variable {State : Type _} {Label : Type _}

namespace Cslib.LTS

/-- Converts an `LTS` into an `FLTS` using the subset construction. -/
@[scoped grind =]
def toFLTS (lts : LTS State Label) : FLTS (Set State) Label where
  tr := lts.setImage

/-- Characterisation of transitions in `LTS.toFLTS` wrt transitions in the original `LTS`. -/
@[scoped grind =]
theorem toFLTS_mem_tr {lts : LTS State Label} {S : Set State} {s' : State} {μ : Label} :
  s' ∈ lts.toFLTS.tr S μ ↔ ∃ s ∈ S, lts.Tr s μ s' := by
  simp only [LTS.toFLTS, LTS.setImage, Set.mem_iUnion, exists_prop]
  grind

/-- Characterisation of multistep transitions in `LTS.toFLTS` wrt multistep transitions in the
original `LTS`. -/
@[scoped grind =]
theorem toFLTS_mem_mtr {lts : LTS State Label} {S : Set State} {s' : State} {μs : List Label} :
  s' ∈ lts.toFLTS.mtr S μs ↔ ∃ s ∈ S, lts.MTr s μs s' := by
  simp only [LTS.toFLTS, FLTS.mtr]
  /- TODO: Grind does not catch a useful rewrite in the subset construction for automata

    A very similar issue seems to occur in the proof of `LTS.toFLTS_language_eq`.

    labels: grind, lts, automata
  -/
  rw [← LTS.setImageMultistep_foldl_setImage]
  grind

/-- Characterisation of multistep transitions in `LTS.toFLTS` as image transitions in `LTS`. -/
@[scoped grind =]
theorem toFLTS_mtr_setImageMultistep {lts : LTS State Label} :
  lts.toFLTS.mtr = lts.setImageMultistep := by grind

end Cslib.LTS
