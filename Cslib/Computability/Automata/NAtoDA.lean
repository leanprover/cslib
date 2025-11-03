/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Ching-Tsun Chou
-/

import Cslib.Computability.Automata.DA
import Cslib.Computability.Automata.NA

/-! # Conversion of NA into DA (subset construction) -/

namespace Cslib

namespace NA

variable {State Symbol : Type*}

section SubsetConstruction

/-- Converts an `NA` into a `DA` using the subset construction. -/
@[scoped grind =]
def toDA (na : NA State Symbol) : DA (Set State) Symbol where
  start := na.start
  tr := na.setImage

/-- Characterisation of transitions in `NA.toDA` wrt transitions in the original NA. -/
@[simp, scoped grind =]
theorem toDA_mem_tr {na : NA State Symbol} {S : Set State} {s' : State} {x : Symbol} :
  s' ∈ na.toDA.tr S x ↔ ∃ s ∈ S, na.Tr s x s' := by
  simp only [NA.toDA, LTS.setImage, Set.mem_iUnion, exists_prop]
  grind

/-- Characterisation of multistep transitions in `NA.toDA` wrt multistep transitions in the
original NA. -/
@[simp, scoped grind =]
theorem toDA_mem_mtr {na : NA State Symbol} {S : Set State} {s' : State} {xs : List Symbol} :
  s' ∈ na.toDA.mtr S xs ↔ ∃ s ∈ S, na.MTr s xs s' := by
  simp only [NA.toDA, DA.mtr]
  /- TODO: Grind does not catch a useful rewrite in the subset construction for automata

    A very similar issue seems to occur in the proof of `NA.toDA_language_eq`.

    labels: grind, lts, automata
  -/
  rw [← LTS.setImageMultistep_foldl_setImage]
  grind

/-- Characterisation of multistep transitions in `NA.toDA` as image transitions in `LTS`. -/
@[scoped grind =]
theorem toDA_mtr_setImageMultistep {na : NA State Symbol} :
  na.toDA.mtr = na.setImageMultistep := by grind

/-- The `DA` constructed from an `NA` has the same language. -/
@[simp]
theorem toDA_language_eq {na : NA State Symbol} {acc : Set State} :
  na.toDA.language { S | ∃ s ∈ S, s ∈ acc } = na.language acc := by
  ext xs
  rw [DA.mem_language]
  grind

end SubsetConstruction
end NA

end Cslib
