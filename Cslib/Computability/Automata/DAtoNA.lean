/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Ching-Tsun Chou
-/

import Cslib.Computability.Automata.DA
import Cslib.Computability.Automata.NA

/-! # Conversion of DA into NA -/

namespace Cslib

open scoped DA NA

namespace DA

variable {State : Type*} {Symbol : Type*}

section NA

/-- `DA` can be viewed as a special case of `NA`. -/
@[scoped grind =]
def toNA (da : DA State Symbol) : NA State Symbol where
  start := {da.start}
  Tr := fun s1 μ s2 => da.tr s1 μ = s2

@[simp, scoped grind =]
lemma toNA_start {da : DA State Symbol} : da.toNA.start = {da.start} := rfl

instance : Coe (DA State Symbol) (NA State Symbol) where
  coe := toNA

/-- `DA.toNA` correctly characterises transitions. -/
@[simp, scoped grind =]
theorem toNA_tr {da : DA State Symbol} {s1 s2 : State} {μ : Symbol} :
  da.toNA.Tr s1 μ s2 ↔ da.tr s1 μ = s2 := by
  rfl

/-- The transition system of a DA is deterministic. -/
@[simp, scoped grind ⇒]
theorem toNA_deterministic (da : DA State Symbol) : da.toNA.Deterministic := by
  grind

/-- The transition system of a DA is image-finite. -/
@[simp, scoped grind ⇒]
theorem toNA_imageFinite (da : DA State Symbol) : da.toNA.ImageFinite :=
  da.toNA.deterministic_imageFinite da.toNA_deterministic

/-- Characterisation of multistep transitions. -/
@[simp, scoped grind =]
theorem toNA_mtr {da : DA State Symbol} {s1 s2 : State} {xs : List Symbol} :
  da.toNA.MTr s1 xs s2 ↔ da.mtr s1 xs = s2 := by
  have : ∀ x, da.toNA.Tr s1 x (da.tr s1 x) := by grind
  constructor <;> intro h
  case mp => induction h <;> grind
  case mpr => induction xs generalizing s1 <;> grind

/-- The `NA` constructed from a `DA` has the same language. -/
@[simp, scoped grind =]
theorem toNA_language_eq {da : DA State Symbol} {acc : Set State} :
  da.toNA.language acc = da.language acc := by
  ext xs
  constructor
  · grind
  · rintro ⟨s, h1, h2⟩
    have := toNA_mtr.mpr h2
    refine ⟨s, ?_, da.start, ?_⟩ <;> grind

end NA

end DA

end Cslib
