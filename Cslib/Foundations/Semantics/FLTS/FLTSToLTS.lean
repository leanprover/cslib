/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Foundations.Semantics.LTS.Basic

@[expose] public section

variable {State Label : Type*}

namespace Cslib.FLTS

/-- `FLTS` is a special case of `LTS`. -/
@[scoped grind =]
def toLTS (flts : FLTS State Label) : LTS State Label where
  Tr s1 μ s2 := flts.tr s1 μ = s2

instance : Coe (FLTS State Label) (LTS State Label) where
  coe := toLTS

/-- `FLTS.toLTS` correctly characterises transitions. -/
@[scoped grind =]
theorem toLTS_tr {flts : FLTS State Label} {s1 : State} {μ : Label} {s2 : State} :
  flts.toLTS.Tr s1 μ s2 ↔ flts.tr s1 μ = s2 := by rfl

/-- The transition system of a FLTS is deterministic. -/
@[scoped grind ⇒]
instance toLTS_deterministic (flts : FLTS State Label) : flts.toLTS.Deterministic := by
  open LTS in grind

/-- The transition system of a FLTS is image-finite. -/
@[scoped grind ⇒]
instance toLTS_imageFinite (flts : FLTS State Label) : flts.toLTS.ImageFinite :=
  flts.toLTS.deterministic_imageFinite

open LTS LTS.MTr in
/-- Characterisation of multistep transitions. -/
@[scoped grind =]
theorem toLTS_mtr {flts : FLTS State Label} {s1 : State} {μs : List Label} {s2 : State} :
    flts.toLTS.MTr s1 μs s2 ↔ flts.mtr s1 μs = s2 := by
  have : ∀ μ, flts.toLTS.Tr s1 μ (flts.tr s1 μ) := by grind
  constructor <;> intro h
  case mp => induction h <;> grind
  case mpr => induction μs generalizing s1 <;> grind

end Cslib.FLTS
