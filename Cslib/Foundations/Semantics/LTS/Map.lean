/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Foundations.Semantics.LTS.Basic


/-!
# Map operation for LTS.
-/

@[expose] public section

namespace Cslib.LTS

section MapLabel

/-- Constructs an LTS by mapping its labels into those of an existing LTS. -/
def mapLabel (lts : LTS State Label₁) (f : Label₂ → Label₁) : LTS State Label₂ where
  Tr s μ s' := lts.Tr s (f μ) s'

@[simp]
theorem mapLabel_tr {lts : LTS State Label₁} :
    (lts.mapLabel f).Tr s μ s' ↔ lts.Tr s (f μ) s' := by rfl

scoped grind_pattern mapLabel_tr => (lts.mapLabel f).Tr s μ s'

@[simp, scoped grind =]
theorem mapLabel_mTr {lts : LTS State Label₁} {f : Label₂ → Label₁} :
    (lts.mapLabel f).MTr s μs s' ↔ lts.MTr s (μs.map f) s' := by
  induction μs generalizing s with
  | nil => grind
  | cons μ μs ih => grind [=_ mapLabel_tr (f := f)]

end MapLabel

end Cslib.LTS
