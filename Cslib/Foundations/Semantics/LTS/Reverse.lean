/-
Copyright (c) 2026 Vignesh Karri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vignesh Karri
-/

module

public import Cslib.Foundations.Semantics.LTS.Basic

/-!
# Reverse operation for LTS.
-/

@[expose] public section

namespace Cslib.LTS

section Reverse

/-- Constructs an LTS by reversing the transitions of an existing LTS. -/
def reverse (lts : LTS State Label) : LTS State Label where
  Tr s μ s' := lts.Tr s' μ s

@[simp]
theorem reverse_tr {lts : LTS State Label} :
    (lts.reverse).Tr s μ s' ↔ lts.Tr s' μ s := by rfl

/-- Reversing an LTS twice gives back the original LTS. -/
@[simp]
theorem reverse_reverse (lts : LTS State Label) : lts.reverse.reverse = lts := rfl

/-- The multistep transitions of `lts.reverse` are exactly the reversed multistep transitions of
`lts` -/
@[simp]
theorem reverse_mTr {lts : LTS State Label} :
    lts.reverse.MTr s' μs s ↔ lts.MTr s μs.reverse s' := by
  induction μs generalizing s s' with
  | nil =>
    simp_all [eq_comm]
  | cons x xs ih =>
    simp only [List.reverse_cons, LTS.MTr.cons_iff]
    constructor
    · rintro ⟨mid, h1, h2⟩
      exact LTS.MTr.stepR lts (ih.mp h2) h1
    · intro hmtr
      obtain ⟨mid, h1, h2⟩ := LTS.MTr.split hmtr
      simp only [LTS.MTr.singleton_iff] at h2
      exact ⟨mid, h2, ih.mpr h1⟩

end Reverse

end Cslib.LTS
