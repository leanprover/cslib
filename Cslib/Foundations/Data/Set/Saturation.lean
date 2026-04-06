/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Init
public import Mathlib.Order.SetNotation
public import Mathlib.Data.Set.Basic

@[expose] public section

/-!
# Saturation
-/

namespace Set

variable {ι α : Type*}

/-- `f : ι → Set α` saturates `s : Set α` iff `f i` is a subset of `s`
whenever `f i` and `s` has any intersection at all. -/
def Saturates (f : ι → Set α) (s : Set α) : Prop :=
  ∀ i : ι, (f i ∩ s).Nonempty → f i ⊆ s

variable {f : ι → Set α} {s : Set α}

/-- If `f` saturates `s`, then `f` saturates its complement `sᶜ` as well. -/
@[simp, scoped grind .]
theorem saturates_compl (hs : Saturates f s) : Saturates f sᶜ := by
  rintro i ⟨_, _⟩ y _ _
  have : (f i ∩ s).Nonempty := ⟨y, by grind⟩
  grind [Saturates]

/-- If `f` is a cover and saturates `s`, then `s` is the union of all `f i` that intersects `s`. -/
theorem saturates_eq_biUnion (hs : Saturates f s) (hc : ⋃ i, f i = univ) :
    s = ⋃ i ∈ {i | (f i ∩ s).Nonempty}, f i := by
  ext x
  simp only [mem_setOf_eq, mem_iUnion, exists_prop]
  constructor
  · intro h_x
    obtain ⟨i, _⟩ := mem_iUnion.mp <| univ_subset_iff.mpr hc <| mem_univ x
    use i, ⟨x, by grind⟩, by grind
  · rintro ⟨i, h_i, _⟩
    grind [hs i h_i]

end Set
