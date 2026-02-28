/-
Copyright (c) 2025 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Foundations.Data.OmegaSequence.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Order.Filter.Cofinite

@[expose] public section

/-!
# Infinite occurrences
-/

namespace Cslib

open Function Set Filter

namespace ωSequence

universe u v w
variable {α : Type u} {β : Type v} {δ : Type w}

/-- The set of elements that appear infinitely often in an ω-sequence. -/
def infOcc (xs : ωSequence α) : Set α :=
  { x | ∃ᶠ k in atTop, xs k = x }

/-- An alternative characterization of "infinitely often". -/
theorem frequently_iff_strictMono {p : ℕ → Prop} :
    (∃ᶠ n in atTop, p n) ↔ ∃ f : ℕ → ℕ, StrictMono f ∧ ∀ m, p (f m) := by
  constructor
  · intro h
    exact extraction_of_frequently_atTop h
  · rintro ⟨f, h_mono, h_p⟩
    rw [Nat.frequently_atTop_iff_infinite]
    have h_range : range f ⊆ {n | p n} := by grind
    grind [Infinite.mono, infinite_range_of_injective, StrictMono.injective]

/-- In a finite type, the elements of a set occurs infinitely often iff
some element in the set occurs infinitely often. -/
theorem frequently_in_finite_type [Finite α] {s : Set α} {xs : ωSequence α} :
    (∃ᶠ k in atTop, xs k ∈ s) ↔ ∃ x ∈ s, ∃ᶠ k in atTop, xs k = x := by
  constructor
  · intro h_inf
    rw [Nat.frequently_atTop_iff_infinite] at h_inf
    have : Infinite (xs ⁻¹' s) := h_inf.to_subtype
    let rf := Set.restrictPreimage s xs
    obtain ⟨⟨x, h_x⟩, h_inf'⟩ := Finite.exists_infinite_fiber rf
    rw [← Set.infinite_range_iff (Subtype.val_injective.comp Subtype.val_injective)] at h_inf'
    simp only [range, comp_apply, Subtype.exists, mem_preimage, mem_singleton_iff,
      restrictPreimage_mk, Subtype.mk.injEq, ← Nat.frequently_atTop_iff_infinite, rf] at h_inf'
    grind
  · rintro ⟨_, _, h_inf⟩
    apply Frequently.mono h_inf
    grind

end ωSequence

end Cslib
