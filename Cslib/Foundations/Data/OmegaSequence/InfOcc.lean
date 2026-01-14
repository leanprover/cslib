/-
Copyright (c) 2025 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Foundations.Data.OmegaSequence.Defs
public import Mathlib.Order.Filter.AtTopBot.Basic
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

end ωSequence

end Cslib
