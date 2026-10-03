/-
Copyright (c) 2025 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Foundations.Data.Nat.Segment
public import Cslib.Foundations.Data.OmegaSequence.Defs
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Finite

/-!
# Infinite occurrences
-/

@[expose] public section

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
  simpa using (Set.toFinite s).frequently_exists (l := atTop) (p := fun x k => xs k = x)

open Nat in
/-- If `p` is true infinitely often, then `p` is true in infinitely many segments
of any strictly monotonic function `f`. -/
theorem frequently_in_strictMono {p : ℕ → Prop} {f : ℕ → ℕ}
    (hm : StrictMono f) (hf : ∃ᶠ k in atTop, p k) :
    ∃ᶠ n in atTop, ∃ k, k < f (n + 1) - f n ∧ p (f n + k) := by
  apply frequently_atTop.mpr
  intro m
  obtain ⟨k, _, _⟩ := frequently_atTop.mp hf (f m)
  use segment f k
  have h0 : f 0 ≤ k := by grind [StrictMono.monotone hm (show 0 ≤ m by grind)]
  split_ands
  · by_contra
    have h1 : segment f k + 1 ≤ m := by grind
    grind [(StrictMono.le_iff_le hm).mpr h1, segment_upper_bound' hm h0]
  · use k - f (segment f k)
    grind [segment_lower_bound' hm h0, segment_upper_bound' hm h0]

open Nat in
/-- Every infinite subset of ℕ is the range of a strictly monotonic function from ℕ to ℕ. -/
theorem strictMono_of_infinite {ns : Set ℕ} (h : ns.Infinite) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ range φ = ns :=
  ⟨nth (· ∈ ns), nth_strictMono h, range_nth_of_infinite h⟩

end ωSequence

end Cslib
