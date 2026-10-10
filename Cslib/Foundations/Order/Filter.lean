/-
Copyright (c) 2026 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Cslib.Init
public import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Fintype.Order

/-! # Basic lemmas on filters-/

@[expose] public section

namespace Filter

lemma eventuallyEq_atTop {α β : Type*} [Preorder α] [IsDirectedOrder α] [Nonempty α] {f g : α → β} :
    f =ᶠ[atTop] g ↔ ∃ a, ∀ b ≥ a, f b = g b :=
  eventually_atTop

lemma eventuallyLE_atTop {α β : Type*} [Preorder α] [IsDirectedOrder α] [Nonempty α] [LE β]
    {f g : α → β} : f ≤ᶠ[atTop] g ↔ ∃ a, ∀ b ≥ a, f b ≤ g b :=
  eventually_atTop

lemma EventuallyLE.exists_mul_const {α β : Type*} [LinearOrder α] [Nonempty α]
    [LocallyFiniteOrderBot α] [PartialOrder β] [IsDirectedOrder β] [Semiring β] [IsOrderedRing β]
    {f g : α → β} (h : f ≤ᶠ[atTop] g) (hg : ∀ a, 1 ≤ g a) :
    ∃ c, ∀ a, f a ≤ c * g a := by
  obtain ⟨a, ha⟩ := eventuallyLE_atTop.mp h
  obtain ⟨c, hc⟩ := (Set.finite_Iio a).image f |>.exists_le
  obtain ⟨c', hc', hc1⟩ := exists_ge_ge c 1
  use c'
  intro b
  obtain (hb | hb) := lt_or_ge b a
  · have : 0 ≤ c' := zero_le_one.trans hc1
    nth_grw 1 [hc (f b) ⟨b, hb, by rfl⟩, ← hg b, hc', mul_one]
  · have : 0 ≤ g b := zero_le_one.trans (hg b)
    grw [← hc1, ha b hb, one_mul]

end Filter
