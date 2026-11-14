/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.AtomStructure
public import Mathlib.Data.Set.Card

/-!
# Lyndon algebras

Given a type `α` with a distinguished element `e`, Lyndon's construction makes `α` into an atom
structure in which `e` is the only identity atom, every atom is its own converse, and for
`p, q ≠ e`

* `p ; p = p + e`, and
* `p ; q` is the sum of all atoms other than `p`, `q` and `e` when `p ≠ q`.

This is an atom structure exactly when `α` has one, two, or at least five elements; we follow
[Monk1964] in requiring at least five. The complex algebra of this atom structure is the
*Lyndon algebra* `𝔄(α, e)`. Geometrically, `α \ {e}` is the set of points of a projective line
and `𝔄(α, e)` is the complex algebra of this one-dimensional geometry in the sense of
[Givant2017a], Section 3.6.

The terminology varies in the literature. In [Monk1964] the "Lyndon algebras" are the algebras
satisfying a list of axioms (composition is associative, commutative, additive and has `1'` as an
identity, converse is trivial, and `1' ≤ x ; y` if and only if `x · y ≠ 0`), which characterize the
integral relation algebras with trivial converse, and `𝔄(α, e)` is shown to be one of them. We
follow the modern usage, in which the name refers to the construction.

## Main definitions

* `Cslib.RelationAlgebra.lyndonCycles`: the cycles of Lyndon's atom structure.
* `Cslib.RelationAlgebra.AtomStructure.lyndon`: Lyndon's atom structure.

## Main statements

* `Cslib.RelationAlgebra.ComplexAlgebra.isIntegral_lyndon` and the `TrivialStar` instance:
  Theorem A of [Monk1964], that `𝔄(α, e)` is an integral relation algebra with trivial converse.

## References

* [R. C. Lyndon, *Relation algebras and projective geometries*][Lyndon1961]
* [J. D. Monk, *On representable relation algebras*][Monk1964]
* [Steven Givant, *Introduction to Relation Algebras*][Givant2017a]

-/

@[expose] public section

namespace Cslib.RelationAlgebra

variable {α : Type*} {e r s t : α}

/-- The cycles of Lyndon's atom structure on a type with a distinguished element `e`: the triples
`(r, s, t)` such that one of the three is `e` and the other two agree, or all three agree, or
`r`, `s`, `t` and `e` are pairwise distinct. -/
def lyndonCycles (e : α) : Set (α × α × α) :=
  {(r, s, t) | r = e ∧ s = t ∨ s = e ∧ r = t ∨ t = e ∧ r = s ∨ r = s ∧ s = t ∨
    r ≠ s ∧ s ≠ t ∧ r ≠ t ∧ r ≠ e ∧ s ≠ e ∧ t ≠ e}

theorem mem_lyndonCycles : (r, s, t) ∈ lyndonCycles e ↔
    r = e ∧ s = t ∨ s = e ∧ r = t ∨ t = e ∧ r = s ∨ r = s ∧ s = t ∨
      r ≠ s ∧ s ≠ t ∧ r ≠ t ∧ r ≠ e ∧ s ≠ e ∧ t ≠ e := .rfl

/-- A type with at least five elements has an element distinct from any four given ones. -/
theorem _root_.ENat.exists_ne_of_five_le_card (h : 5 ≤ ENat.card α) (a b c d : α) :
    ∃ x, x ≠ a ∧ x ≠ b ∧ x ≠ c ∧ x ≠ d := by
  by_contra hcon
  have hsub : (Set.univ : Set α) ⊆ {a, b, c, d} := fun x _ => by
    by_contra hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx
    exact hcon ⟨x, hx⟩
  have hle : ENat.card α ≤ 4 := by
    rw [← Set.encard_univ]
    calc (Set.univ : Set α).encard
      _ ≤ ({a, b, c, d} : Set α).encard := Set.encard_le_encard hsub
      _ ≤ ({b, c, d} : Set α).encard + 1 := Set.encard_insert_le _ _
      _ ≤ ({c, d} : Set α).encard + 1 + 1 := by gcongr; exact Set.encard_insert_le _ _
      _ ≤ ({d} : Set α).encard + 1 + 1 + 1 := by gcongr; exact Set.encard_insert_le _ _
      _ = 4 := by rw [Set.encard_singleton]; rfl
  exact absurd (h.trans hle) (by decide)

/-- Lyndon's cycles are associative on a type with at least five elements. -/
theorem lyndonCycles_assoc (h : 5 ≤ ENat.card α) {r q p s t : α}
    (h₁ : (r, q, p) ∈ lyndonCycles e) (h₂ : (s, t, q) ∈ lyndonCycles e) :
    ∃ q', (q', t, p) ∈ lyndonCycles e ∧ (r, s, q') ∈ lyndonCycles e := by
  obtain ⟨x, hx⟩ := ENat.exists_ne_of_five_le_card h e r s t
  obtain ⟨y, hy⟩ := ENat.exists_ne_of_five_le_card h e r p s
  simp only [mem_lyndonCycles] at h₁ h₂ ⊢
  by_contra hcon
  have he := not_exists.mp hcon e
  have hr := not_exists.mp hcon r
  have hs := not_exists.mp hcon s
  have ht := not_exists.mp hcon t
  have hp := not_exists.mp hcon p
  have hq := not_exists.mp hcon q
  have hx' := not_exists.mp hcon x
  have hy' := not_exists.mp hcon y
  grind (splits := 40)

namespace AtomStructure

/-- Lyndon's atom structure on a type with at least five elements and a distinguished element `e`,
denoted `𝔄(α, e)` in [Monk1964]. -/
def lyndon (e : α) (h : 5 ≤ ENat.card α) : AtomStructure α where
  conv a := a
  id := {e}
  cycles := lyndonCycles e
  assoc := lyndonCycles_assoc h
  id_cycle_right {s r p} (hs : s = e) hc := by
    rw [mem_lyndonCycles] at hc
    grind
  exists_id_cycle_right r := ⟨e, rfl, .inr (.inl ⟨rfl, rfl⟩)⟩
  cycle_left {r s t} hc := by
    rw [mem_lyndonCycles] at hc ⊢
    grind

variable (h : 5 ≤ ENat.card α)

@[simp]
theorem lyndon_conv (a : α) : (lyndon e h).conv a = a := rfl

@[simp]
theorem lyndon_id : (lyndon e h).id = {e} := rfl

@[simp]
theorem lyndon_cycles : (lyndon e h).cycles = lyndonCycles e := rfl

end AtomStructure

namespace ComplexAlgebra

open AtomStructure

variable (h : 5 ≤ ENat.card α)

/-- **Theorem A** of [Monk1964], first half: the Lyndon algebra is integral. -/
theorem isIntegral_lyndon : IsIntegral (ComplexAlgebra (lyndon e h)) :=
  (isIntegral_iff _).mpr ⟨e, rfl⟩

/-- **Theorem A** of [Monk1964], second half: the converse of the Lyndon algebra is trivial. -/
instance : TrivialStar (ComplexAlgebra (lyndon e h)) where
  star_trivial x := by
    ext a
    rw [mem_star, lyndon_conv]

end ComplexAlgebra

end Cslib.RelationAlgebra
