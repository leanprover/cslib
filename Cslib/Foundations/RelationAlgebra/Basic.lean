/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Init
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Order.Atoms
public import Mathlib.Order.BooleanAlgebra.Defs

/-!
# Relation algebras

A relation algebra in the sense of Tarski (not to be confused with a relational algebra) is an
extension of Boolean algebras that are designed to form an algebraic analysis of relations,
`α → α → Prop` in Lean. They have applications in computer science such as the theory of constraint
satisfaction as well as mathematical connections such as combinatorics.

## References

* [R. Maddux, *Relation Algebras*][Maddux2006]

-/

@[expose] public section

namespace Cslib

/-- The class of relation algebras. Note the notational differences from the literature. In addition
to inheriting Mathlib's notations for Boolean algebras, `star` is used for converse, and the monoid
reduct for composition uses multiplicative notation. -/
class RelationAlgebra (α : Type*) extends BooleanAlgebra α, Monoid α, StarMul α where
  sup_mul (a b c : α) : (a ⊔ b) * c = a * c ⊔ b * c
  star_sup (a b : α) : star (a ⊔ b) = star a ⊔ star b
  tarski (a b : α) : star a * (a * b)ᶜ ≤ bᶜ

namespace RelationAlgebra

/-- A `RelationAlgebra` can be constructed using Tarski's original ten axioms. -/
@[instance_reducible]
def_wanted ofTarski {α : Type*} [Max α] [Compl α] [Mul α] [One α] [Star α]
    (sup_comm : ∀ a b : α, a ⊔ b = b ⊔ a)
    (sup_assoc : ∀ a b c : α, (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c))
    (huntington : ∀ a b : α, (aᶜ ⊔ b)ᶜ ⊔ (aᶜ ⊔ bᶜ)ᶜ = a)
    (mul_assoc : ∀ a b c : α, (a * b) * c = a * (b * c))
    (mul_one : ∀ a : α, a * 1 = a)
    (star_star : ∀ a : α, star (star a) = a)
    (star_mul : ∀ a b : α, star (a * b) = star b * star a)
    (sup_mul : ∀ a b c : α, (a ⊔ b) * c = a * c ⊔ b * c)
    (star_sup : ∀ a b : α, star (a ⊔ b) = star a ⊔ star b)
    (tarski : ∀ a b : α, star a * (a * b)ᶜ ⊔ bᶜ = bᶜ) : RelationAlgebra α

variable {α : Type*} [RelationAlgebra α]

theorem star_mono : Monotone (star : α → α) := by
  intro a b h
  rw [← sup_eq_right, ← star_sup, sup_eq_right.mpr h]

theorem mul_sup (a b c : α) : a * (b ⊔ c) = a * b ⊔ a * c := by
  apply star_injective
  simp [star_sup, sup_mul]

theorem left_modular (a b c : α) : a * b ⊓ c ≤ a * (b ⊓ star a * c) :=
  calc
    a * b ⊓ c = (a * (b ⊓ star a * c) ⊔ a * (b ⊓ (star a * c)ᶜ)) ⊓ c := by
      rw [← mul_sup, ← inf_sup_left, sup_compl_eq_top, inf_top_eq]
    _ ≤ (a * (b ⊓ star a * c) ⊔ a * (star a * c)ᶜ) ⊓ c := by
      apply inf_le_inf_right
      apply sup_le_sup_left
      rw [← sup_eq_right, ← mul_sup, sup_eq_right.mpr inf_le_right]
    _ ≤ (a * (b ⊓ star a * c) ⊔ cᶜ) ⊓ c := by
      apply inf_le_inf_right
      apply sup_le_sup_left
      simpa only [star_star] using tarski (star a) c
    _ = a * (b ⊓ star a * c) ⊓ c := by rw [inf_sup_right, compl_inf_self, sup_bot_eq]
    _ ≤ a * (b ⊓ star a * c) := inf_le_left

/-- Composition is monotone in its second argument. -/
theorem mul_le_mul_left {a b : α} (h : a ≤ b) (c : α) : c * a ≤ c * b := by
  rw [← sup_eq_right, ← mul_sup, sup_eq_right.mpr h]

/-- Composition is monotone in its first argument. -/
theorem mul_le_mul_right {a b : α} (h : a ≤ b) (c : α) : a * c ≤ b * c := by
  rw [← sup_eq_right, ← sup_mul, sup_eq_right.mpr h]

/-- Composition is monotone in both arguments. -/
theorem mul_le_mul {a b c d : α} (hab : a ≤ b) (hcd : c ≤ d) : a * c ≤ b * d :=
  (mul_le_mul_right hab c).trans (mul_le_mul_left hcd b)

/-- Converse preserves the empty relation. -/
@[simp] theorem star_bot : star (⊥ : α) = ⊥ := by
  apply le_antisymm _ bot_le
  simpa only [star_star] using star_mono (bot_le : (⊥ : α) ≤ star ⊥)

/-- Converse preserves the greatest relation. -/
@[simp] theorem star_top : star (⊤ : α) = ⊤ := by
  apply le_antisymm le_top
  simpa only [star_star] using star_mono (le_top : star (⊤ : α) ≤ ⊤)

/-- Converse preserves meets. -/
theorem star_inf (a b : α) : star (a ⊓ b) = star a ⊓ star b := by
  apply le_antisymm (le_inf (star_mono inf_le_left) (star_mono inf_le_right))
  have h : star (star a ⊓ star b) ≤ a ⊓ b := by
    simpa only [star_star] using
      le_inf (star_mono (inf_le_left : star a ⊓ star b ≤ star a))
        (star_mono (inf_le_right : star a ⊓ star b ≤ star b))
  simpa only [star_star] using star_mono h

/-- Converse preserves complements. -/
@[simp] theorem star_compl (a : α) : star aᶜ = (star a)ᶜ := by
  apply Eq.symm
  apply compl_unique
  · rw [← star_inf, inf_compl_self, star_bot]
  · rw [← star_sup, sup_compl_eq_top, star_top]

/-- The right-handed form of Tarski's axiom. -/
theorem right_tarski (a b : α) : (a * b)ᶜ * star b ≤ aᶜ := by
  simpa only [star_mul, star_compl, star_star] using
    star_mono (tarski (star b) (star a))

/-- Composing with the empty relation on the right yields the empty relation. -/
@[simp] theorem mul_bot (a : α) : a * ⊥ = ⊥ := by
  apply le_antisymm _ bot_le
  calc
    a * ⊥ ≤ a * (star a * ⊤)ᶜ := mul_le_mul_left bot_le a
    _ ≤ (⊤ : α)ᶜ := by simpa only [star_star] using tarski (star a) ⊤
    _ = ⊥ := compl_top

/-- Composing with the empty relation on the left yields the empty relation. -/
@[simp] theorem bot_mul (a : α) : ⊥ * a = ⊥ := by
  apply star_injective
  simp only [star_mul, star_bot, mul_bot]

/-- Every element lies below its composition with the greatest relation on the left. -/
theorem le_top_mul (a : α) : a ≤ ⊤ * a := by
  simpa only [one_mul] using mul_le_mul_right (le_top : (1 : α) ≤ ⊤) a

/-- Every element lies below its composition with the greatest relation on the right. -/
theorem le_mul_top (a : α) : a ≤ a * ⊤ := by
  simpa only [mul_one] using mul_le_mul_left (le_top : (1 : α) ≤ ⊤) a

/-- The greatest relation is idempotent under composition. -/
@[simp] theorem top_mul_top : (⊤ : α) * ⊤ = ⊤ :=
  le_antisymm le_top (le_top_mul ⊤)

/-- A relation algebra is *integral* when its identity is an atom. -/
def Integral : Prop := IsAtom (1 : α)

/-- The set of identity atoms. -/
def IdentityAtoms : Set α := {a : α | IsAtom a ∧ a ≤ 1}

/-- The set of symmetric diversity atoms, those below the complement of identity. -/
def SymmetricDiversityAtoms : Set α := {a : α | IsAtom a ∧ a ≤ 1ᶜ ∧ star a = a}

/-- The set of nonsymmetric diversity atoms. The diversity condition follows from
`le_compl_one_of_mem_nonsymmetricDiversityAtoms`. -/
def NonsymmetricDiversityAtoms : Set α := {a : α | IsAtom a ∧ star a ≠ a}

/-- Every nonsymmetric atom lies below the complement of identity. -/
theorem le_compl_one_of_mem_nonsymmetricDiversityAtoms {a : α}
    (h : a ∈ NonsymmetricDiversityAtoms) : a ≤ 1ᶜ := by
  rw [le_compl_iff_disjoint_right, ← h.1.not_le_iff_disjoint]
  intro ha
  have hstar : a ≤ star a := by calc
     a = a * 1 ⊓ 1 := by rw [mul_one, inf_eq_left.mpr ha]
     _ ≤ a * (1 ⊓ star a * 1) := left_modular a 1 1
     _ ≤ 1 * (1 ⊓ star a * 1) := by rw [← sup_eq_right, ← sup_mul, sup_eq_right.mpr ha]
     _ = 1 ⊓ star a := by rw [one_mul, mul_one]
     _ ≤ star a := inf_le_right
  have : star a ≤ a := by calc
    star a ≤ star (star a) := star_mono hstar
    _ = a := star_star a
  cases h
  grind

end RelationAlgebra

end Cslib
