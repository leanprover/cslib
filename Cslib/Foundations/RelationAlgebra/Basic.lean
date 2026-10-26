/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Init
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Order.Atoms
public import Cslib.Foundations.Order.Huntington

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

/-- The relation algebra of a complete Boolean algebra. -/
class CompleteRelationAlgebra (α : Type*) extends RelationAlgebra α, CompleteBooleanAlgebra α

/-- The relation algebra of a complete and atomic Boolean algebra. -/
class CompleteAtomicRelationAlgebra (α : Type*) extends CompleteRelationAlgebra α,
    CompleteAtomicBooleanAlgebra α

namespace RelationAlgebra

/-- A `RelationAlgebra` can be constructed using Tarski's original ten axioms. -/
@[instance_reducible]
def ofTarski {α : Type*} [Max α] [Compl α] [Mul α] [One α] [Star α]
    (sup_comm : ∀ a b : α, a ⊔ b = b ⊔ a)
    (sup_assoc : ∀ a b c : α, (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c))
    (huntington : ∀ a b : α, (aᶜ ⊔ b)ᶜ ⊔ (aᶜ ⊔ bᶜ)ᶜ = a)
    (mul_assoc : ∀ a b c : α, (a * b) * c = a * (b * c))
    (mul_one : ∀ a : α, a * 1 = a)
    (star_involutive : ∀ a : α, star (star a) = a)
    (star_mul : ∀ a b : α, star (a * b) = star b * star a)
    (sup_mul : ∀ a b c : α, (a ⊔ b) * c = a * c ⊔ b * c)
    (star_sup : ∀ a b : α, star (a ⊔ b) = star a ⊔ star b)
    (tarski : ∀ a b : α, star a * (a * b)ᶜ ⊔ bᶜ = bᶜ) : RelationAlgebra α where
  __ := @HuntingtonAlgebra.instBooleanAlgebra α {
    default := 1
    assoc := sup_assoc
    comm := sup_comm
    huntington := huntington
  }
  mul_assoc := mul_assoc
  mul_one := mul_one
  one_mul a := by
    suffices star (1 : α) = 1 by
      rw [← star_involutive (1 * a), star_mul, this, mul_one, star_involutive]
    rw [← star_involutive (star 1), ← mul_one (star 1), star_mul, star_involutive, mul_one,
      star_involutive]
  star_involutive := star_involutive
  star_mul := star_mul
  sup_mul := sup_mul
  star_sup := star_sup
  tarski := tarski

variable {α : Type*} [RelationAlgebra α]

@[gcongr]
theorem star_mono : Monotone (star : α → α) := by
  intro a b h
  rw [← sup_eq_right, ← star_sup, sup_of_le_right h]

theorem mul_sup (a b c : α) : a * (b ⊔ c) = a * b ⊔ a * c := by
  apply star_injective
  simp [star_sup, sup_mul]

instance : MulLeftMono α where
  elim a b c h := by simp [← sup_eq_right, ← mul_sup, sup_of_le_right h]

instance : MulRightMono α where
  elim a b c h := by simp [← sup_eq_right, ← sup_mul, sup_of_le_right h]

@[simp]
theorem mul_bot (a : α) : a * ⊥ = ⊥ := by
  apply le_antisymm _ bot_le
  calc
    a * ⊥ ≤ a * (star a * ⊤)ᶜ := mul_le_mul_right bot_le a
    _ ≤ ⊥ := by simpa using tarski (star a) ⊤

@[simp]
theorem isAtom_star_iff {a : α} : IsAtom (star a) ↔ IsAtom a :=
  (Equiv.Perm.star.toOrderIso star_mono star_mono).isAtom_iff a

theorem atom_cycle_left {r s p : α} (hs : IsAtom s) (hp : p ≠ ⊥) (h : p ≤ r * s) :
    s ≤ star r * p := by
  by_contra hsnot
  have hsc : s ≤ (star r * p)ᶜ := le_compl_iff_disjoint_right.mpr (hs.not_le_iff_disjoint.mp hsnot)
  have hc : p ≤ pᶜ := calc
    p ≤ r * s := h
    _ ≤ r * (star r * p)ᶜ := mul_le_mul_right hsc r
    _ ≤ pᶜ := by simpa using tarski (star r) p
  simp_all

theorem left_modular (a b c : α) : a * b ⊓ c ≤ a * (b ⊓ star a * c) :=
  calc
    a * b ⊓ c = (a * (b ⊓ star a * c) ⊔ a * (b ⊓ (star a * c)ᶜ)) ⊓ c := by
      rw [← mul_sup, ← inf_sup_left, sup_compl_eq_top, inf_top_eq]
    _ ≤ (a * (b ⊓ star a * c) ⊔ a * (star a * c)ᶜ) ⊓ c := by gcongr; exact inf_le_right
    _ ≤ (a * (b ⊓ star a * c) ⊔ cᶜ) ⊓ c := by grw [← tarski (star a) c, star_star]
    _ = a * (b ⊓ star a * c) ⊓ c := by rw [inf_sup_right, compl_inf_self, sup_bot_eq]
    _ ≤ a * (b ⊓ star a * c) := inf_le_left

/-- If an atom lies below a product, its right factor can be replaced by an atom below it. -/
theorem exists_atom_le_mul_right [IsAtomic α] {a b p : α} (hp : IsAtom p) (h : p ≤ a * b) :
    ∃ s, IsAtom s ∧ s ≤ b ∧ p ≤ a * s := by
  have hmod : p ≤ a * (b ⊓ star a * p) := by simpa [inf_eq_right.mpr h] using left_modular a b p
  obtain hb | ⟨s, hs, hsb⟩ := eq_bot_or_exists_atom_le (b ⊓ star a * p)
  · rw [hb, mul_bot] at hmod
    exact (hp.ne_bot (le_bot_iff.mp hmod)).elim
  · use s, hs, hsb.trans inf_le_left
    simpa using atom_cycle_left hp hs.ne_bot (hsb.trans inf_le_right)

/-- If an atom lies below a product, its left factor can be replaced by an atom below it. -/
theorem exists_atom_le_mul_left [IsAtomic α] {a b p : α} (hp : IsAtom p) (h : p ≤ a * b) :
    ∃ r, IsAtom r ∧ r ≤ a ∧ p ≤ r * b := by
  obtain ⟨s, hs, hsa, hps⟩ :=
    exists_atom_le_mul_right (isAtom_star_iff.mpr hp) (by simpa using star_mono h)
  exact ⟨star s, isAtom_star_iff.mpr hs, by simpa using star_mono hsa, by simpa using star_mono hps⟩

/-- A relation algebra is *integral* when its identity is an atom. -/
def IsIntegral (α : Type*) [RelationAlgebra α] : Prop := IsAtom (1 : α)

/-- The set of identity atoms. -/
def identityAtoms (α : Type*) [RelationAlgebra α] : Set α := {a : α | IsAtom a ∧ a ≤ 1}

/-- The set of symmetric diversity atoms, those below the complement of identity. -/
def symmetricDiversityAtoms (α : Type*) [RelationAlgebra α] : Set α :=
  {a : α | IsAtom a ∧ a ≤ 1ᶜ ∧ star a = a}

/-- The set of nonsymmetric diversity atoms. The diversity condition follows from
`le_compl_one_of_mem_nonsymmetricDiversityAtoms`. -/
def nonsymmetricDiversityAtoms (α : Type*) [RelationAlgebra α] : Set α :=
  {a : α | IsAtom a ∧ star a ≠ a}

/-- Every nonsymmetric atom lies below the complement of identity. -/
theorem le_compl_one_of_mem_nonsymmetricDiversityAtoms {a : α}
    (h : a ∈ nonsymmetricDiversityAtoms α) : a ≤ 1ᶜ := by
  rw [le_compl_iff_disjoint_right, ← h.1.not_le_iff_disjoint]
  intro ha
  have hstar : a ≤ star a := by calc
     a = a * 1 ⊓ 1 := by rw [mul_one, inf_eq_left.mpr ha]
     _ ≤ a * (1 ⊓ star a * 1) := left_modular a 1 1
     _ ≤ 1 * (1 ⊓ star a * 1) := mul_le_mul_left ha _
     _ = 1 ⊓ star a := by rw [one_mul, mul_one]
     _ ≤ star a := inf_le_right
  have : star a ≤ a := by calc
    star a ≤ star (star a) := star_mono hstar
    _ = a := star_star a
  cases h
  grind

end RelationAlgebra

end Cslib
