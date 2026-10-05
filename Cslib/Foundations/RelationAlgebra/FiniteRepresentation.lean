/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Cycles
public import Mathlib.Algebra.Group.Basic

/-!
# Representations of finite relation algebras by atom labels

A labelling of the edges of a square by atoms determines a representation of the complex
algebra when all atoms occur and the labels respect identity, converse, and composition.
For a finite base, these conditions can be checked by finite computation. Infinite bases
are also allowed: finiteness refers to the algebra, not to its representations.
-/

@[expose] public section

universe u

namespace Cslib.RelationAlgebra

variable {j k : ℕ}

/-- An atomic representation of a finite integral cycle table on a square. -/
structure AtomRepresentation (T : IntegralCycleTable j k) (Base : Type u) where
  /-- The unique atom labelling each ordered pair of base points. -/
  label : Base → Base → Atom j k
  /-- Every atom labels at least one edge. -/
  surjective : Function.Surjective (fun p : Base × Base => label p.1 p.2)
  /-- Exactly the diagonal edges have the identity label. -/
  identity (x y : Base) : label x y = none ↔ x = y
  /-- Reversing an edge takes the converse of its label. -/
  converse (x y : Base) : label y x = Atom.converse (label x y)
  /-- Every allowed atomic product has exactly the required intermediate witnesses. -/
  composition (a b : Atom j k) (x y : Base) :
    cycleClosure T.cycles a b (label x y) ↔ ∃ z, label x z = a ∧ label z y = b

namespace AtomRepresentation

variable {T : IntegralCycleTable j k} {Base : Type u} (r : AtomRepresentation T Base)

/-- Interpret a complex-algebra element as the union of the edges labelled by its atoms. -/
def toHom : RelationAlgebraHom (Complex T) (SquareRelations Base) where
  toFun a := fun p => r.label p.1 p.2 ∈ a.atoms
  map_sup' a b := by
    funext p
    exact propext Finset.mem_union
  map_inf' a b := by
    funext p
    exact propext Finset.mem_inter
  map_top' := by
    funext p
    exact propext (iff_true_intro (Finset.mem_univ _))
  map_bot' := by
    funext p
    exact propext (iff_false_intro (Finset.notMem_empty _))
  map_one' := by
    funext p
    apply propext
    change r.label p.1 p.2 ∈ ({none} : Finset (Atom j k)) ↔ p.1 = p.2
    rw [Finset.mem_singleton, r.identity]
  map_mul' a b := by
    funext p
    apply propext
    change r.label p.1 p.2 ∈
      (Finset.univ.filter fun z =>
        ∃ x ∈ a.atoms, ∃ y ∈ b.atoms, cycleClosure T.cycles x y z) ↔
      ∃ z, r.label p.1 z ∈ a.atoms ∧ r.label z p.2 ∈ b.atoms
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, hx, y, hy, hxy⟩
      obtain ⟨z, hz, hz'⟩ := (r.composition x y p.1 p.2).mp hxy
      exact ⟨z, hz ▸ hx, hz' ▸ hy⟩
    · rintro ⟨z, hz, hz'⟩
      exact ⟨r.label p.1 z, hz, r.label z p.2, hz',
        (r.composition _ _ _ _).mpr ⟨z, rfl, rfl⟩⟩
  map_star' a := by
    funext p
    apply propext
    change r.label p.1 p.2 ∈ a.atoms.image Atom.converse ↔ r.label p.2 p.1 ∈ a.atoms
    rw [Finset.mem_image, r.converse p.1 p.2]
    constructor
    · rintro ⟨z, hz, h⟩
      rw [← h, Atom.converse_converse]
      exact hz
    · intro h
      exact ⟨Atom.converse (r.label p.1 p.2), h, Atom.converse_converse _⟩

/-- All atoms occur, so the interpretation distinguishes distinct algebra elements. -/
theorem toHom_injective : Function.Injective r.toHom := by
  intro a b h
  have hab : a.atoms = b.atoms := by
    apply Finset.ext
    intro z
    obtain ⟨p, hp⟩ := r.surjective z
    change r.label p.1 p.2 = z at hp
    have hm := congrFun h p
    change (r.label p.1 p.2 ∈ a.atoms) = (r.label p.1 p.2 ∈ b.atoms) at hm
    rw [hp] at hm
    exact iff_of_eq hm
  cases a
  cases b
  exact congrArg Complex.mk hab

/-- Atom labels on a small base give a representation in the universe of the finite algebra. -/
theorem representable {Base : Type} (r : AtomRepresentation T Base) :
    Representable (Complex T) :=
  representable_of_injective_hom r.toHom r.toHom_injective

end AtomRepresentation

/-- A partition of a group that realizes the atoms and their multiplication table. -/
structure GroupAtomRepresentation (T : IntegralCycleTable j k) (G : Type u) [Group G] where
  /-- The atom containing each group element. -/
  label : G → Atom j k
  /-- Each atomic block is nonempty. -/
  surjective : Function.Surjective label
  /-- The identity block is the singleton containing the group identity. -/
  identity (g : G) : label g = none ↔ g = 1
  /-- Group inversion sends each block to its converse. -/
  converse (g : G) : label g⁻¹ = Atom.converse (label g)
  /-- A block product contains precisely the elements allowed by the cycle table. -/
  composition (a b : Atom j k) (g : G) :
    cycleClosure T.cycles a b (label g) ↔ ∃ h, label h = a ∧ label (h⁻¹ * g) = b

namespace GroupAtomRepresentation

variable {T : IntegralCycleTable j k} {G : Type u} [Group G]

/-- Label an edge by the block of its group difference. -/
def toAtomRepresentation (r : GroupAtomRepresentation T G) : AtomRepresentation T G where
  label x y := r.label (x⁻¹ * y)
  surjective a := by
    obtain ⟨g, hg⟩ := r.surjective a
    exact ⟨(1, g), by simpa using hg⟩
  identity x y := by simp [r.identity, inv_mul_eq_one]
  converse x y := by simpa using r.converse (x⁻¹ * y)
  composition a b x y := by
    rw [r.composition]
    constructor
    · rintro ⟨g, hg, hg'⟩
      exact ⟨x * g, by simpa using hg, by simpa [mul_assoc] using hg'⟩
    · rintro ⟨z, hz, hz'⟩
      exact ⟨x⁻¹ * z, hz, by simpa [mul_assoc] using hz'⟩

/-- A group partition with the prescribed atomic products represents the complex algebra. -/
theorem representable {G : Type} [Group G] (r : GroupAtomRepresentation T G) :
    Representable (Complex T) :=
  r.toAtomRepresentation.representable

end GroupAtomRepresentation

end Cslib.RelationAlgebra
