/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.FiniteRepresentation

/-!
# Atomic square representations of finite integral relation algebras

A representation of a finite integral relation algebra can be read as a labelling of a
single nonempty square by its atoms. This reduces arbitrary product representations to
atomic networks, without imposing a finiteness assumption on their bases.
-/

@[expose] public section

universe u

namespace Cslib.RelationAlgebra

namespace AtomRepresentation

variable {j k : ℕ} {T : IntegralCycleTable j k} {Base : Type u}

private theorem hom_mem (f : RelationAlgebraHom (Complex T) (SquareRelations Base))
    (a : Complex T) (x y : Base) :
    f a (x, y) ↔ ∃ c ∈ a.atoms, f (Complex.atom T c) (x, y) := by
  obtain ⟨s⟩ := a
  induction s using Finset.induction_on with
  | empty =>
    change f (⊥ : Complex T) (x, y) ↔ ∃ c ∈ (∅ : Finset (Atom j k)), _
    rw [map_bot]
    change False ↔ _
    simp
  | @insert c s hc ih =>
    have heq : (⟨insert c s⟩ : Complex T) = Complex.atom T c ⊔ ⟨s⟩ := by
      apply Complex.ext
      simp [Complex.atom]
    rw [heq, map_sup]
    change (f (Complex.atom T c) (x, y) ∨ f ⟨s⟩ (x, y)) ↔
      ∃ z ∈ insert c s, f (Complex.atom T z) (x, y)
    simpa using or_congr Iff.rfl ih

private theorem exists_label (f : RelationAlgebraHom (Complex T) (SquareRelations Base))
    (x y : Base) : ∃ c, f (Complex.atom T c) (x, y) := by
  have htop : f ⊤ (x, y) := by rw [map_top]; trivial
  obtain ⟨c, _, hc⟩ := (hom_mem f ⊤ x y).mp htop
  exact ⟨c, hc⟩

/-- The unique atom whose image contains a given edge of a square homomorphism. -/
noncomputable def homLabel (f : RelationAlgebraHom (Complex T) (SquareRelations Base))
    (x y : Base) : Atom j k :=
  Classical.choose (show ∃ c, f (Complex.atom T c) (x, y) from by exact exists_label f x y)

private theorem homLabel_spec (f : RelationAlgebraHom (Complex T) (SquareRelations Base))
    (x y : Base) : f (Complex.atom T (homLabel f x y)) (x, y) :=
  Classical.choose_spec (exists_label f x y)

private theorem label_unique (f : RelationAlgebraHom (Complex T) (SquareRelations Base))
    {a b : Atom j k} {x y : Base} (ha : f (Complex.atom T a) (x, y))
    (hb : f (Complex.atom T b) (x, y)) : a = b := by
  by_contra h
  have hi : Complex.atom T a ⊓ Complex.atom T b = ⊥ := by
    apply Complex.ext
    simp [Complex.atom, h]
  have hf : f (Complex.atom T a ⊓ Complex.atom T b) (x, y) := by
    rw [map_inf]
    exact ⟨ha, hb⟩
  rw [hi, map_bot] at hf
  exact hf

private theorem homLabel_mem (f : RelationAlgebraHom (Complex T) (SquareRelations Base))
    (a : Complex T) (x y : Base) :
    homLabel f x y ∈ a.atoms ↔ f a (x, y) := by
  rw [hom_mem]
  constructor
  · intro h
    exact ⟨homLabel f x y, h, homLabel_spec f x y⟩
  · rintro ⟨c, hc, hf⟩
    rw [label_unique f (homLabel_spec f x y) hf]
    exact hc

private theorem homLabel_eq (f : RelationAlgebraHom (Complex T) (SquareRelations Base))
    (a : Atom j k) (x y : Base) :
    homLabel f x y = a ↔ f (Complex.atom T a) (x, y) := by
  simpa only [Complex.atom, Finset.mem_singleton] using
    homLabel_mem f (Complex.atom T a) x y

/-- Every homomorphism to an inhabited square yields an atomic representation.

The integral identity atom ensures that each atomic relation occurs: its product with
its converse contains every diagonal edge. -/
noncomputable def ofHom [Nonempty Base]
    (f : RelationAlgebraHom (Complex T) (SquareRelations Base)) : AtomRepresentation T Base where
  label := homLabel f
  surjective := by
    intro a
    let x : Base := Classical.choice inferInstance
    have hi : (1 : Complex T) ≤ Complex.atom T a * Complex.atom T a.converse := by
      apply (Complex.atom_le_mul_iff T _ _ _).mpr
      exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    have hx : f (1 : Complex T) (x, x) := by rw [map_one]; rfl
    have hp := (OrderHomClass.mono f hi) hx
    rw [map_mul] at hp
    obtain ⟨y, hxy, _⟩ := hp
    exact ⟨(x, y), (homLabel_eq f a x y).mpr hxy⟩
  identity x y := by
    rw [homLabel_eq]
    change f 1 (x, y) ↔ x = y
    rw [map_one]
    rfl
  converse x y := by
    apply (homLabel_eq f _ y x).mpr
    rw [← Complex.star_atom, map_star]
    exact homLabel_spec f x y
  composition a b x y := by
    rw [← Complex.atom_le_mul_iff]
    change {homLabel f x y} ⊆ (Complex.atom T a * Complex.atom T b).atoms ↔ _
    rw [Finset.singleton_subset_iff, homLabel_mem, map_mul]
    change (∃ z, f (Complex.atom T a) (x, z) ∧ f (Complex.atom T b) (z, y)) ↔ _
    simp only [homLabel_eq]

end AtomRepresentation

/-- A finite integral cycle algebra is representable exactly when its atoms label a square. -/
theorem representable_iff_nonempty_atomRepresentation {j k : ℕ} (T : IntegralCycleTable j k) :
    Representable (Complex T) ↔ ∃ Base : Type, Nonempty (AtomRepresentation T Base) := by
  constructor
  · rintro ⟨ι, Base, ⟨r⟩⟩
    have hex : ∃ i, Nonempty (Base i) := by
      by_contra h
      have heq : (⊥ : Complex T) = ⊤ := by
        apply r.injective
        funext i p
        exact False.elim (h ⟨i, ⟨p.1⟩⟩)
      have hmem := congrArg (fun a : Complex T => none ∈ a.atoms) heq
      simp at hmem
    obtain ⟨i, hi⟩ := hex
    let := hi
    exact ⟨Base i, ⟨AtomRepresentation.ofHom (r.hom i)⟩⟩
  · rintro ⟨Base, ⟨r⟩⟩
    exact r.representable

end Cslib.RelationAlgebra
