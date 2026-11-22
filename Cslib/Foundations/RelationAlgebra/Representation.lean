/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Pi

/-!
# Representable relation algebras

One of the primary notions of interest in the study of relation algebras is the notion of
*representation* by a relation algebra of concrete relations.

Recall Stone's representation for Boolean algebras which (at a low level of
generality) states that every Boolean algebra has an isomorphism into a particular "field of sets".
Tarski's hope was that an analogous property would hold for abstract relation algebras, with the
isomorphism desired being into a relation algebra of concrete relations. This turns out to be false,
with the classification and conditions for the representation of a relation algebra thus being a
matter of much interest.

-/

@[expose] public section

universe u v w

namespace Cslib.RelationAlgebra

/-- A representation of a relation algebra is an injective morphism into a product of relations. -/
structure Representation (α : Type u) [RelationAlgebra α] (ι : Type v) (β : ι → Type w) where
  /-- A `RelationAlgebraHom` into a product of relations. -/
  hom : RelationAlgebraHom α (∀ i, SetRel (β i) (β i))
  injective : Function.Injective hom

/-- A relation algebra is representable if a `Representation` exists. -/
def Representable (α : Type u) [RelationAlgebra α] : Prop :=
  ∃ (ι : Type u) (β : ι → Type u), Nonempty (Representation α ι β)

/-- Representations can be precomposed with injective homomorphisms. -/
def Representation.compInjective {α α' ι : Type*} {β : ι → Type*} [RelationAlgebra α]
    [RelationAlgebra α'] (r : Representation α' ι β) (f : RelationAlgebraHom α α')
    (hf : Function.Injective f) : Representation α ι β where
  hom := r.hom.comp f
  injective := r.injective.comp hf

/-- Representations can be precomposed with equivalences. -/
def Representation.compEquiv {α α' ι : Type*} {β : ι → Type*} [RelationAlgebra α]
    [RelationAlgebra α'] (r : Representation α' ι β) (e : RelationAlgebraEquiv α α') :
    Representation α ι β := r.compInjective e.toHom e.toHom_injective

/-- A relation algebra that embeds into a representable relation algebra is representable. -/
theorem Representable.of_injective {α α' : Type u} [RelationAlgebra α] [RelationAlgebra α']
    (f : RelationAlgebraHom α α') (hf : Function.Injective f) (h : Representable α') :
    Representable α :=
  let ⟨ι, β, ⟨r⟩⟩ := h
  ⟨ι, β, ⟨r.compInjective f hf⟩⟩

/-- Representability is preserved by equivalence. -/
theorem Representable.of_equiv {α α' : Type u} [RelationAlgebra α] [RelationAlgebra α']
    (heqv : Nonempty (RelationAlgebraEquiv α α')) (h : Representable α') :
    Representable α := h.of_injective heqv.some.toHom heqv.some.toHom_injective

/-- A `Representation α ι β` in arbitrary universes can be contracted to the universe of `α`. -/
proof_wanted representable_univ {α : Type u} [RelationAlgebra α] {ι : Type v} {β : ι → Type w} :
    Representation α ι β → Representable α

end Cslib.RelationAlgebra
