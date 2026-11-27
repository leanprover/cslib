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

universe u₁ u₂ v w

namespace Cslib.RelationAlgebra

variable {α α₁ : Type u₁} {α₂ : Type u₂} [RelationAlgebra α] [RelationAlgebra α₁]
  [RelationAlgebra α₂] {ι : Type v} {β : ι → Type w}

variable (α ι β) in
/-- A representation of a relation algebra is an injective morphism into a product of relations. -/
structure Representation where
  /-- A `RelationAlgebraHom` into a product of relations. -/
  hom : RelationAlgebraHom α (∀ i, SetRel (β i) (β i))
  injective : Function.Injective hom

variable (α) in
/-- A relation algebra is representable if a `Representation` exists. -/
def Representable : Prop := ∃ (ι : Type u₁) (β : ι → Type u₁), Nonempty (Representation α ι β)

/-- Representations can be precomposed with injective homomorphisms. -/
def Representation.compInjective (r : Representation α₂ ι β) (f : RelationAlgebraHom α₁ α₂)
    (hf : Function.Injective f) : Representation α₁ ι β where
  hom := r.hom.comp f
  injective := r.injective.comp hf

/-- Representations can be precomposed with equivalences. -/
def Representation.compEquiv (r : Representation α₂ ι β) (e : RelationAlgebraEquiv α₁ α₂) :
    Representation α₁ ι β := r.compInjective e.toHom e.toHom_injective

/-- A relation algebra that embeds into a representable relation algebra is representable. -/
theorem Representable.of_injective (f : RelationAlgebraHom α α₁) (hf : Function.Injective f)
    (h : Representable α₁) : Representable α :=
  let ⟨ι, β, ⟨r⟩⟩ := h
  ⟨ι, β, ⟨r.compInjective f hf⟩⟩

/-- Representability is preserved by equivalence. -/
theorem Representable.of_equiv (e : RelationAlgebraEquiv α α₁) (h : Representable α₁) :
    Representable α :=
  h.of_injective e.toHom e.toHom_injective

theorem _root_.Cslib.RelationAlgebraEquiv.representable_iff (e : RelationAlgebraEquiv α α₁) :
    Representable α ↔ Representable α₁ :=
  ⟨fun h ↦ h.of_equiv e.symm, fun h ↦ h.of_equiv e⟩

/-- A `Representation α ι β` in arbitrary universes can be contracted to the universe of `α`. -/
proof_wanted representable_univ (r : Representation α ι β) : Representable α

end Cslib.RelationAlgebra
