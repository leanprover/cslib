/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Pi
public import Mathlib.Basic.Rel

/-!
# Representable relation algebras

One of the primary notions of interest in the study of relation algebras is the notion of
*representation* by a relation algebra of concrete relations.

Recall Stone's representation for Boolean algebras which (at a low level of
generality) states that every Boolean algebra has an isomorphism into a particuliar "field of sets".
Tarski's hope was that an analogous property would hold for abstract relation algebras, with the
isomorphism desired being into a relation algebra of concrete relations. This turns out to be false,
with the clasification and conditions for the representation of a relation algebra thus being a
matter of much interest.

-/

@[expose] public section

universe u v w

namespace Cslib.RelationAlgebra

/-- Relations over a type `α`. This definition exists because we need to prevent some instances from
  from Mathlib being included. -/
def SquareRelations (α : Type u) : Type u := SetRel α α

namespace SquareRelations

instance (α : Type u) : BooleanAlgebra (SquareRelations α) :=
  inferInstanceAs (BooleanAlgebra (SetRel α α))

instance (α : Type u) : Monoid (SquareRelations α) where
  one := SetRel.id
  mul := SetRel.comp
  mul_assoc := SetRel.comp_assoc
  one_mul := SetRel.id_comp
  mul_one := SetRel.comp_id

instance (α : Type u) : StarMul (SquareRelations α) where
  star := SetRel.inv
  star_involutive := fun _ => SetRel.inv_inv
  star_mul := SetRel.inv_comp

instance (α : Type u) : RelationAlgebra (SquareRelations α) where
  sup_mul a b c := by
    unfold SquareRelations at *
    ext ⟨x, z⟩
    exact (exists_congr fun y => or_and_right).trans exists_or
  star_sup _ _ := rfl
  tarski a b := by
    rintro ⟨x, z⟩ ⟨y, hxy, hyz⟩ hxz
    exact hyz ⟨x, hxy, hxz⟩

end SquareRelations

/-- A representation of a relation algebra is an injective morphism into a product of relations. -/
structure Representation (α : Type u) [RelationAlgebra α] (ι : Type v) (β : ι → Type w) where
  /-- A `RelationAlgebraHom` into a product of relations. -/
  hom : RelationAlgebraHom α (∀ i, SquareRelations (β i))
  injective : Function.Injective hom

/-- A relation algebra is representable if a `Representation` exists. -/
def Representable (α : Type u) [RelationAlgebra α] : Prop :=
  ∃ (ι : Type u) (β : ι → Type u), Nonempty (Representation α ι β)

/-- A `Representation α ι β` in arbitrary universes can be contracted to the universe of `α`. -/
proof_wanted representable_univ {α : Type u} [RelationAlgebra α] {ι : Type v} {β :  ι → Type w} :
    Representation α ι β → Representable α

end Cslib.RelationAlgebra

