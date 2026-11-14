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

variable {α : Type u} {R S : SquareRelations α} {a b c : α}

instance : Membership (α × α) (SquareRelations α) :=
  inferInstanceAs (Membership (α × α) (SetRel α α))

/-- The element of `SquareRelations α` given by a binary relation. -/
def ofRel (r : α → α → Prop) : SquareRelations α :=
  show SetRel α α from {p | r p.1 p.2}

@[ext]
theorem ext (h : ∀ a b, (a, b) ∈ R ↔ (a, b) ∈ S) : R = S :=
  Set.ext fun ⟨a, b⟩ => h a b

@[simp]
theorem mem_ofRel {r : α → α → Prop} : (a, b) ∈ ofRel r ↔ r a b := .rfl

@[simp]
theorem mem_sup : (a, b) ∈ R ⊔ S ↔ (a, b) ∈ R ∨ (a, b) ∈ S := .rfl

@[simp]
theorem mem_inf : (a, b) ∈ R ⊓ S ↔ (a, b) ∈ R ∧ (a, b) ∈ S := .rfl

@[simp]
theorem mem_compl : (a, b) ∈ Rᶜ ↔ (a, b) ∉ R := .rfl

@[simp]
theorem mem_top : (a, b) ∈ (⊤ : SquareRelations α) := trivial

@[simp]
theorem notMem_bot : (a, b) ∉ (⊥ : SquareRelations α) := id

@[simp]
theorem mem_one : (a, b) ∈ (1 : SquareRelations α) ↔ a = b := .rfl

@[simp]
theorem mem_mul : (a, c) ∈ R * S ↔ ∃ b, (a, b) ∈ R ∧ (b, c) ∈ S := .rfl

@[simp]
theorem mem_star : (a, b) ∈ star R ↔ (b, a) ∈ R := .rfl

theorem le_def : R ≤ S ↔ ∀ a b, (a, b) ∈ R → (a, b) ∈ S :=
  ⟨fun h _ _ hab => h hab, fun h ⟨a, b⟩ hab => h a b hab⟩

end SquareRelations

/-- A representation of a relation algebra is an injective morphism into a product of relations. -/
structure Representation (α : Type u) [RelationAlgebra α] (ι : Type v) (β : ι → Type w) where
  /-- A `RelationAlgebraHom` into a product of relations. -/
  hom : RelationAlgebraHom α (∀ i, SquareRelations (β i))
  injective : Function.Injective hom

/-- A relation algebra is representable if a `Representation` exists. -/
def Representable (α : Type u) [RelationAlgebra α] : Prop :=
  ∃ (ι : Type u) (β : ι → Type u), Nonempty (Representation α ι β)

/-- Pull a representation back along an injective homomorphism. -/
def Representation.comap {α : Type*} {α' : Type u} [RelationAlgebra α] [RelationAlgebra α']
    {ι : Type v} {β : ι → Type w} (r : Representation α' ι β) (f : RelationAlgebraHom α α')
    (hf : Function.Injective f) : Representation α ι β where
  hom := r.hom.comp f
  injective := r.injective.comp hf

/-- A relation algebra that embeds into a representable relation algebra is representable. -/
theorem Representable.of_injective {α α' : Type u} [RelationAlgebra α] [RelationAlgebra α']
    (f : RelationAlgebraHom α α') (hf : Function.Injective f) (h : Representable α') :
    Representable α :=
  let ⟨ι, β, ⟨r⟩⟩ := h
  ⟨ι, β, ⟨r.comap f hf⟩⟩

/-- A `Representation α ι β` in arbitrary universes can be contracted to the universe of `α`. -/
proof_wanted representable_univ {α : Type u} [RelationAlgebra α] {ι : Type v} {β : ι → Type w} :
    Representation α ι β → Representable α

end Cslib.RelationAlgebra

