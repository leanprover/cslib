/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Pi
public import Cslib.Foundations.RelationAlgebra.Simple
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

`Representation` uses an embedding into a product of full square relation algebras.
`ProperRepresentation` instead uses an embedding into relations whose Boolean top is an
equivalence relation, with complement taken relative to that relation. Its image is the concrete
family, and the embedding gives an isomorphism onto that family.
The `proof_wanted` declarations state the equivalence of these formulations and the existence
of a representation with a single square factor for simple representable relation algebras.

## References

* [R. Maddux, *Relation Algebras*][Maddux2006]

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

/-- The algebra of all binary relations on a nonempty set is simple, as in the examples
following the Simplicity Theorem in [Givant2017, p. 389][Givant2017]. -/
theorem simple (α : Type*) [Nonempty α] : Simple (SquareRelations α) := by
  refine ⟨inferInstanceAs (Nontrivial (SetRel α α)), fun a ha => ?_⟩
  obtain ⟨⟨x, y⟩, hxy⟩ := Set.nonempty_iff_ne_empty.mpr ha
  apply top_unique
  rintro ⟨w, z⟩ _
  exact ⟨y, ⟨x, Set.mem_univ _, hxy⟩, Set.mem_univ _⟩

/-- A full square relation algebra is simple exactly when its base is nonempty. -/
theorem simple_iff_nonempty (α : Type*) : Simple (SquareRelations α) ↔ Nonempty α := by
  constructor
  · intro h
    by_contra hn
    have : IsEmpty α := not_nonempty_iff.mp hn
    have := h.nontrivial
    exact bot_ne_top (α := SquareRelations α) (Set.ext fun ⟨x, _⟩ => isEmptyElim x)
  · intro h
    have := h
    exact simple α

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

structure ProperRepresentation (α : Type u) [RelationAlgebra α] (β : Type v) where
  setoid : Setoid β
  embedding : α ↪ SetRel β β
  map_bot : embedding ⊥ = ∅
  map_top : embedding ⊤ = {p | setoid.r p.1 p.2}
  map_one : embedding 1 = SetRel.id
  map_sup : ∀ a b, embedding (a ⊔ b) = embedding a ∪ embedding b
  map_inf : ∀ a b, embedding (a ⊓ b) = embedding a ∩ embedding b
  map_compl : ∀ a, embedding aᶜ = {p | setoid.r p.1 p.2} \ embedding a
  map_mul : ∀ a b, embedding (a * b) = SetRel.comp (embedding a) (embedding b)
  map_star : ∀ a, embedding (star a) = SetRel.inv (embedding a)

proof_wanted representable_iff_concrete (α : Type u) [RelationAlgebra α] :
    Representable α ↔ ∃ β : Type u, Nonempty (ProperRepresentation α β)

proof_wanted representable_iff_single_factor
    (α : Type u) [RelationAlgebra α] (h : Simple α) :
    Representable α ↔ ∃ β : Type u, Nonempty (Representation α Unit (fun _ => β))

proof_wanted representable_iff_concrete_universal
    (α : Type u) [RelationAlgebra α] (h : Simple α) :
    Representable α ↔ ∃ (β : Type u) (R : ProperRepresentation α β), ∀ x y, R.setoid.r x y

end Cslib.RelationAlgebra

