/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Hom
public import Mathlib.Basic.Rel

/-!
# Representable relation algebras

The full square relation algebra on a type consists of its binary relations. A representation of
an arbitrary relation algebra is an injective homomorphism into a product of full square relation
algebras. Equivalently, its relations have an equivalence relation as their Boolean unit, obtained
by taking the disjoint union of the squares. The bases need not be finite or inhabited.

## References

* I. Hodkinson, *A construction of cylindric and polyadic algebras from atomic relation algebras*,
  Algebra Universalis 68 (2012), 257–285, Definition 2.2.
  <https://www.doc.ic.ac.uk/~imh/papers/red.pdf>
-/

@[expose] public section

universe u v w

namespace Cslib.RelationAlgebra

/-- Binary relations with relational composition, identity, and converse. This type synonym keeps
these operations separate from pointwise operations on sets. -/
def SquareRelations (Base : Type u) : Type u := SetRel Base Base

namespace SquareRelations

instance (Base : Type u) : BooleanAlgebra (SquareRelations Base) :=
  inferInstanceAs (BooleanAlgebra (SetRel Base Base))

instance (Base : Type u) : Monoid (SquareRelations Base) where
  one := SetRel.id
  mul := SetRel.comp
  mul_assoc := SetRel.comp_assoc
  one_mul := SetRel.id_comp
  mul_one := SetRel.comp_id

instance (Base : Type u) : StarMul (SquareRelations Base) where
  star := SetRel.inv
  star_involutive := fun _ => SetRel.inv_inv
  star_mul := SetRel.inv_comp

instance (Base : Type u) : RelationAlgebra (SquareRelations Base) where
  sup_mul := by sorry
  star_sup := by sorry
  tarski := by sorry

end SquareRelations

/-- A representation by a family of full square relation algebras. Injectivity is required for
the whole family; individual component homomorphisms need not be injective. -/
structure Representation (A : Type u) [RelationAlgebra A]
    (ι : Type v) (Base : ι → Type w) where
  /-- The component homomorphisms. -/
  hom : ∀ i, RelationAlgebraHom A (SquareRelations (Base i))
  /-- The component homomorphisms jointly distinguish all algebra elements. -/
  injective : Function.Injective (fun a i => hom i a)

/-- A relation algebra is representable when it embeds into a product of full square relation
algebras. The index and base types are taken in the universe of the algebra; no finiteness
assumption is imposed on them. -/
def Representable (A : Type u) [RelationAlgebra A] : Prop :=
  ∃ (ι : Type u) (Base : ι → Type u), Nonempty (Representation A ι Base)

/-- Every full square relation algebra is representable. -/
theorem representable_squareRelations (Base : Type u) : Representable (SquareRelations Base) := by
  sorry

/-- Representability is invariant under relation-algebra isomorphism. -/
theorem representable_iff_of_equiv {A : Type u} {B : Type v}
    [RelationAlgebra A] [RelationAlgebra B] (e : RelationAlgebraEquiv A B) :
    Representable A ↔ Representable B := by
  sorry

end Cslib.RelationAlgebra
