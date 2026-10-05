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
  sup_mul a b c := by
    apply Set.ext
    rintro ⟨x, z⟩
    change (∃ y, (a (x, y) ∨ b (x, y)) ∧ c (y, z)) ↔
      (∃ y, a (x, y) ∧ c (y, z)) ∨ (∃ y, b (x, y) ∧ c (y, z))
    aesop
  star_sup _ _ := rfl
  tarski a b := by
    rintro ⟨x, z⟩ ⟨y, hxy, hyz⟩ hxz
    exact hyz ⟨x, hxy, hxz⟩

end SquareRelations

/-- A representation as an injective homomorphism into a product of full square relation algebras.
Individual component homomorphisms need not be injective. -/
structure Representation (A : Type u) [RelationAlgebra A]
    (ι : Type v) (Base : ι → Type w) where
  /-- The homomorphism into the product of full square relation algebras. -/
  hom : RelationAlgebraHom A (∀ i, SquareRelations (Base i))
  /-- The homomorphism distinguishes all algebra elements. -/
  injective : Function.Injective hom

/-- A relation algebra is representable when it embeds into a product of full square relation
algebras. The index and base types are taken in the universe of the algebra; no finiteness
assumption is imposed on them. -/
def Representable (A : Type u) [RelationAlgebra A] : Prop :=
  ∃ (ι : Type u) (Base : ι → Type u), Nonempty (Representation A ι Base)

namespace Representation

variable {A : Type u} {Base : Type v} [RelationAlgebra A]

private noncomputable def witness (f : RelationAlgebraHom A (SquareRelations Base))
    (fallback : Base) (a b : A) (x y : Base) : Base := by
  classical
  exact if h : f (a * b) (x, y) then
    Classical.choose (show ∃ z, f a (x, z) ∧ f b (z, y) from by
      rw [map_mul] at h
      exact h)
  else fallback

private theorem witness_spec (f : RelationAlgebraHom A (SquareRelations Base)) (fallback : Base)
    (a b : A) (x y : Base) (h : f (a * b) (x, y)) :
    f a (x, witness f fallback a b x y) ∧ f b (witness f fallback a b x y, y) := by
  classical
  simp only [witness, dite_eq_left h]
  exact Classical.choose_spec (show ∃ z, f a (x, z) ∧ f b (z, y) from by
    rw [map_mul] at h
    exact h)

private inductive Point (A : Type u) : Type u where
  | left
  | right
  | compose (a b : A) (x y : Point A)

private noncomputable def pointEval (f : RelationAlgebraHom A (SquareRelations Base)) (x y : Base) :
    Point A → Base
  | .left => x
  | .right => y
  | .compose a b p q => witness f x a b (pointEval f x y p) (pointEval f x y q)

private noncomputable def pointSetoid (f : RelationAlgebraHom A (SquareRelations Base))
    (x y : Base) : Setoid (Point A) := Setoid.ker (pointEval f x y)

private abbrev SmallBase (f : RelationAlgebraHom A (SquareRelations Base)) (x y : Base) :=
  Quotient (pointSetoid f x y)

private noncomputable def quotientEval (f : RelationAlgebraHom A (SquareRelations Base))
    (x y : Base) : SmallBase f x y → Base :=
  Quotient.lift (pointEval f x y) (fun _ _ h => h)

private theorem quotientEval_injective (f : RelationAlgebraHom A (SquareRelations Base))
    (x y : Base) : Function.Injective (quotientEval f x y) := by
  intro p q
  induction p using Quotient.inductionOn with | h p =>
    induction q using Quotient.inductionOn with | h q =>
      intro h
      exact Quotient.sound (s := pointSetoid f x y) h

private noncomputable def smallHom (f : RelationAlgebraHom A (SquareRelations Base)) (x y : Base) :
    RelationAlgebraHom A (SquareRelations (SmallBase f x y)) where
  toFun a := fun p => f a (quotientEval f x y p.1, quotientEval f x y p.2)
  map_sup' a b := by
    funext p
    exact congrFun (f.map_sup' a b) _
  map_inf' a b := by
    funext p
    exact congrFun (f.map_inf' a b) _
  map_top' := by
    funext p
    exact congrFun (map_top f) _
  map_bot' := by
    funext p
    exact congrFun (map_bot f) _
  map_one' := by
    funext p
    apply propext
    change f 1 (quotientEval f x y p.1, quotientEval f x y p.2) ↔ p.1 = p.2
    rw [map_one]
    exact (quotientEval_injective f x y).eq_iff
  map_star' a := by
    funext p
    exact congrFun (map_star f a) _
  map_mul' a b := by
    funext p
    obtain ⟨p, q⟩ := p
    induction p using Quotient.inductionOn with | h p =>
      induction q using Quotient.inductionOn with | h q =>
        apply propext
        change f (a * b) (pointEval f x y p, pointEval f x y q) ↔
          ∃ z : SmallBase f x y,
            f a (pointEval f x y p, quotientEval f x y z) ∧
            f b (quotientEval f x y z, pointEval f x y q)
        constructor
        · intro h
          exact ⟨Quotient.mk _ (.compose a b p q), witness_spec f x a b _ _ h⟩
        · rintro ⟨z, hz, hz'⟩
          rw [map_mul]
          exact ⟨quotientEval f x y z, hz, hz'⟩


/-- Any representation can be reduced to bases and an index type in the source universe.

For each unequal pair of algebra elements, choose a component and an edge that distinguish
it. Closing the two endpoints under composition witnesses uses finite trees labelled by
algebra elements. Quotienting these trees by equality of their evaluations gives a base in
the source universe and preserves all relational operations. -/
theorem representable {ι : Type v} {Family : ι → Type w}
    (r : Representation A ι Family) : Representable A := by
  classical
  let component := (RelationAlgebraHom.piEquiv A (fun i => SquareRelations (Family i))).symm r.hom
  let Pair := {p : A × A // p.1 ≠ p.2}
  have separates (p : Pair) :
      ∃ i, ∃ x y, component i p.1.1 (x, y) ≠ component i p.1.2 (x, y) := by
    by_contra h
    push Not at h
    apply p.2
    apply r.injective
    funext i
    funext q
    exact h i q.1 q.2
  choose index x y distinct using separates
  refine ⟨Pair, fun p => SmallBase (component (index p)) (x p) (y p),
    ⟨⟨RelationAlgebraHom.pi (fun p => smallHom (component (index p)) (x p) (y p)), ?_⟩⟩⟩
  intro a b h
  by_contra hab
  let p : Pair := ⟨(a, b), hab⟩
  have heq := congrFun h p
  have hedge := congrFun heq (Quotient.mk _ Point.left, Quotient.mk _ Point.right)
  exact distinct p hedge

end Representation


/-- An injective homomorphism into a full square relation algebra gives a representation. -/
theorem representable_of_injective_hom {A Base : Type u} [RelationAlgebra A]
    (f : RelationAlgebraHom A (SquareRelations Base)) (hf : Function.Injective f) :
    Representable A := by
  refine ⟨PUnit.{u + 1}, fun _ => Base, ⟨⟨RelationAlgebraHom.pi (fun _ => f), ?_⟩⟩⟩
  intro a b h
  exact hf (congrFun h PUnit.unit)

/-- Every full square relation algebra is representable. -/
theorem representable_squareRelations (Base : Type u) : Representable (SquareRelations Base) := by
  exact representable_of_injective_hom (RelationAlgebraHom.id _) Function.injective_id

/-- An injective homomorphism into a representable algebra gives a representation. -/
theorem representable_of_injective {A B : Type u} [RelationAlgebra A] [RelationAlgebra B]
    (f : RelationAlgebraHom A B) (hf : Function.Injective f) (hB : Representable B) :
    Representable A := by
  obtain ⟨ι, Base, ⟨r⟩⟩ := hB
  refine ⟨ι, Base, ⟨⟨r.hom.comp f, ?_⟩⟩⟩
  exact r.injective.comp hf

/-- Representability is invariant under relation-algebra isomorphism. -/
theorem representable_iff_of_equiv {A : Type u} {B : Type v}
    [RelationAlgebra A] [RelationAlgebra B] (e : RelationAlgebraEquiv A B) :
    Representable A ↔ Representable B := by
  constructor
  · rintro ⟨ι, Base, ⟨r⟩⟩
    apply Representation.representable
    refine ⟨r.hom.comp e.symm.toHom, ?_⟩
    exact r.injective.comp (EquivLike.injective e.symm)
  · rintro ⟨ι, Base, ⟨r⟩⟩
    apply Representation.representable
    refine ⟨r.hom.comp e.toHom, ?_⟩
    exact r.injective.comp (EquivLike.injective e)

end Cslib.RelationAlgebra
