/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Pi
public import Cslib.Foundations.Data.SetRel

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

/-- The relation algebra of all binary relations on a type `α`. This is scoped so that other
instances, such as those under `Pointwise`, can be used elsewhere. -/
scoped instance (α : Type u) : RelationAlgebra (SetRel α α) where
  one := SetRel.id
  mul := SetRel.comp
  mul_assoc := SetRel.comp_assoc
  one_mul := SetRel.id_comp
  mul_one := SetRel.comp_id
  star := SetRel.inv
  star_involutive _ := SetRel.inv_inv
  star_mul := SetRel.inv_comp
  sup_mul a b c := by
    ext ⟨x, z⟩
    exact (exists_congr fun y => or_and_right).trans exists_or
  star_sup _ _ := rfl
  tarski a b := by
    rintro ⟨x, z⟩ ⟨y, hxy, hyz⟩ hxz
    exact hyz ⟨x, hxy, hxz⟩

variable {α β : Type u} {R S : SetRel α α} {a b c : α}

theorem _root_.SetRel.mul_eq_comp : R * S = R.comp S := rfl

theorem _root_.SetRel.one_eq_id : (1 : SetRel α α) = SetRel.id := rfl

theorem _root_.SetRel.star_eq_inv : star R = R.inv := rfl

@[simp]
theorem _root_.SetRel.mem_mul : (a, c) ∈ R * S ↔ ∃ b, (a, b) ∈ R ∧ (b, c) ∈ S := .rfl

@[simp]
theorem _root_.SetRel.mem_one : (a, b) ∈ (1 : SetRel α α) ↔ a = b := .rfl

@[simp]
theorem _root_.SetRel.mem_star : (a, b) ∈ star R ↔ (b, a) ∈ R := .rfl

@[simps!]
def _root_.RelationAlgebraEquiv.ofEquivSetRel (e : α ≃ β) :
    RelationAlgebraEquiv (SetRel α α) (SetRel β β) where
  __ := SetRel.mapEquiv e e
  map_rel_iff' := SetRel.map_subset_map_iff e.injective e.injective
  map_mul' _ _ := SetRel.map_comp_of_injective e.injective
  map_star' _ := SetRel.inv_map.symm

/-- A representation of a relation algebra is an injective morphism into a product of relations. -/
structure Representation (α : Type u) [RelationAlgebra α] (ι : Type v) (β : ι → Type w) where
  /-- A `RelationAlgebraHom` into a product of relations. -/
  hom : RelationAlgebraHom α (∀ i, SetRel (β i) (β i))
  injective : Function.Injective hom

/-- A relation algebra is representable if a `Representation` exists. -/
def Representable (α : Type u) [RelationAlgebra α] : Prop :=
  ∃ (ι : Type u) (β : ι → Type u), Nonempty (Representation α ι β)

/-- A `Representation α ι β` in arbitrary universes can be contracted to the universe of `α`. -/
proof_wanted representable_univ {α : Type u} [RelationAlgebra α] {ι : Type v} {β : ι → Type w} :
    Representation α ι β → Representable α

variable {α β : Type*} [RelationAlgebra α]

structure Representation' (α β : Type*) [RelationAlgebra α] extends
    LatticeHom α (SetRel β β), StarMonoidHom α (SetRel β β) where
  injective' : Function.Injective toFun
  map_bot' : toFun ⊥ = ⊥
  -- map_sdiff' (a b : α) : toFun (a \ b) = toFun a \ toFun b

instance instFunLikeRepresentation' : FunLike (Representation' α β) α (SetRel β β) where
  coe R := R.toFun
  coe_injective S R := by cases S; cases R; simp

lemma Representation'.injective (R : Representation' α β) : Function.Injective R := R.injective'

instance : LatticeHomClass (Representation' α β) α (SetRel β β) where
  map_sup R := R.map_sup'
  map_inf R := R.map_inf'

protected lemma Representation'.mono (R : Representation' α β) :
  Monotone R := OrderHomClass.mono R

-- lemma Representation'.map_sdiff (R : Representation' α β) {a b : α} :
--     R (a \ b) = R a \ R b := R.map_sdiff' a b

instance : MonoidHomClass (Representation' α β) α (SetRel β β) where
  map_mul R := R.map_mul'
  map_one R := R.map_one'

instance : StarHomClass (Representation' α β) α (SetRel β β) where
  map_star R := R.map_star'

instance : BotHomClass (Representation' α β) α (SetRel β β) where
  map_bot R := R.map_bot'
--     rw [← sdiff_self (a := 1), ← sdiff_self (a := (1 : SetRel β β)), R.map_sdiff, map_one R]

@[simps]
def prodRepresentation' (ι : Type v) (α : ι → Type w) :
    Representation' (∀ i, SetRel (α i) (α i)) (Σ i, α i) where
  toFun := SetRel.piToSigma
  injective' := SetRel.piToSigma_inj
  map_sup' _ _ := SetRel.piToSigma_union
  map_inf' _ _ := SetRel.piToSigma_inter
  map_one' := SetRel.piToSigma_id
  map_mul' _ _ := SetRel.piToSigma_comp
  map_star' _ := SetRel.piToSigma_inv
  map_bot' := SetRel.piToSigma_bot
  -- map_sdiff' _ _ := SetRel.piToSigma_sdiff

def Representation'.compHom {α β γ : Type*} [RelationAlgebra α] [RelationAlgebra β]
    (f : RelationAlgebraHom α β) (hf : Function.Injective f) (R : Representation' β γ) :
    Representation' α γ where
  toFun a := R.toFun (f a)
  __ := R.toStarMonoidHom.comp f.toStarMonoidHom
  __ := R.toLatticeHom.comp f.toBoundedLatticeHom.toLatticeHom
  injective' := R.injective.comp hf
  map_bot' := by simp [R.map_bot']
  -- map_sdiff' a b := by simp_rw [_root_.map_sdiff', R.map_sdiff']

def Representation'.ofRepresentation (α : Type u) [RelationAlgebra α] (ι : Type v) (β : ι → Type w)
    (R : Representation α ι β) : Representation' α (Σ i, β i) :=
  (prodRepresentation' ι β).compHom R.hom R.injective

end Cslib.RelationAlgebra
