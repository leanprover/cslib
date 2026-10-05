/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Basic
public import Mathlib.Algebra.Star.MonoidHom
public import Mathlib.Order.Hom.BoundedLattice

/-!
# Morphisms and isomorphisms of relation algebras

Relation algebra morphisms preserve the bounded lattice structure, composition, identity,
and converse. Bounded lattice morphisms between Boolean algebras automatically preserve
complements, so no additional complement-preservation field is needed.

Relation algebra isomorphisms combine an order isomorphism with a star multiplicative
equivalence. These already preserve the Boolean operations and multiplicative identity.
-/

@[expose] public section

namespace Cslib

/-- A morphism of relation algebras. -/
structure RelationAlgebraHom (A B : Type*) [RelationAlgebra A] [RelationAlgebra B]
    extends BoundedLatticeHom A B, StarMonoidHom A B

/-- An isomorphism of relation algebras. -/
structure RelationAlgebraEquiv (A B : Type*) [RelationAlgebra A] [RelationAlgebra B]
    extends toOrderIso : OrderIso A B, StarMulEquiv A B

/-- The underlying homomorphism preserving composition, identity, and converse. -/
add_decl_doc RelationAlgebraHom.toStarMonoidHom

/-- The underlying equivalence preserving composition and converse. -/
add_decl_doc RelationAlgebraEquiv.toStarMulEquiv

namespace RelationAlgebraHom

variable {A B C : Type*} [RelationAlgebra A] [RelationAlgebra B] [RelationAlgebra C]

instance : FunLike (RelationAlgebraHom A B) A B where
  coe f := f.toFun
  coe_injective f g h := by cases f; cases g; simp_all

instance : BoundedLatticeHomClass (RelationAlgebraHom A B) A B where
  map_sup f := f.map_sup'
  map_inf f := f.map_inf'
  map_top f := f.map_top'
  map_bot f := f.map_bot'

instance : MonoidHomClass (RelationAlgebraHom A B) A B where
  map_mul f := f.map_mul'
  map_one f := f.map_one'

instance : StarHomClass (RelationAlgebraHom A B) A B where
  map_star f := f.map_star'

@[ext]
theorem ext {f g : RelationAlgebraHom A B} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext _ _ h

/-- The identity relation algebra morphism. -/
protected def id (A : Type*) [RelationAlgebra A] : RelationAlgebraHom A A :=
  { BoundedLatticeHom.id A, StarMonoidHom.id A with }

/-- Composition of relation algebra morphisms, with `f.comp g` applying `g` first. -/
def comp (f : RelationAlgebraHom B C) (g : RelationAlgebraHom A B) : RelationAlgebraHom A C :=
  { f.toBoundedLatticeHom.comp g.toBoundedLatticeHom,
    f.toStarMonoidHom.comp g.toStarMonoidHom with }

@[simp]
theorem id_apply (a : A) : RelationAlgebraHom.id A a = a := rfl

@[simp]
theorem comp_apply (f : RelationAlgebraHom B C) (g : RelationAlgebraHom A B) (a : A) :
    f.comp g a = f (g a) := rfl

end RelationAlgebraHom

namespace RelationAlgebraEquiv

variable {A B C : Type*} [RelationAlgebra A] [RelationAlgebra B] [RelationAlgebra C]

instance : EquivLike (RelationAlgebraEquiv A B) A B where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h := by cases f; cases g; simp_all

instance : OrderIsoClass (RelationAlgebraEquiv A B) A B where
  map_le_map_iff f := f.map_rel_iff'

instance : MulEquivClass (RelationAlgebraEquiv A B) A B where
  map_mul f := f.map_mul'

instance : StarHomClass (RelationAlgebraEquiv A B) A B where
  map_star f := f.map_star'

@[ext]
theorem ext {f g : RelationAlgebraEquiv A B} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext _ _ h

/-- The identity relation algebra isomorphism. -/
protected def refl (A : Type*) [RelationAlgebra A] : RelationAlgebraEquiv A A :=
  { OrderIso.refl A, StarMulEquiv.refl A with }

/-- The inverse of a relation algebra isomorphism. -/
def symm (f : RelationAlgebraEquiv A B) : RelationAlgebraEquiv B A :=
  { f.toOrderIso.symm, f.toStarMulEquiv.symm with }

/-- Composition of relation algebra isomorphisms, with `f.trans g` applying `f` first. -/
def trans (f : RelationAlgebraEquiv A B) (g : RelationAlgebraEquiv B C) :
    RelationAlgebraEquiv A C :=
  { f.toOrderIso.trans g.toOrderIso, f.toStarMulEquiv.trans g.toStarMulEquiv with }

/-- Forget the inverse of a relation algebra isomorphism. -/
def toHom (f : RelationAlgebraEquiv A B) : RelationAlgebraHom A B :=
  { (f.toOrderIso : BoundedLatticeHom A B), f.toStarMulEquiv.toStarMonoidHom with }

@[simp]
theorem refl_apply (a : A) : RelationAlgebraEquiv.refl A a = a := rfl

@[simp]
theorem trans_apply (f : RelationAlgebraEquiv A B) (g : RelationAlgebraEquiv B C) (a : A) :
    f.trans g a = g (f a) := rfl

@[simp]
theorem toHom_apply (f : RelationAlgebraEquiv A B) (a : A) : f.toHom a = f a := rfl

@[simp]
theorem symm_apply_apply (f : RelationAlgebraEquiv A B) (a : A) : f.symm (f a) = a :=
  f.left_inv a

@[simp]
theorem apply_symm_apply (f : RelationAlgebraEquiv A B) (b : B) : f (f.symm b) = b :=
  f.right_inv b

end RelationAlgebraEquiv

end Cslib
