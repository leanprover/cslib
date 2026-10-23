/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Hom
public import Mathlib.Algebra.Star.Pi

/-!
# Products of relation algebras

This module defines the relation algebra structure over products. This is a key component of
the representation of a relation algebra.

-/

@[expose] public section

namespace Cslib

instance Pi.instRelationAlgebra {ι : Type*} {β : ι → Type*} [∀ i, RelationAlgebra (β i)] :
    RelationAlgebra (∀ i, β i) where
  sup_mul a b c := funext fun i => RelationAlgebra.sup_mul (a i) (b i) (c i)
  star_sup a b := funext fun i => RelationAlgebra.star_sup (a i) (b i)
  tarski a b i := RelationAlgebra.tarski (a i) (b i)

namespace RelationAlgebraHom

variable {α : Type*} [RelationAlgebra α] {ι : Type*} {β : ι → Type*} [∀ i, RelationAlgebra (β i)]

/-- The product of `RelationAlgebraHom`s is a `RelationAlgebraHom` into a product. -/
def pi (f : ∀ i, RelationAlgebraHom α (β i)) : RelationAlgebraHom α (∀ i, β i) where
  toFun a i := f i a
  __ := MonoidHom.pi fun i => (f i).toMonoidHom
  map_sup' a b := funext fun i => map_sup (f i) a b
  map_inf' a b := funext fun i => map_inf (f i) a b
  map_top' := funext fun i => map_top (f i)
  map_bot' := funext fun i => map_bot (f i)
  map_star' a := funext fun i => map_star (f i) a

@[simp]
theorem pi_apply (f : ∀ i, RelationAlgebraHom α (β i)) (a : α) (i : ι) : pi f a i = f i a :=
  rfl

variable (β) in
/-- The `RelationAlgebraHom` into a single fiber. -/
def eval (i : ι) : RelationAlgebraHom (∀ i, β i) (β i) where
  toFun b := b i
  __ := Pi.evalLatticeHom i
  __ := Pi.evalMonoidHom β i
  map_top' := rfl
  map_bot' := rfl
  map_star' _ := rfl

@[simp]
theorem eval_apply (i : ι) (b : ∀ i, β i) : eval β i b = b i :=
  rfl

variable (α β) in
/-- The equivalence between products of `RelationAlgebraHom` and the `RelationAlgebraHom` into a
  product that is given by composition of `eval`. -/
def piEquiv : (∀ i, RelationAlgebraHom α (β i)) ≃ RelationAlgebraHom α (∀ i, β i) where
  toFun := pi
  invFun f i := (eval β i).comp f
  left_inv _ := rfl
  right_inv _ := rfl

end RelationAlgebraHom

end Cslib
