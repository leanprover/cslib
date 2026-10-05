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

The product of a family of relation algebras is a relation algebra with every operation taken
pointwise. Its Boolean algebra, monoid, and star structures are Mathlib's pointwise ones, so only
the three additional axioms need proofs.

Morphisms into the product correspond to families of morphisms into the factors; see
`RelationAlgebraHom.piEquiv`.
-/

@[expose] public section

namespace Cslib

/-- The product of a family of relation algebras, with every operation taken pointwise. -/
instance Pi.instRelationAlgebra {ι : Type*} {B : ι → Type*} [∀ i, RelationAlgebra (B i)] :
    RelationAlgebra (∀ i, B i) where
  __ := (inferInstance : BooleanAlgebra (∀ i, B i))
  __ := (inferInstance : Monoid (∀ i, B i))
  __ := (inferInstance : StarMul (∀ i, B i))
  sup_mul a b c := funext fun i => RelationAlgebra.sup_mul (a i) (b i) (c i)
  star_sup a b := funext fun i => RelationAlgebra.star_sup (a i) (b i)
  tarski a b i := RelationAlgebra.tarski (a i) (b i)

namespace RelationAlgebraHom

variable {A : Type*} [RelationAlgebra A] {ι : Type*} {B : ι → Type*}
  [∀ i, RelationAlgebra (B i)]

/-- A family of morphisms into the factors, combined into one morphism into the product. -/
def pi (f : ∀ i, RelationAlgebraHom A (B i)) : RelationAlgebraHom A (∀ i, B i) where
  toFun a i := f i a
  map_sup' a b := funext fun i => map_sup (f i) a b
  map_inf' a b := funext fun i => map_inf (f i) a b
  map_top' := funext fun i => map_top (f i)
  map_bot' := funext fun i => map_bot (f i)
  map_one' := funext fun i => map_one (f i)
  map_mul' a b := funext fun i => map_mul (f i) a b
  map_star' a := funext fun i => map_star (f i) a

@[simp]
theorem pi_apply (f : ∀ i, RelationAlgebraHom A (B i)) (a : A) (i : ι) : pi f a i = f i a :=
  rfl

variable (B) in
/-- Evaluation at an index, as a morphism out of the product. -/
def eval (i : ι) : RelationAlgebraHom (∀ i, B i) (B i) where
  toFun b := b i
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl
  map_top' := rfl
  map_bot' := rfl
  map_one' := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl

@[simp]
theorem eval_apply (i : ι) (b : ∀ i, B i) : eval B i b = b i :=
  rfl

variable (A B) in
/-- Morphisms into the product correspond to families of morphisms into the factors. -/
def piEquiv : (∀ i, RelationAlgebraHom A (B i)) ≃ RelationAlgebraHom A (∀ i, B i) where
  toFun := pi
  invFun f i := (eval B i).comp f
  left_inv _ := rfl
  right_inv _ := rfl

end RelationAlgebraHom

end Cslib

