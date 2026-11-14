/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Init
public import Mathlib.Algebra.Star.Basic
public import Mathlib.ModelTheory.Basic

/-!
# First-order language of relation algebras

This module defines the first-order language of relation algebras, following Mathlib's treatment of
the language of rings in `Mathlib.ModelTheory.Algebra.Ring.Basic`.

The signature is the one of Tarski's axiomatization, as in `Cslib.RelationAlgebra.ofTarski`: join,
complement, composition, converse and identity. Meet is definable from join and complement, so
this language has the same expressive power as the signature `(A, +, ·, -, ;, ˘, 1')` used in
[Monk1964].

## Main definitions

* `FirstOrder.Language.relationAlgebra`: the language of relation algebras, with function symbols
  for `⊔`, `ᶜ`, `*`, `star` and `1`.
* `FirstOrder.RelationAlgebra.CompatibleRelationAlgebra`: a class stating that a type is a
  `Language.relationAlgebra.Structure`, and that this structure agrees with the operations already
  given on the type.
* `FirstOrder.RelationAlgebra.compatibleRelationAlgebraOfRelationAlgebra`: given a type with
  instances for each of the operations, construct a `CompatibleRelationAlgebra` instance.

## References

* [J. D. Monk, *On representable relation algebras*][Monk1964]

-/

@[expose] public section

namespace FirstOrder

/-- The type of function symbols of the language of relation algebras. -/
inductive relationAlgebraFunc : ℕ → Type
  | sup : relationAlgebraFunc 2
  | compl : relationAlgebraFunc 1
  | mul : relationAlgebraFunc 2
  | star : relationAlgebraFunc 1
  | one : relationAlgebraFunc 0
  deriving DecidableEq

/-- The language of relation algebras, with function symbols for `⊔`, `ᶜ`, `*`, `star` and `1`. -/
def Language.relationAlgebra : Language :=
  { Functions := relationAlgebraFunc
    Relations := fun _ => Empty }
  deriving IsAlgebraic

namespace RelationAlgebra

open relationAlgebraFunc Language Structure

/-- `relationAlgebraFunc.sup`, but with the defeq type `Language.relationAlgebra.Functions 2`. -/
abbrev supFunc : Language.relationAlgebra.Functions 2 := sup

/-- `relationAlgebraFunc.compl`, but with the defeq type
`Language.relationAlgebra.Functions 1`. -/
abbrev complFunc : Language.relationAlgebra.Functions 1 := compl

/-- `relationAlgebraFunc.mul`, but with the defeq type `Language.relationAlgebra.Functions 2`. -/
abbrev mulFunc : Language.relationAlgebra.Functions 2 := mul

/-- `relationAlgebraFunc.star`, but with the defeq type `Language.relationAlgebra.Functions 1`. -/
abbrev starFunc : Language.relationAlgebra.Functions 1 := star

/-- `relationAlgebraFunc.one`, but with the defeq type `Language.relationAlgebra.Functions 0`. -/
abbrev oneFunc : Language.relationAlgebra.Functions 0 := one

/-- A type `A` is a `CompatibleRelationAlgebra` if it is a structure for the language of relation
algebras and this structure is the same as the structure already given on `A` by the classes
`Max`, `Compl`, `Mul`, `Star` and `One`.

As for `FirstOrder.Ring.CompatibleRing`, this class does not extend the operation classes, so that
it can be used in combination with a `Cslib.RelationAlgebra` instance. -/
class CompatibleRelationAlgebra (A : Type*) [Max A] [Compl A] [Mul A] [Star A] [One A]
    extends Language.relationAlgebra.Structure A where
  /-- The join of the structure is the one given by the `Max` instance. -/
  funMap_sup : ∀ x, funMap supFunc x = x 0 ⊔ x 1
  /-- The complement of the structure is the one given by the `Compl` instance. -/
  funMap_compl : ∀ x, funMap complFunc x = (x 0)ᶜ
  /-- The composition of the structure is the one given by the `Mul` instance. -/
  funMap_mul : ∀ x, funMap mulFunc x = x 0 * x 1
  /-- The converse of the structure is the one given by the `Star` instance. -/
  funMap_star : ∀ x, funMap starFunc x = Star.star (x 0)
  /-- The identity of the structure is the one given by the `One` instance. -/
  funMap_one : ∀ x, funMap (oneFunc : Language.relationAlgebra.Constants) x = 1

open CompatibleRelationAlgebra

attribute [simp] funMap_sup funMap_compl funMap_mul funMap_star funMap_one

/-- Given a type `A` with instances for each of the relation algebra operations, make a
`Language.relationAlgebra.Structure A` instance, along with a proof that the operations given by
the structure are the same as those given by the instances.

As for `FirstOrder.Ring.compatibleRingOfRing`, this is a `def` and not an `instance`. It can be
used by writing `let _ := compatibleRelationAlgebraOfRelationAlgebra A`. -/
@[instance_reducible]
def compatibleRelationAlgebraOfRelationAlgebra (A : Type*) [Max A] [Compl A] [Mul A] [Star A]
    [One A] : CompatibleRelationAlgebra A :=
  { funMap := fun {n} f =>
      match n, f with
      | _, .sup => fun x => x 0 ⊔ x 1
      | _, .compl => fun x => (x 0)ᶜ
      | _, .mul => fun x => x 0 * x 1
      | _, .star => fun x => Star.star (x 0)
      | _, .one => fun _ => 1
    funMap_sup := fun _ => rfl
    funMap_compl := fun _ => rfl
    funMap_mul := fun _ => rfl
    funMap_star := fun _ => rfl
    funMap_one := fun _ => rfl }

end RelationAlgebra

end FirstOrder
