/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Basic
public import Mathlib.ModelTheory.Semantics

/-!
# First-order language of relation algebras

This module defines the first-order language of relation algebras, along with instances of `Max`,
`Min`, `Compl`, `Mul`, `Star` and `One` on terms of this language. The development closely follows
Mathlib's treatment of the language of rings in `Mathlib.ModelTheory.Algebra.Ring.Basic`.

The signature is the one used in [Monk1964]: `(A, +, ·, -, ;, ˘, 1')`.

## Main definitions

* `FirstOrder.Language.relationAlgebra`: the language of relation algebras, with function symbols
  for `⊔`, `⊓`, `ᶜ`, `*`, `star` and `1`.
* `FirstOrder.RelationAlgebra.CompatibleRelationAlgebra`: a class stating that a type is a
  `Language.relationAlgebra.Structure`, and that this structure agrees with the operations already
  given on the type.
* `FirstOrder.RelationAlgebra.compatibleRelationAlgebraOfRelationAlgebra`: given a type with
  instances for each of the operations, construct a `CompatibleRelationAlgebra` instance.

## References

* [J. D. Monk, *On representable relation algebras*][Monk1964]

-/

@[expose] public section

variable {α : Type*}

namespace FirstOrder

open FirstOrder

/-- The type of function symbols of the language of relation algebras. -/
inductive relationAlgebraFunc : ℕ → Type
  | sup : relationAlgebraFunc 2
  | inf : relationAlgebraFunc 2
  | compl : relationAlgebraFunc 1
  | mul : relationAlgebraFunc 2
  | star : relationAlgebraFunc 1
  | one : relationAlgebraFunc 0
  deriving DecidableEq

/-- The language of relation algebras, with function symbols for `⊔`, `⊓`, `ᶜ`, `*`, `star`
and `1`. -/
def Language.relationAlgebra : Language :=
  { Functions := relationAlgebraFunc
    Relations := fun _ => Empty }
  deriving IsAlgebraic

namespace RelationAlgebra

open relationAlgebraFunc Language

/-- `relationAlgebraFunc.sup`, but with the defeq type `Language.relationAlgebra.Functions 2`. -/
abbrev supFunc : Language.relationAlgebra.Functions 2 := sup

/-- `relationAlgebraFunc.inf`, but with the defeq type `Language.relationAlgebra.Functions 2`. -/
abbrev infFunc : Language.relationAlgebra.Functions 2 := inf

/-- `relationAlgebraFunc.compl`, but with the defeq type
`Language.relationAlgebra.Functions 1`. -/
abbrev complFunc : Language.relationAlgebra.Functions 1 := compl

/-- `relationAlgebraFunc.mul`, but with the defeq type `Language.relationAlgebra.Functions 2`. -/
abbrev mulFunc : Language.relationAlgebra.Functions 2 := mul

/-- `relationAlgebraFunc.star`, but with the defeq type `Language.relationAlgebra.Functions 1`. -/
abbrev starFunc : Language.relationAlgebra.Functions 1 := star

/-- `relationAlgebraFunc.one`, but with the defeq type `Language.relationAlgebra.Functions 0`. -/
abbrev oneFunc : Language.relationAlgebra.Functions 0 := one

instance (α : Type*) : Max (Language.relationAlgebra.Term α) :=
  { max := supFunc.apply₂ }

theorem sup_def (α : Type*) (t₁ t₂ : Language.relationAlgebra.Term α) :
    t₁ ⊔ t₂ = supFunc.apply₂ t₁ t₂ := rfl

instance (α : Type*) : Min (Language.relationAlgebra.Term α) :=
  { min := infFunc.apply₂ }

theorem inf_def (α : Type*) (t₁ t₂ : Language.relationAlgebra.Term α) :
    t₁ ⊓ t₂ = infFunc.apply₂ t₁ t₂ := rfl

instance (α : Type*) : Compl (Language.relationAlgebra.Term α) :=
  { compl := complFunc.apply₁ }

theorem compl_def (α : Type*) (t : Language.relationAlgebra.Term α) :
    tᶜ = complFunc.apply₁ t := rfl

instance (α : Type*) : Mul (Language.relationAlgebra.Term α) :=
  { mul := mulFunc.apply₂ }

theorem mul_def (α : Type*) (t₁ t₂ : Language.relationAlgebra.Term α) :
    t₁ * t₂ = mulFunc.apply₂ t₁ t₂ := rfl

instance (α : Type*) : Star (Language.relationAlgebra.Term α) :=
  { star := starFunc.apply₁ }

theorem star_def (α : Type*) (t : Language.relationAlgebra.Term α) :
    Star.star t = starFunc.apply₁ t := rfl

instance (α : Type*) : One (Language.relationAlgebra.Term α) :=
  { one := Constants.term oneFunc }

theorem one_def (α : Type*) :
    (1 : Language.relationAlgebra.Term α) = Constants.term oneFunc := rfl

open Structure

/-- A type `A` is a `CompatibleRelationAlgebra` if it is a structure for the language of relation
algebras and this structure is the same as the structure already given on `A` by the classes
`Max`, `Min`, `Compl`, `Mul`, `Star` and `One`.

As for `FirstOrder.Ring.CompatibleRing`, this class does not extend the operation classes, so that
it can be used in combination with a `Cslib.RelationAlgebra` instance. -/
class CompatibleRelationAlgebra (A : Type*) [Max A] [Min A] [Compl A] [Mul A] [Star A] [One A]
    extends Language.relationAlgebra.Structure A where
  /-- The join of the structure is the one given by the `Max` instance. -/
  funMap_sup : ∀ x, funMap supFunc x = x 0 ⊔ x 1
  /-- The meet of the structure is the one given by the `Min` instance. -/
  funMap_inf : ∀ x, funMap infFunc x = x 0 ⊓ x 1
  /-- The complement of the structure is the one given by the `Compl` instance. -/
  funMap_compl : ∀ x, funMap complFunc x = (x 0)ᶜ
  /-- The composition of the structure is the one given by the `Mul` instance. -/
  funMap_mul : ∀ x, funMap mulFunc x = x 0 * x 1
  /-- The converse of the structure is the one given by the `Star` instance. -/
  funMap_star : ∀ x, funMap starFunc x = Star.star (x 0)
  /-- The identity of the structure is the one given by the `One` instance. -/
  funMap_one : ∀ x, funMap (oneFunc : Language.relationAlgebra.Constants) x = 1

open CompatibleRelationAlgebra

attribute [simp] funMap_sup funMap_inf funMap_compl funMap_mul funMap_star funMap_one

section

variable {A : Type*} [Max A] [Min A] [Compl A] [Mul A] [Star A] [One A]
  [CompatibleRelationAlgebra A]

@[simp]
theorem realize_sup (x y : relationAlgebra.Term α) (v : α → A) :
    Term.realize v (x ⊔ y) = Term.realize v x ⊔ Term.realize v y := by
  simp [sup_def, funMap_sup]

@[simp]
theorem realize_inf (x y : relationAlgebra.Term α) (v : α → A) :
    Term.realize v (x ⊓ y) = Term.realize v x ⊓ Term.realize v y := by
  simp [inf_def, funMap_inf]

@[simp]
theorem realize_compl (x : relationAlgebra.Term α) (v : α → A) :
    Term.realize v xᶜ = (Term.realize v x)ᶜ := by
  simp [compl_def, funMap_compl]

@[simp]
theorem realize_mul (x y : relationAlgebra.Term α) (v : α → A) :
    Term.realize v (x * y) = Term.realize v x * Term.realize v y := by
  simp [mul_def, funMap_mul]

@[simp]
theorem realize_star (x : relationAlgebra.Term α) (v : α → A) :
    Term.realize v (Star.star x) = Star.star (Term.realize v x) := by
  simp [star_def, funMap_star]

@[simp]
theorem realize_one (v : α → A) : Term.realize v (1 : relationAlgebra.Term α) = 1 := by
  simp [one_def, funMap_one, constantMap]

end

/-- Given a type `A` with instances for each of the relation algebra operations, make a
`Language.relationAlgebra.Structure A` instance, along with a proof that the operations given by
the structure are the same as those given by the instances.

As for `FirstOrder.Ring.compatibleRingOfRing`, this is a `def` and not an `instance`, because the
path from a relation algebra to a structure and back cannot be made to commute by definition. It
can be used by writing `let _ := compatibleRelationAlgebraOfRelationAlgebra A`. -/
@[instance_reducible]
def compatibleRelationAlgebraOfRelationAlgebra (A : Type*) [Max A] [Min A] [Compl A] [Mul A]
    [Star A] [One A] : CompatibleRelationAlgebra A :=
  { funMap := fun {n} f =>
      match n, f with
      | _, .sup => fun x => x 0 ⊔ x 1
      | _, .inf => fun x => x 0 ⊓ x 1
      | _, .compl => fun x => (x 0)ᶜ
      | _, .mul => fun x => x 0 * x 1
      | _, .star => fun x => Star.star (x 0)
      | _, .one => fun _ => 1
    funMap_sup := fun _ => rfl
    funMap_inf := fun _ => rfl
    funMap_compl := fun _ => rfl
    funMap_mul := fun _ => rfl
    funMap_star := fun _ => rfl
    funMap_one := fun _ => rfl }

variable (A : Type*) [Language.relationAlgebra.Structure A]

/-- A def to put a `Max` instance on a type with a `Language.relationAlgebra.Structure`
instance. To be used sparingly, as for `FirstOrder.Ring.addOfRingStructure`. -/
abbrev supOfRelationAlgebraStructure : Max A :=
  { max := fun x y => funMap supFunc ![x, y] }

/-- A def to put a `Min` instance on a type with a `Language.relationAlgebra.Structure`
instance. To be used sparingly, as for `FirstOrder.Ring.addOfRingStructure`. -/
abbrev infOfRelationAlgebraStructure : Min A :=
  { min := fun x y => funMap infFunc ![x, y] }

/-- A def to put a `Compl` instance on a type with a `Language.relationAlgebra.Structure`
instance. To be used sparingly, as for `FirstOrder.Ring.addOfRingStructure`. -/
abbrev complOfRelationAlgebraStructure : Compl A :=
  { compl := fun x => funMap complFunc ![x] }

/-- A def to put a `Mul` instance on a type with a `Language.relationAlgebra.Structure`
instance. To be used sparingly, as for `FirstOrder.Ring.addOfRingStructure`. -/
abbrev mulOfRelationAlgebraStructure : Mul A :=
  { mul := fun x y => funMap mulFunc ![x, y] }

/-- A def to put a `Star` instance on a type with a `Language.relationAlgebra.Structure`
instance. To be used sparingly, as for `FirstOrder.Ring.addOfRingStructure`. -/
abbrev starOfRelationAlgebraStructure : Star A :=
  { star := fun x => funMap starFunc ![x] }

/-- A def to put a `One` instance on a type with a `Language.relationAlgebra.Structure`
instance. To be used sparingly, as for `FirstOrder.Ring.addOfRingStructure`. -/
abbrev oneOfRelationAlgebraStructure : One A :=
  { one := funMap oneFunc ![] }

attribute [local instance] supOfRelationAlgebraStructure infOfRelationAlgebraStructure
  complOfRelationAlgebraStructure mulOfRelationAlgebraStructure starOfRelationAlgebraStructure
  oneOfRelationAlgebraStructure

/-- Given a type `A` with a `Language.relationAlgebra.Structure A`, the instances given by
`supOfRelationAlgebraStructure` etc. are compatible with the structure on `A`.

This definition is only to be used when `supOfRelationAlgebraStructure` etc. are local
instances. -/
abbrev compatibleRelationAlgebraOfRelationAlgebraStructure : CompatibleRelationAlgebra A :=
  { funMap_sup := by
      simp only [Fin.forall_fin_succ_pi, Fin.cons_zero, Fin.forall_fin_zero_pi]
      intros; rfl
    funMap_inf := by
      simp only [Fin.forall_fin_succ_pi, Fin.cons_zero, Fin.forall_fin_zero_pi]
      intros; rfl
    funMap_compl := by
      simp only [Fin.forall_fin_succ_pi, Fin.cons_zero, Fin.forall_fin_zero_pi]
      intros; rfl
    funMap_mul := by
      simp only [Fin.forall_fin_succ_pi, Fin.cons_zero, Fin.forall_fin_zero_pi]
      intros; rfl
    funMap_star := by
      simp only [Fin.forall_fin_succ_pi, Fin.cons_zero, Fin.forall_fin_zero_pi]
      intros; rfl
    funMap_one := by
      simp only [Fin.forall_fin_zero_pi]
      rfl }

end RelationAlgebra

end FirstOrder
