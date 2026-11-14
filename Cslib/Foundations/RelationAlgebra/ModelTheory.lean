/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Basic
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.ModelTheory.Semantics

/-!
# First-order language and theory of relation algebras

This module defines the first-order language of relation algebras, along with instances of `Max`,
`Min`, `Compl`, `Mul`, `Star` and `One` on terms of this language, and the first-order theory of
relation algebras as a theory over this language. The development closely follows Mathlib's
treatment of the language of rings in `Mathlib.ModelTheory.Algebra.Ring.Basic` and of the theory
of fields in `Mathlib.ModelTheory.Algebra.Field.Basic`.

The signature is the one used in [Monk1964]: `(A, +, ·, -, ;, ˘, 1')`. The axioms are Tarski's ten
equations, as in `Cslib.RelationAlgebra.ofTarski`, together with an equation defining meet from
join and complement. In particular the theory is finite.

## Main definitions

* `FirstOrder.Language.relationAlgebra`: the language of relation algebras, with function symbols
  for `⊔`, `⊓`, `ᶜ`, `*`, `star` and `1`.
* `FirstOrder.RelationAlgebra.CompatibleRelationAlgebra`: a class stating that a type is a
  `Language.relationAlgebra.Structure`, and that this structure agrees with the operations already
  given on the type.
* `FirstOrder.RelationAlgebra.compatibleRelationAlgebraOfRelationAlgebra`: given a type with
  instances for each of the operations, construct a `CompatibleRelationAlgebra` instance.
* `FirstOrder.Language.Theory.relationAlgebra`: the theory of relation algebras.
* `FirstOrder.RelationAlgebra.relationAlgebraOfModel`: a model of the theory of relation algebras
  is a relation algebra.
* `FirstOrder.RelationAlgebra.compatibleRelationAlgebraOfModel`: the operations given by
  `relationAlgebraOfModel` are compatible with the structure.

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

namespace RelationAlgebra

variable {A : Type*}

open Language Structure BoundedFormula

/-- An indexing type to name each of the relation algebra axioms. The theory of relation algebras
is defined as the range of a function `RelationAlgebraAxiom → Language.relationAlgebra.Sentence`. -/
inductive RelationAlgebraAxiom : Type
  | supComm : RelationAlgebraAxiom
  | supAssoc : RelationAlgebraAxiom
  | huntington : RelationAlgebraAxiom
  | infDef : RelationAlgebraAxiom
  | mulAssoc : RelationAlgebraAxiom
  | mulOne : RelationAlgebraAxiom
  | starStar : RelationAlgebraAxiom
  | starMul : RelationAlgebraAxiom
  | supMul : RelationAlgebraAxiom
  | starSup : RelationAlgebraAxiom
  | tarski : RelationAlgebraAxiom

instance : Finite RelationAlgebraAxiom :=
  Finite.of_surjective
    (![.supComm, .supAssoc, .huntington, .infDef, .mulAssoc, .mulOne, .starStar, .starMul,
      .supMul, .starSup, .tarski] : Fin 11 → RelationAlgebraAxiom)
    (fun ax => by
      cases ax
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩, ⟨5, rfl⟩, ⟨6, rfl⟩, ⟨7, rfl⟩,
        ⟨8, rfl⟩, ⟨9, rfl⟩, ⟨10, rfl⟩])

/-- The first-order sentence corresponding to each relation algebra axiom. -/
@[simp]
def RelationAlgebraAxiom.toSentence : RelationAlgebraAxiom → Language.relationAlgebra.Sentence
  | .supComm => ∀' ∀' ((&0 ⊔ &1) =' (&1 ⊔ &0))
  | .supAssoc => ∀' ∀' ∀' (((&0 ⊔ &1) ⊔ &2) =' (&0 ⊔ (&1 ⊔ &2)))
  | .huntington => ∀' ∀' ((((&0)ᶜ ⊔ &1)ᶜ ⊔ ((&0)ᶜ ⊔ (&1)ᶜ)ᶜ) =' &0)
  | .infDef => ∀' ∀' ((&0 ⊓ &1) =' ((&0)ᶜ ⊔ (&1)ᶜ)ᶜ)
  | .mulAssoc => ∀' ∀' ∀' (((&0 * &1) * &2) =' (&0 * (&1 * &2)))
  | .mulOne => ∀' ((&0 * (1 : Language.relationAlgebra.Term _)) =' &0)
  | .starStar => ∀' (star (star &0) =' &0)
  | .starMul => ∀' ∀' (star (&0 * &1) =' (star &1 * star &0))
  | .supMul => ∀' ∀' ∀' (((&0 ⊔ &1) * &2) =' ((&0 * &2) ⊔ (&1 * &2)))
  | .starSup => ∀' ∀' (star (&0 ⊔ &1) =' (star &0 ⊔ star &1))
  | .tarski => ∀' ∀' (((star &0 * (&0 * &1)ᶜ) ⊔ (&1)ᶜ) =' (&1)ᶜ)

/-- The proposition corresponding to each relation algebra axiom. -/
@[simp]
def RelationAlgebraAxiom.toProp (A : Type*) [Max A] [Min A] [Compl A] [Mul A] [Star A] [One A] :
    RelationAlgebraAxiom → Prop
  | .supComm => ∀ a b : A, a ⊔ b = b ⊔ a
  | .supAssoc => ∀ a b c : A, (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c)
  | .huntington => ∀ a b : A, (aᶜ ⊔ b)ᶜ ⊔ (aᶜ ⊔ bᶜ)ᶜ = a
  | .infDef => ∀ a b : A, a ⊓ b = (aᶜ ⊔ bᶜ)ᶜ
  | .mulAssoc => ∀ a b c : A, (a * b) * c = a * (b * c)
  | .mulOne => ∀ a : A, a * 1 = a
  | .starStar => ∀ a : A, star (star a) = a
  | .starMul => ∀ a b : A, star (a * b) = star b * star a
  | .supMul => ∀ a b c : A, (a ⊔ b) * c = a * c ⊔ b * c
  | .starSup => ∀ a b : A, star (a ⊔ b) = star a ⊔ star b
  | .tarski => ∀ a b : A, star a * (a * b)ᶜ ⊔ bᶜ = bᶜ

/-- The first-order theory of relation algebras, as a theory over the language of relation
algebras. -/
def _root_.FirstOrder.Language.Theory.relationAlgebra : Language.relationAlgebra.Theory :=
  Set.range RelationAlgebraAxiom.toSentence

/-- The theory of relation algebras is finite. -/
theorem _root_.FirstOrder.Language.Theory.finite_relationAlgebra :
    Theory.relationAlgebra.Finite :=
  Set.finite_range _

theorem RelationAlgebraAxiom.realize_toSentence_iff_toProp {A : Type*} [Max A] [Min A] [Compl A]
    [Mul A] [Star A] [One A] [CompatibleRelationAlgebra A] (ax : RelationAlgebraAxiom) :
    (A ⊨ (ax.toSentence : Sentence Language.relationAlgebra)) ↔ ax.toProp A := by
  cases ax <;>
  simp [Sentence.Realize, Formula.Realize, Fin.snoc]

theorem RelationAlgebraAxiom.toProp_of_model {A : Type*} [Max A] [Min A] [Compl A] [Mul A]
    [Star A] [One A] [CompatibleRelationAlgebra A] [Theory.relationAlgebra.Model A]
    (ax : RelationAlgebraAxiom) : ax.toProp A :=
  (RelationAlgebraAxiom.realize_toSentence_iff_toProp ax).1
    (Theory.realize_sentence_of_mem Theory.relationAlgebra (Set.mem_range_self ax))

open RelationAlgebraAxiom

/-- A model for the theory of relation algebras is a relation algebra. To be introduced locally on
types that do not already have instances for the relation algebra operations.

When this is used, it is almost always useful to also add locally the instance
`compatibleRelationAlgebraOfModel` afterwards. -/
abbrev relationAlgebraOfModel (A : Type*) [Language.relationAlgebra.Structure A]
    [Theory.relationAlgebra.Model A] : Cslib.RelationAlgebra A :=
  letI := supOfRelationAlgebraStructure A
  letI := infOfRelationAlgebraStructure A
  letI := complOfRelationAlgebraStructure A
  letI := mulOfRelationAlgebraStructure A
  letI := starOfRelationAlgebraStructure A
  letI := oneOfRelationAlgebraStructure A
  letI := compatibleRelationAlgebraOfRelationAlgebraStructure A
  Cslib.RelationAlgebra.ofTarski
    supComm.toProp_of_model
    supAssoc.toProp_of_model
    huntington.toProp_of_model
    mulAssoc.toProp_of_model
    mulOne.toProp_of_model
    starStar.toProp_of_model
    starMul.toProp_of_model
    supMul.toProp_of_model
    starSup.toProp_of_model
    tarski.toProp_of_model

section

attribute [local instance] relationAlgebraOfModel

/-- The instances given by `relationAlgebraOfModel` are compatible with the
`Language.relationAlgebra.Structure` instance on `A`. This instance is to be used on models for
the language of relation algebras that do not already have the operations on the type.

Always add `relationAlgebraOfModel` as a local instance first before using this instance.

Unlike `FirstOrder.Field.compatibleRingOfModelField`, the meet of `relationAlgebraOfModel` is not
the one of the structure by definition, but by the axiom defining meet. -/
abbrev compatibleRelationAlgebraOfModel (A : Type*) [Language.relationAlgebra.Structure A]
    [Theory.relationAlgebra.Model A] : CompatibleRelationAlgebra A :=
  { funMap_sup := by
      simp only [Fin.forall_fin_succ_pi, Fin.cons_zero, Fin.forall_fin_zero_pi]
      intros; rfl
    funMap_inf := by
      let _ := supOfRelationAlgebraStructure A
      let _ := infOfRelationAlgebraStructure A
      let _ := complOfRelationAlgebraStructure A
      let _ := mulOfRelationAlgebraStructure A
      let _ := starOfRelationAlgebraStructure A
      let _ := oneOfRelationAlgebraStructure A
      let _ := compatibleRelationAlgebraOfRelationAlgebraStructure A
      simp only [Fin.forall_fin_succ_pi, Fin.cons_zero, Fin.forall_fin_zero_pi]
      exact infDef.toProp_of_model (A := A)
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

end

instance [Cslib.RelationAlgebra A] [CompatibleRelationAlgebra A] :
    Theory.relationAlgebra.Model A :=
  { realize_of_mem := by
      simp only [Theory.relationAlgebra, Set.mem_range, exists_imp]
      rintro φ a rfl
      rw [a.realize_toSentence_iff_toProp (A := A)]
      cases a with
      | supComm => exact sup_comm
      | supAssoc => exact sup_assoc
      | huntington => exact fun a b => by simp [← inf_sup_left]
      | infDef => exact fun a b => by rw [compl_sup, compl_compl, compl_compl]
      | mulAssoc => exact mul_assoc
      | mulOne => exact mul_one
      | starStar => exact star_star
      | starMul => exact star_mul
      | supMul => exact Cslib.RelationAlgebra.sup_mul
      | starSup => exact Cslib.RelationAlgebra.star_sup
      | tarski => exact fun a b => sup_eq_right.mpr (Cslib.RelationAlgebra.tarski a b) }

end RelationAlgebra

end FirstOrder
