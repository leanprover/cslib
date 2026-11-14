/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.ModelTheory.Basic
public import Mathlib.Data.Set.Finite.Range

/-!
# The first-order theory of relation algebras

This module defines the first-order theory of relation algebras as a theory over the language
of relation algebras, following Mathlib's treatment of the theory of fields in
`Mathlib.ModelTheory.Algebra.Field.Basic`. The axioms are Tarski's ten equations, as in
`Cslib.RelationAlgebra.ofTarski`, together with an equation defining meet from join and
complement. In particular the theory is finite.

## Main definitions

* `FirstOrder.Language.Theory.relationAlgebra`: the theory of relation algebras.
* `FirstOrder.RelationAlgebra.relationAlgebraOfModel`: a model of the theory of relation algebras
  is a relation algebra.
* `FirstOrder.RelationAlgebra.compatibleRelationAlgebraOfModel`: the operations given by
  `relationAlgebraOfModel` are compatible with the structure.

-/

@[expose] public section

variable {A : Type*}

namespace FirstOrder

namespace RelationAlgebra

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
