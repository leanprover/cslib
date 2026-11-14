/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.Combinatorics.ProjectivePlane.BruckRyser
public import Cslib.Foundations.Logic.ModelTheory.ElementaryClass
public import Cslib.Foundations.RelationAlgebra.Lyndon.Plane
public import Cslib.Foundations.RelationAlgebra.Lyndon.Ultraproduct
public import Cslib.Foundations.RelationAlgebra.ModelTheory.Theory
public import Mathlib.Order.Filter.Ultrafilter.Basic

/-!
# Representable relation algebras are not finitely axiomatizable

This module proves the theorem of [Monk1964] that the class of representable relation algebras is
not finitely axiomatizable, answering a question of Tarski.

For each `k`, let `𝔄ₖ` be the Lyndon algebra with `2 * 3 ^ (2 * k + 1) + 2` atoms
(`Cslib.RelationAlgebra.Monk.Algebra`).

* No `𝔄ₖ` is representable: by Lyndon's theorem a representation would yield a projective plane
  of order `2 * 3 ^ (2 * k + 1)`, which is excluded by the Bruck–Ryser theorem.
* A nonprincipal ultraproduct of the `𝔄ₖ` embeds into a Lyndon algebra with infinitely many atoms,
  which is representable over a group, again by Lyndon.

By Łoś's theorem no first-order sentence can therefore hold in exactly the representable relation
algebras.

## Main statements

* `Cslib.RelationAlgebra.exists_product_groupRepresentable_not_representable`: Theorem 1 of
  [Monk1964], that there is an ultraproduct of non-representable integral relation algebras with
  trivial converse which is representable over a group.
* `Cslib.RelationAlgebra.exists_not_representable_realize`: every sentence that holds in all
  integral relation algebras with trivial converse that are representable over a group also holds
  in one that is not representable.
* `Cslib.RelationAlgebra.not_isFinitelyAxiomatizable_inter_representableClass` and
  `Cslib.RelationAlgebra.not_isFinitelyAxiomatizable_inter_groupRepresentableClass`: Theorem 2 of
  [Monk1964], for an arbitrary class containing all integral relation algebras with trivial
  converse (the algebras called "Lyndon algebras" in [Monk1964]).
* `Cslib.RelationAlgebra.not_isFinitelyAxiomatizable_of_theory`: Theorem 2 of [Monk1964] as
  stated there, for an elementary class.
* `Cslib.RelationAlgebra.not_isFinitelyAxiomatizable_representableClass` and
  `Cslib.RelationAlgebra.not_isFinitelyAxiomatizable_groupRepresentableClass`: neither the class
  of representable relation algebras nor the class of relation algebras representable over a group
  is finitely axiomatizable.

## Implementation notes

Classes of relation algebras are formalized as sets of bundled structures for the language of
relation algebras, as in `Cslib.Foundations.Logic.ModelTheory.ElementaryClass`. A structure belongs
to such a class when it is a model of the theory of relation algebras whose induced relation
algebra has the property in question (`Cslib.RelationAlgebra.structureClass`).

[Monk1964] takes an ultraproduct over the set of all `m ≥ 3` that are not the order of a
projective plane, with respect to an arbitrary nonprincipal ultrafilter. We use the explicit
subfamily `2 * 3 ^ (2 * k + 1)` given there and the hyperfilter on `ℕ`.

The hypothesis of Theorem 2 in [Monk1964] that the class is elementary is not needed, because the
ultraproduct in Theorem 1 is itself an integral relation algebra with trivial converse.

## References

* [J. D. Monk, *On representable relation algebras*][Monk1964]

-/

@[expose] public section

universe u v w

namespace Cslib.RelationAlgebra

open AtomStructure Configuration FirstOrder FirstOrder.Language FirstOrder.RelationAlgebra
open CategoryTheory (Bundled)

namespace Monk

/-- The atoms of the `k`-th algebra of Monk's sequence: a type with `2 * 3 ^ (2 * k + 1) + 2`
elements. -/
abbrev Atom (k : ℕ) : Type u := ULift.{u} (Fin (2 * 3 ^ (2 * k + 1) + 2))

theorem natCard_atom (k : ℕ) : Nat.card (Atom.{u} k) = 2 * 3 ^ (2 * k + 1) + 2 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_ulift, Fintype.card_fin]

theorem five_le_card_atom (k : ℕ) : 5 ≤ ENat.card (Atom.{u} k) := by
  have h3 : 3 ^ 1 ≤ 3 ^ (2 * k + 1) := Nat.pow_le_pow_right (by decide) (by omega)
  rw [ENat.card_eq_coe_fintype_card, Fintype.card_ulift, Fintype.card_fin]
  exact_mod_cast (by omega : 5 ≤ 2 * 3 ^ (2 * k + 1) + 2)

/-- The `k`-th algebra of Monk's sequence: the Lyndon algebra with `2 * 3 ^ (2 * k + 1) + 2`
atoms. -/
abbrev Algebra (k : ℕ) : Type u :=
  ComplexAlgebra (lyndon (⟨0⟩ : Atom.{u} k) (five_le_card_atom k))

theorem isIntegral (k : ℕ) : IsIntegral (Algebra.{u} k) :=
  ComplexAlgebra.isIntegral_lyndon _

/-- The algebras of Monk's sequence have no representations, by Lyndon's theorem and the
Bruck–Ryser theorem. -/
theorem isEmpty_representation (k : ℕ) {ι : Type v} {β : ι → Type w} :
    IsEmpty (Representation (Algebra.{u} k) ι β) := by
  refine ⟨fun ρ => ?_⟩
  obtain ⟨P, L, _, _, _, _, hord⟩ := exists_projectivePlane_order_of_representation _ _ ρ
  rw [natCard_atom] at hord
  exact ProjectivePlane.order_ne_two_mul_three_pow P L k (by omega)

theorem not_representable (k : ℕ) : ¬ Representable (Algebra.{u} k) :=
  fun ⟨_, _, ⟨ρ⟩⟩ => (isEmpty_representation k).false ρ

/-- The ultraproduct of the types of atoms of Monk's sequence is infinite. -/
theorem infinite_product_atom :
    Infinite ((Filter.hyperfilter ℕ : Filter ℕ).Product Atom.{u}) := by
  refine Ultraproduct.infinite_product _ _ fun n => ?_
  filter_upwards [Nat.hyperfilter_le_atTop (Filter.eventually_ge_atTop n)] with k hk
  rw [Cardinal.mk_fintype, Fintype.card_ulift, Fintype.card_fin]
  have hlt : 2 * k + 1 < 3 ^ (2 * k + 1) := Nat.lt_pow_self (by decide)
  exact_mod_cast (by omega : n ≤ 2 * 3 ^ (2 * k + 1) + 2)

/-- A nonprincipal ultraproduct of Monk's sequence is representable over a group. -/
theorem groupRepresentable_product :
    GroupRepresentable ((Filter.hyperfilter ℕ : Filter ℕ).Product Algebra.{u}) :=
  have := infinite_product_atom.{u}
  groupRepresentable_product_lyndon (fun _ => ⟨0⟩) five_le_card_atom (Filter.hyperfilter ℕ)

end Monk

/-- **Theorem 1** of [Monk1964]: there exists an ultraproduct of integral relation algebras with
trivial converse that is representable over a group, while none of its factors is
representable. -/
theorem exists_product_groupRepresentable_not_representable :
    ∃ (ι : Type) (U : Ultrafilter ι) (A : ι → Type u) (_ : ∀ i, RelationAlgebra (A i)),
      (∀ i, IsIntegral (A i) ∧ TrivialStar (A i)) ∧ (∀ i, ¬ Representable (A i)) ∧
      GroupRepresentable ((U : Filter ι).Product A) :=
  ⟨ℕ, Filter.hyperfilter ℕ, Monk.Algebra, inferInstance,
    fun k => ⟨Monk.isIntegral k, inferInstance⟩, Monk.not_representable,
    Monk.groupRepresentable_product⟩

/-- No first-order sentence separates the relation algebras representable over a group from the
non-representable ones, even among the integral relation algebras with trivial converse: a
sentence that holds in all algebras of the former kind holds in one of the latter kind. -/
theorem exists_not_representable_realize (σ : Language.relationAlgebra.Sentence)
    (hσ : ∀ (A : Type u) [RelationAlgebra A] [CompatibleRelationAlgebra A],
      IsIntegral A → TrivialStar A → GroupRepresentable A → A ⊨ σ) :
    ∃ (A : Type u) (_ : RelationAlgebra A) (_ : CompatibleRelationAlgebra A),
      IsIntegral A ∧ TrivialStar A ∧ ¬ Representable A ∧ A ⊨ σ := by
  let c (k : ℕ) : CompatibleRelationAlgebra (Monk.Algebra.{u} k) :=
    compatibleRelationAlgebraOfRelationAlgebra _
  have hprod := hσ ((Filter.hyperfilter ℕ : Filter ℕ).Product Monk.Algebra.{u})
    Monk.groupRepresentable_product.isIntegral inferInstance Monk.groupRepresentable_product
  obtain ⟨k, hk⟩ := ((Ultraproduct.sentence_realize σ).mp hprod).exists
  exact ⟨Monk.Algebra k, inferInstance, c k, Monk.isIntegral k, inferInstance,
    Monk.not_representable k, hk⟩

/-- The class of structures for the language of relation algebras that are relation algebras with
a given property. -/
def structureClass (p : ∀ (A : Type u) [RelationAlgebra A], Prop) :
    Set (Bundled.{u} Language.relationAlgebra.Structure) :=
  {M | ∃ h : (M : Type u) ⊨ Theory.relationAlgebra, @p M (@relationAlgebraOfModel M _ h)}

/-- The class of integral relation algebras with trivial converse. These are the algebras called
"Lyndon algebras" in [Monk1964], see `Cslib.RelationAlgebra.ofMonk`. -/
def monkClass : Set (Bundled.{u} Language.relationAlgebra.Structure) :=
  structureClass fun A _ => IsIntegral A ∧ TrivialStar A

/-- The class of representable relation algebras. -/
def representableClass : Set (Bundled.{u} Language.relationAlgebra.Structure) :=
  structureClass fun A _ => Representable A

/-- The class of relation algebras representable over a group. -/
def groupRepresentableClass : Set (Bundled.{u} Language.relationAlgebra.Structure) :=
  structureClass fun A _ => GroupRepresentable A

section

variable {A : Type u} [inst : RelationAlgebra A] [CompatibleRelationAlgebra A]

theorem mem_monkClass_iff :
    (Bundled.of A : Bundled Language.relationAlgebra.Structure) ∈ monkClass ↔
      IsIntegral A ∧ TrivialStar A :=
  ⟨fun ⟨_, h⟩ => ⟨@RelationAlgebraHom.isIntegral_of_injective A A inst (relationAlgebraOfModel A)
      (toModelHom A) (toModelHom_injective A) h.1,
    @RelationAlgebraHom.trivialStar_of_injective A A inst (relationAlgebraOfModel A)
      (toModelHom A) (toModelHom_injective A) h.2⟩,
  fun h => ⟨inferInstanceAs (A ⊨ Theory.relationAlgebra),
    @RelationAlgebraHom.isIntegral_of_injective A A (relationAlgebraOfModel A) inst
      (ofModelHom A) (ofModelHom_injective A) h.1,
    @RelationAlgebraHom.trivialStar_of_injective A A (relationAlgebraOfModel A) inst
      (ofModelHom A) (ofModelHom_injective A) h.2⟩⟩

theorem mem_representableClass_iff :
    (Bundled.of A : Bundled Language.relationAlgebra.Structure) ∈ representableClass ↔
      Representable A :=
  ⟨fun ⟨_, h⟩ => @Representable.of_injective A A inst (relationAlgebraOfModel A) (toModelHom A)
      (toModelHom_injective A) h,
  fun h => ⟨inferInstanceAs (A ⊨ Theory.relationAlgebra),
    @Representable.of_injective A A (relationAlgebraOfModel A) inst (ofModelHom A)
      (ofModelHom_injective A) h⟩⟩

theorem mem_groupRepresentableClass_iff :
    (Bundled.of A : Bundled Language.relationAlgebra.Structure) ∈ groupRepresentableClass ↔
      GroupRepresentable A :=
  ⟨fun ⟨_, h⟩ => @GroupRepresentable.of_injective A A inst (relationAlgebraOfModel A)
      (toModelHom A) (toModelHom_injective A) h,
  fun h => ⟨inferInstanceAs (A ⊨ Theory.relationAlgebra),
    @GroupRepresentable.of_injective A A (relationAlgebraOfModel A) inst (ofModelHom A)
      (ofModelHom_injective A) h⟩⟩

end

theorem groupRepresentableClass_subset_representableClass :
    groupRepresentableClass.{u} ⊆ representableClass :=
  fun M ⟨h, hg⟩ =>
    ⟨h, @GroupRepresentable.representable M (@relationAlgebraOfModel M _ h) hg⟩

section

variable {K : Set (Bundled.{u} Language.relationAlgebra.Structure)}

/-- **Theorem 2** of [Monk1964], for an arbitrary class: if a class of structures contains all
integral relation algebras with trivial converse, then the class of its members that are relation
algebras representable over a group is not finitely axiomatizable. -/
theorem not_isFinitelyAxiomatizable_inter_groupRepresentableClass (hK : monkClass ⊆ K) :
    ¬ IsFinitelyAxiomatizable (K ∩ groupRepresentableClass) := by
  let c (k : ℕ) : CompatibleRelationAlgebra (Monk.Algebra.{u} k) :=
    compatibleRelationAlgebraOfRelationAlgebra _
  refine not_isFinitelyAxiomatizable_of_product (Filter.hyperfilter ℕ) Monk.Algebra.{u}
    (fun k hk => ?_) ⟨hK ?_, ?_⟩
  · exact Monk.not_representable k
      (mem_representableClass_iff.mp (groupRepresentableClass_subset_representableClass hk.2))
  · exact mem_monkClass_iff.mpr ⟨Monk.groupRepresentable_product.isIntegral, inferInstance⟩
  · exact mem_groupRepresentableClass_iff.mpr Monk.groupRepresentable_product

/-- **Theorem 2** of [Monk1964], for an arbitrary class: if a class of structures contains all
integral relation algebras with trivial converse, then the class of its members that are
representable relation algebras is not finitely axiomatizable. -/
theorem not_isFinitelyAxiomatizable_inter_representableClass (hK : monkClass ⊆ K) :
    ¬ IsFinitelyAxiomatizable (K ∩ representableClass) := by
  let c (k : ℕ) : CompatibleRelationAlgebra (Monk.Algebra.{u} k) :=
    compatibleRelationAlgebraOfRelationAlgebra _
  refine not_isFinitelyAxiomatizable_of_product (Filter.hyperfilter ℕ) Monk.Algebra.{u}
    (fun k hk => ?_) ⟨hK ?_, ?_⟩
  · exact Monk.not_representable k (mem_representableClass_iff.mp hk.2)
  · exact mem_monkClass_iff.mpr ⟨Monk.groupRepresentable_product.isIntegral, inferInstance⟩
  · exact mem_representableClass_iff.mpr Monk.groupRepresentable_product.representable

end

/-- **Theorem 2** of [Monk1964]: if `K` is an elementary class containing all integral relation
algebras with trivial converse, then neither the class of all representable relation algebras in
`K` nor the class of all algebras in `K` representable over a group is finitely axiomatizable. -/
theorem not_isFinitelyAxiomatizable_of_theory (T : Language.relationAlgebra.Theory)
    (hT : ∀ M ∈ monkClass.{u}, (M : Type u) ⊨ T) :
    ¬ IsFinitelyAxiomatizable
        ({M : Bundled.{u} Language.relationAlgebra.Structure | (M : Type u) ⊨ T} ∩
          representableClass) ∧
      ¬ IsFinitelyAxiomatizable
        ({M : Bundled.{u} Language.relationAlgebra.Structure | (M : Type u) ⊨ T} ∩
          groupRepresentableClass) :=
  ⟨not_isFinitelyAxiomatizable_inter_representableClass hT,
    not_isFinitelyAxiomatizable_inter_groupRepresentableClass hT⟩

/-- The class of representable relation algebras is not finitely axiomatizable. -/
theorem not_isFinitelyAxiomatizable_representableClass :
    ¬ IsFinitelyAxiomatizable representableClass.{u} := by
  have h := not_isFinitelyAxiomatizable_inter_representableClass (Set.subset_univ monkClass.{u})
  rwa [Set.univ_inter] at h

/-- The class of relation algebras representable over a group is not finitely axiomatizable. -/
theorem not_isFinitelyAxiomatizable_groupRepresentableClass :
    ¬ IsFinitelyAxiomatizable groupRepresentableClass.{u} := by
  have h := not_isFinitelyAxiomatizable_inter_groupRepresentableClass
    (Set.subset_univ monkClass.{u})
  rwa [Set.univ_inter] at h

end Cslib.RelationAlgebra
