/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.Combinatorics.ProjectivePlane.BruckRyser
public import Cslib.Foundations.RelationAlgebra.Lyndon
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
* `Cslib.RelationAlgebra.exists_not_representable_model`: every finite theory that holds in all
  integral relation algebras with trivial converse that are representable over a group also holds
  in one that is not representable.
* `Cslib.RelationAlgebra.not_exists_finite_theory_iff_and`: Theorem 2 of [Monk1964] in a general
  form, for an arbitrary class containing all integral relation algebras with trivial converse
  (the algebras called "Lyndon algebras" in [Monk1964]) and an arbitrary property between
  representability over a group and representability.
* `Cslib.RelationAlgebra.not_exists_finite_theory_iff_model_and_representable`: Theorem 2 of
  [Monk1964] as stated there, for an elementary class.
* `Cslib.RelationAlgebra.not_exists_finite_theory_iff_representable` and
  `Cslib.RelationAlgebra.not_exists_finite_theory_iff_groupRepresentable`: neither the class of
  representable relation algebras nor the class of relation algebras representable over a group
  is finitely axiomatizable.

## Implementation notes

Following the conventions of `Mathlib.ModelTheory.Algebra.Ring.Basic`, a class of relation algebras
is a predicate on types carrying a `RelationAlgebra` instance, and it is *finitely axiomatizable*
when there is a finite theory `T` in the language of relation algebras such that a relation
algebra `A` with a compatible structure is a model of `T` exactly when it belongs to the class.
This is finite axiomatizability relative to the class of all relation algebras. Since relation
algebras are themselves defined by finitely many equations, it is equivalent to the existence of a
finite theory whose models, among all structures for the language, are exactly the members of the
class.

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

/-- No finite first-order theory separates the relation algebras representable over a group from
the non-representable ones, even among the integral relation algebras with trivial converse: a
finite theory that holds in all algebras of the former kind holds in one of the latter kind. -/
theorem exists_not_representable_model (T : Language.relationAlgebra.Theory) (hT : T.Finite)
    (h : ∀ (A : Type u) [RelationAlgebra A] [CompatibleRelationAlgebra A],
      IsIntegral A → TrivialStar A → GroupRepresentable A → A ⊨ T) :
    ∃ (A : Type u) (_ : RelationAlgebra A) (_ : CompatibleRelationAlgebra A),
      IsIntegral A ∧ TrivialStar A ∧ ¬ Representable A ∧ A ⊨ T := by
  let c (k : ℕ) : CompatibleRelationAlgebra (Monk.Algebra.{u} k) :=
    compatibleRelationAlgebraOfRelationAlgebra _
  have hprod := h ((Filter.hyperfilter ℕ : Filter ℕ).Product Monk.Algebra.{u})
    Monk.groupRepresentable_product.isIntegral inferInstance Monk.groupRepresentable_product
  have hall : ∀ φ ∈ T, ∀ᶠ k in (Filter.hyperfilter ℕ : Filter ℕ), Monk.Algebra.{u} k ⊨ φ :=
    fun φ hφ => (Ultraproduct.sentence_realize φ).mp ((Theory.model_iff T).mp hprod φ hφ)
  obtain ⟨k, hk⟩ := ((Filter.eventually_all_finite hT).mpr hall).exists
  exact ⟨Monk.Algebra k, inferInstance, c k, Monk.isIntegral k, inferInstance,
    Monk.not_representable k, (Theory.model_iff T).mpr hk⟩

/-- **Theorem 2** of [Monk1964], in a general form. Let `R` be a property of relation algebras
that is implied by representability over a group and implies representability, and let `K` be a
class of relation algebras containing all integral relation algebras with trivial converse. Then
the class of algebras in `K` satisfying `R` is not finitely axiomatizable.

The class `K` is allowed to depend on the first-order structure, so that it can be taken to be the
class of models of a theory. -/
theorem not_exists_finite_theory_iff_and
    (R : ∀ (A : Type u) [RelationAlgebra A], Prop)
    (hGR : ∀ (A : Type u) [RelationAlgebra A], GroupRepresentable A → R A)
    (hR : ∀ (A : Type u) [RelationAlgebra A], R A → Representable A)
    (K : ∀ (A : Type u) [RelationAlgebra A] [CompatibleRelationAlgebra A], Prop)
    (hK : ∀ (A : Type u) [RelationAlgebra A] [CompatibleRelationAlgebra A],
      IsIntegral A → TrivialStar A → K A) :
    ¬ ∃ T : Language.relationAlgebra.Theory, T.Finite ∧
      ∀ (A : Type u) [RelationAlgebra A] [CompatibleRelationAlgebra A], A ⊨ T ↔ K A ∧ R A := by
  rintro ⟨T, hfin, hT⟩
  obtain ⟨A, _, _, -, -, hrep, hA⟩ := exists_not_representable_model T hfin
    fun A _ _ hint hstar hg => (hT A).mpr ⟨hK A hint hstar, hGR A hg⟩
  exact hrep (hR A ((hT A).mp hA).2)

/-- **Theorem 2** of [Monk1964]: if `K` is an elementary class containing all integral relation
algebras with trivial converse, given as the class of models of a theory `T'`, then neither the
class of all representable relation algebras in `K` nor the class of all algebras in `K`
representable over a group is finitely axiomatizable. -/
theorem not_exists_finite_theory_iff_model_and_representable
    (T' : Language.relationAlgebra.Theory)
    (hT' : ∀ (A : Type u) [RelationAlgebra A] [CompatibleRelationAlgebra A],
      IsIntegral A → TrivialStar A → A ⊨ T') :
    (¬ ∃ T : Language.relationAlgebra.Theory, T.Finite ∧
      ∀ (A : Type u) [RelationAlgebra A] [CompatibleRelationAlgebra A],
        A ⊨ T ↔ A ⊨ T' ∧ Representable A) ∧
    ¬ ∃ T : Language.relationAlgebra.Theory, T.Finite ∧
      ∀ (A : Type u) [RelationAlgebra A] [CompatibleRelationAlgebra A],
        A ⊨ T ↔ A ⊨ T' ∧ GroupRepresentable A :=
  ⟨not_exists_finite_theory_iff_and (fun A _ => Representable A)
      (fun _ _ h => h.representable) (fun _ _ h => h) (fun A _ _ => A ⊨ T') hT',
    not_exists_finite_theory_iff_and (fun A _ => GroupRepresentable A)
      (fun _ _ h => h) (fun _ _ h => h.representable) (fun A _ _ => A ⊨ T') hT'⟩

/-- The class of representable relation algebras is not finitely axiomatizable. -/
theorem not_exists_finite_theory_iff_representable :
    ¬ ∃ T : Language.relationAlgebra.Theory, T.Finite ∧
      ∀ (A : Type u) [RelationAlgebra A] [CompatibleRelationAlgebra A],
        A ⊨ T ↔ Representable A := by
  have h := not_exists_finite_theory_iff_and.{u} (fun A _ => Representable A)
    (fun _ _ h => h.representable) (fun _ _ h => h) (fun _ _ _ => True) fun _ _ _ _ _ => trivial
  simpa only [true_and] using h

/-- The class of relation algebras representable over a group is not finitely axiomatizable. -/
theorem not_exists_finite_theory_iff_groupRepresentable :
    ¬ ∃ T : Language.relationAlgebra.Theory, T.Finite ∧
      ∀ (A : Type u) [RelationAlgebra A] [CompatibleRelationAlgebra A],
        A ⊨ T ↔ GroupRepresentable A := by
  have h := not_exists_finite_theory_iff_and.{u} (fun A _ => GroupRepresentable A)
    (fun _ _ h => h) (fun _ _ h => h.representable) (fun _ _ _ => True)
    fun _ _ _ _ _ => trivial
  simpa only [true_and] using h

end Cslib.RelationAlgebra
