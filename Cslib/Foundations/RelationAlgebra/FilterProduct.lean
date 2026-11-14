/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.ModelTheory.Basic
public import Cslib.Foundations.RelationAlgebra.Pi
public import Mathlib.ModelTheory.Ultraproducts

/-!
# Reduced products and ultraproducts of relation algebras

For a filter `l` on `ι` and a family `A : ι → Type*` of relation algebras, the reduced product
`l.Product A` (the quotient of the product by the relation of being equal on a set in `l`) is a
relation algebra, because relation algebras are defined by equations. When `l` is an ultrafilter
this is the ultraproduct, and the relation algebra structure is compatible with the first-order
structure used for Łoś's theorem in `Mathlib.ModelTheory.Ultraproducts`.

## Main definitions

* `Filter.Product.instRelationAlgebra`: the relation algebra structure on a reduced product.
* `Filter.Product.mkHom`: the quotient map from the product, as a `RelationAlgebraHom`.
* `Filter.Product.instCompatibleRelationAlgebra`: the relation algebra structure on an
  ultraproduct agrees with its first-order structure.

-/

@[expose] public section

namespace Filter.Product

open Cslib FirstOrder FirstOrder.Language FirstOrder.RelationAlgebra

section

variable {ι : Type*} {α : ι → Type*} {l : Filter ι}

variable (l) in
/-- The class of a family of elements in a reduced product. -/
def mk (f : ∀ i, α i) : l.Product α := Quotient.mk _ f

/-- The quotient map onto a reduced product is surjective. -/
theorem mk_surjective : Function.Surjective (mk l : (∀ i, α i) → l.Product α) :=
  Quotient.mk_surjective

/-- Every element of a reduced product is the class of some family. -/
@[elab_as_elim]
theorem induction_on {p : l.Product α → Prop} (x : l.Product α) (h : ∀ f, p (mk l f)) : p x :=
  Quotient.inductionOn x h

theorem mk_eq_mk {f g : ∀ i, α i} : mk l f = mk l g ↔ ∀ᶠ i in l, f i = g i :=
  Quotient.eq

end

/-- An ultraproduct of types whose cardinalities are eventually above every natural number is
infinite. -/
theorem _root_.FirstOrder.Language.Ultraproduct.infinite_product {ι : Type*} (U : Ultrafilter ι)
    (M : ι → Type*) [∀ a, Nonempty (M a)]
    (h : ∀ n : ℕ, ∀ᶠ a in (U : Filter ι), (n : Cardinal) ≤ Cardinal.mk (M a)) :
    Infinite ((U : Filter ι).Product M) := by
  let _ : ∀ a, Language.empty.Structure (M a) := fun _ => Language.emptyStructure
  rw [← Language.empty.model_infiniteTheory_iff]
  refine ⟨fun φ hφ => ?_⟩
  obtain ⟨n, rfl⟩ := hφ
  rw [Ultraproduct.sentence_realize]
  exact (h n).mono fun a ha => (Sentence.realize_cardGe _ n).2 ha

variable {ι : Type*} {A : ι → Type*} [∀ i, RelationAlgebra (A i)] {l : Filter ι}

section

/-- The join of a reduced product. Use the `RelationAlgebra` instance instead. -/
abbrev sup : Max (l.Product A) where
  max := Quotient.map₂ (· ⊔ ·) fun _ _ h₁ _ _ h₂ => h₁.mp (h₂.mono fun i h₂ h₁ => by
    simp only [Pi.sup_apply, h₁, h₂])

/-- The complement of a reduced product. Use the `RelationAlgebra` instance instead. -/
abbrev compl : Compl (l.Product A) where
  compl := Quotient.map (·ᶜ) fun _ _ h => h.mono fun i h => by simp only [Pi.compl_apply, h]

/-- The composition of a reduced product. Use the `RelationAlgebra` instance instead. -/
abbrev mul : Mul (l.Product A) where
  mul := Quotient.map₂ (· * ·) fun _ _ h₁ _ _ h₂ => h₁.mp (h₂.mono fun i h₂ h₁ => by
    simp only [Pi.mul_apply, h₁, h₂])

/-- The converse of a reduced product. Use the `RelationAlgebra` instance instead. -/
abbrev star : Star (l.Product A) where
  star := Quotient.map Star.star fun _ _ h => h.mono fun i h => by
    simp only [Pi.star_apply, h]

/-- The identity of a reduced product. Use the `RelationAlgebra` instance instead. -/
abbrev one : One (l.Product A) where
  one := mk l 1

attribute [local instance] sup compl mul star one in
/-- The reduced product of a family of relation algebras is a relation algebra. -/
instance instRelationAlgebra : RelationAlgebra (l.Product A) :=
  Function.Surjective.relationAlgebra (mk l) mk_surjective
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) rfl (fun _ => rfl)

end

variable (A l) in
/-- The quotient map from the product of a family of relation algebras to its reduced product. -/
def mkHom : RelationAlgebraHom (∀ i, A i) (l.Product A) :=
  RelationAlgebraHom.mk' (mk l) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) rfl (fun _ => rfl)

@[simp]
theorem mkHom_apply (f : ∀ i, A i) : mkHom A l f = mk l f := rfl

theorem mkHom_surjective : Function.Surjective (mkHom A l) := mk_surjective

/-- Every element of a reduced product of relation algebras is the image of some element of the
product under the quotient homomorphism. -/
@[elab_as_elim]
theorem mkHom_induction_on {p : l.Product A → Prop} (x : l.Product A)
    (h : ∀ f : ∀ i, A i, p (mkHom A l f)) : p x :=
  induction_on x h

variable {f g : ∀ i, A i}

theorem mkHom_eq_mkHom : mkHom A l f = mkHom A l g ↔ ∀ᶠ i in l, f i = g i :=
  mk_eq_mk

theorem mkHom_le_mkHom : mkHom A l f ≤ mkHom A l g ↔ ∀ᶠ i in l, f i ≤ g i := by
  rw [← sup_eq_right, ← SupHomClass.map_sup, mkHom_eq_mkHom]
  simp only [Pi.sup_apply, sup_eq_right]

instance [∀ i, TrivialStar (A i)] : TrivialStar (l.Product A) where
  star_trivial x := by
    induction x using mkHom_induction_on with | h f
    rw [← map_star]
    exact congrArg _ (funext fun i => star_trivial (f i))

section Ultraproduct

variable (U : Ultrafilter ι) [∀ i, CompatibleRelationAlgebra (A i)]

omit [∀ i, CompatibleRelationAlgebra (A i)] in
/-- Every tuple of elements of a reduced product consists of classes of elements of the
product. -/
theorem exists_mkHom_eq {n : ℕ} (x : Fin n → (U : Filter ι).Product A) :
    ∃ f : Fin n → ∀ i, A i, (fun j => mkHom A (U : Filter ι) (f j)) = x :=
  ⟨fun j => (x j).out, funext fun _ => Quotient.out_eq _⟩

/-- The relation algebra structure on an ultraproduct agrees with its first-order structure. -/
instance instCompatibleRelationAlgebra :
    CompatibleRelationAlgebra ((U : Filter ι).Product A) where
  toStructure := Ultraproduct.structure
  funMap_sup x := by
    obtain ⟨f, rfl⟩ := exists_mkHom_eq U x
    exact (Ultraproduct.funMap_cast _ f).trans <| (congrArg (mkHom A (U : Filter ι))
      (funext fun i => CompatibleRelationAlgebra.funMap_sup _)).trans (SupHomClass.map_sup _ _ _)
  funMap_inf x := by
    obtain ⟨f, rfl⟩ := exists_mkHom_eq U x
    exact (Ultraproduct.funMap_cast _ f).trans <| (congrArg (mkHom A (U : Filter ι))
      (funext fun i => CompatibleRelationAlgebra.funMap_inf _)).trans (InfHomClass.map_inf _ _ _)
  funMap_compl x := by
    obtain ⟨f, rfl⟩ := exists_mkHom_eq U x
    exact (Ultraproduct.funMap_cast _ f).trans <| (congrArg (mkHom A (U : Filter ι))
      (funext fun i => CompatibleRelationAlgebra.funMap_compl _)).trans (map_compl' _ _)
  funMap_mul x := by
    obtain ⟨f, rfl⟩ := exists_mkHom_eq U x
    exact (Ultraproduct.funMap_cast _ f).trans <| (congrArg (mkHom A (U : Filter ι))
      (funext fun i => CompatibleRelationAlgebra.funMap_mul _)).trans (map_mul _ _ _)
  funMap_star x := by
    obtain ⟨f, rfl⟩ := exists_mkHom_eq U x
    exact (Ultraproduct.funMap_cast _ f).trans <| (congrArg (mkHom A (U : Filter ι))
      (funext fun i => CompatibleRelationAlgebra.funMap_star _)).trans (map_star _ _)
  funMap_one x := by
    obtain ⟨f, rfl⟩ := exists_mkHom_eq U x
    exact (Ultraproduct.funMap_cast _ f).trans <| (congrArg (mkHom A (U : Filter ι))
      (funext fun i => CompatibleRelationAlgebra.funMap_one _)).trans (map_one _)

end Ultraproduct

end Filter.Product
