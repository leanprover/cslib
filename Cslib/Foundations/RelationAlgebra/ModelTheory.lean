/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Pi
public import Mathlib.ModelTheory.Ultraproducts

/-!
# First-order language of relation algebras

This module defines the first-order language of relation algebras, following Mathlib's treatment of
the language of rings in `Mathlib.ModelTheory.Algebra.Ring.Basic`, and shows that ultraproducts of
relation algebras are relation algebras whose structure is the one used for Łoś's theorem.

The signature is the one of Tarski's axiomatization, as in `Cslib.RelationAlgebra.ofTarski`: join,
complement, composition, converse and identity. Meet is definable from join and complement, so
this language has the same expressive power as the signature `(A, +, ·, -, ;, ˘, 1')` used in
[Monk1964].

For a filter `l` on `ι` and a family `A : ι → Type*` of relation algebras, the reduced product
`l.Product A` (the quotient of the product by the relation of being equal on a set in `l`) is a
relation algebra, because relation algebras are defined by equations. When `l` is an ultrafilter
this is the ultraproduct, and the relation algebra structure is compatible with the first-order
structure of `Mathlib.ModelTheory.Ultraproducts`.

## Main definitions

* `FirstOrder.Language.relationAlgebra`: the language of relation algebras, with function symbols
  for `⊔`, `ᶜ`, `*`, `star` and `1`.
* `FirstOrder.RelationAlgebra.CompatibleRelationAlgebra`: a class stating that a type is a
  `Language.relationAlgebra.Structure`, and that this structure agrees with the operations already
  given on the type.
* `FirstOrder.RelationAlgebra.compatibleRelationAlgebraOfRelationAlgebra`: given a type with
  instances for each of the operations, construct a `CompatibleRelationAlgebra` instance.
* `Filter.Product.instRelationAlgebra`: the relation algebra structure on a reduced product.
* `Filter.Product.mkHom`: the quotient map from the product, as a `RelationAlgebraHom`.
* `Filter.Product.instCompatibleRelationAlgebra`: the relation algebra structure on an
  ultraproduct agrees with its first-order structure.

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
  .ofTarski
    (mk_surjective.forall₂.mpr fun a b => congrArg (mk l) (sup_comm a b))
    (mk_surjective.forall₃.mpr fun a b c => congrArg (mk l) (sup_assoc a b c))
    (mk_surjective.forall₂.mpr fun a b =>
      congrArg (mk l) (show (aᶜ ⊔ b)ᶜ ⊔ (aᶜ ⊔ bᶜ)ᶜ = a by simp [← inf_sup_left]))
    (mk_surjective.forall₃.mpr fun a b c => congrArg (mk l) (mul_assoc a b c))
    (mk_surjective.forall.mpr fun a => congrArg (mk l) (mul_one a))
    (mk_surjective.forall.mpr fun a => congrArg (mk l) (star_star a))
    (mk_surjective.forall₂.mpr fun a b => congrArg (mk l) (star_mul a b))
    (mk_surjective.forall₃.mpr fun a b c => congrArg (mk l) (RelationAlgebra.sup_mul a b c))
    (mk_surjective.forall₂.mpr fun a b => congrArg (mk l) (RelationAlgebra.star_sup a b))
    (mk_surjective.forall₂.mpr fun a b =>
      congrArg (mk l) (sup_eq_right.mpr (RelationAlgebra.tarski a b)))

end

variable (A l) in
/-- The quotient map from the product of a family of relation algebras to its reduced product. -/
def mkHom : RelationAlgebraHom (∀ i, A i) (l.Product A) where
  toFun := mk l
  map_sup' _ _ := rfl
  map_inf' a b := by
    rw [← compl_compl (mk l a ⊓ mk l b), compl_inf]
    change mk l (a ⊓ b) = mk l (aᶜ ⊔ bᶜ)ᶜ
    rw [← compl_inf, compl_compl]
  map_top' := by
    rw [← sup_compl_eq_top (x := mk l 1)]
    change mk l ⊤ = mk l (1 ⊔ 1ᶜ)
    rw [sup_compl_eq_top]
  map_bot' := by
    rw [← compl_top (α := l.Product A), ← sup_compl_eq_top (x := mk l 1)]
    change mk l ⊥ = mk l (1 ⊔ 1ᶜ)ᶜ
    rw [sup_compl_eq_top, compl_top]
  map_one' := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl

/-- Every element of a reduced product of relation algebras is the image of some element of the
product under the quotient homomorphism. -/
@[elab_as_elim]
theorem mkHom_induction_on {p : l.Product A → Prop} (x : l.Product A)
    (h : ∀ f : ∀ i, A i, p (mkHom A l f)) : p x :=
  induction_on x h

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
