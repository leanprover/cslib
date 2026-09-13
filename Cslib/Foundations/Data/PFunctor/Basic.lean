/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
module

public import Cslib.Init
public import Mathlib.Data.PFunctor.Univariate.Basic

/-!
# Polynomial Functors

Definitions of common `PFunctor` constructions:
- `monomial A B`: constant direction `B` for any shape `a : A`
- `P + Q`: shapes are a disjoint sum, directions are defined by sum elimination on `a : P.A ⊕ Q.A`
- `P * Q`: shapes are pairs of underlying shapes, directions are a disjoint sum over both shapes.

Special cases `C`, `linear`, `selfMonomial`, `purePower`, the indeterminate `y`,
and canonical choices of `0` and `1` are defined as abbreviations or instances over `monomial`.
The scoped notations `A y^ B` and `y^ B` denote `monomial A B` and `purePower B`, respectively.
-/

@[expose] public section

universe uA uB uA₁ uA₂ uB₁ uB₂

namespace PFunctor

/-- Two polynomial functors are equal if their head types are equal and their child types
agree over that equality. -/
@[ext (iff := false)]
theorem ext {P Q : PFunctor.{uA, uB}} (h : P.A = Q.A) (h' : ∀ a, P.B a = Q.B (h ▸ a)) :
    P = Q := by
  cases P; cases Q; simp only [mk.injEq] at h h' ⊢; subst h
  simp_all only [heq_eq_eq, true_and]; funext; exact h' _

section monomial

/-- The monomial `PFunctor` with head type `A` and constant `B` for any `a : A`. -/
abbrev monomial (A : Type uA) (B : Type uB) : PFunctor := ⟨A, fun _ => B⟩

@[inherit_doc] scoped[PFunctor] infixr:82 " y^ " => monomial

lemma monomial_A (A : Type uA) (B : Type uB) : (monomial A B).A = A := rfl

lemma monomial_B (A : Type uA) (B : Type uB) (a : (monomial A B).A) :
    (monomial A B).B a = B := rfl

end monomial

section zero

/-- The zero polynomial functor, defined as `A = PEmpty` and `B _ = PEmpty`, is the identity with
  respect to sum (up to equivalence) -/
@[simps] instance instZeroPFunctor : Zero PFunctor where zero := monomial PEmpty PEmpty

instance instIsEmptyZeroPFunctor : IsEmpty (0 : PFunctor.{uA, uB}).A :=
  inferInstanceAs (IsEmpty PEmpty)

end zero

section one

/-- The unit polynomial functor, defined as `A = PUnit` and `B _ = PEmpty`, is the identity with
  respect to product (up to equivalence) -/
@[simps] instance instOnePFunctor : One PFunctor where one := monomial PUnit PEmpty

instance instUniqueOneA : Unique (1 : PFunctor.{uA, uB}).A := inferInstanceAs (Unique PUnit)

instance instIsEmptyOneB (a : (1 : PFunctor.{uA, uB}).A) : IsEmpty ((1 : PFunctor.{uA, uB}).B a) :=
  inferInstanceAs (IsEmpty PEmpty)

end one

/-- The constant polynomial functor `P(y) = A y^ PEmpty = A`. -/
abbrev C (A : Type uA) : PFunctor := monomial A PEmpty

/-- The linear polynomial functor `P(y) = A y`. -/
abbrev linear (A : Type uA) : PFunctor := monomial A PUnit

/-- The self-monomial polynomial functor `P(y) = S y^ S`. -/
abbrev selfMonomial (S : Type uA) : PFunctor.{uA, uA} := monomial S S

/-- The pure-power polynomial functor `y^ B`, representable on `B`. -/
abbrev purePower (B : Type uB) : PFunctor := monomial PUnit B

@[inherit_doc purePower] scoped[PFunctor] notation:100 "y^" B:100 => purePower B

/-- The indeterminate polynomial functor `P(y) = y`, the identity with respect to
composition and tensor product (up to equivalence). -/
abbrev y : PFunctor := monomial PUnit PUnit

/- Note: no explicit `IsEmpty`/`Unique` instances are needed for the positions and directions
of the abbreviations above: being reducible, they unfold to `PEmpty`/`PUnit` during instance
search. Only `0` and `1` need the explicit instances above, since the `Zero`/`One` instance
projections are not reducible. -/

@[simp] lemma const_pempty : C PEmpty = 0 := rfl

@[simp] lemma const_punit : C PUnit = 1 := rfl

@[simp] lemma linear_punit : linear PUnit = y := rfl

@[simp] lemma selfMonomial_punit : selfMonomial PUnit = y := rfl

@[simp] lemma purePower_punit : purePower PUnit = y := rfl

section add

/-- The sum of two polynomial functors `P` and `Q`, written as `P + Q`,
defined as the sum of the head types and the dependent sum recursor for the child types. -/
@[implicit_reducible] def add (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) :
    PFunctor.{max uA₁ uA₂, uB} :=
  ⟨P.A ⊕ Q.A, @Sum.rec P.A Q.A (fun _ => Type uB) P.B Q.B⟩

@[simps!] instance instHAddPFunctor :
    HAdd PFunctor.{uA₁, uB} PFunctor.{uA₂, uB} PFunctor.{max uA₁ uA₂, uB} where
  hAdd := add

@[simp] lemma add_eq_add (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) :
    P.add Q = P + Q := rfl

end add

section prod

/-- The product of two polynomial functors `P` and `Q`, written as `P * Q`,
defined as the product of the head types and the sum of the child types. -/
@[implicit_reducible] def prod (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) :
    PFunctor.{max uA₁ uA₂, max uB₁ uB₂} := ⟨P.A × Q.A, fun ab => P.B ab.1 ⊕ Q.B ab.2⟩

@[simps!] instance instHMulPFunctor :
    HMul PFunctor.{uA₁, uB₁} PFunctor.{uA₂, uB₂} PFunctor.{max uA₁ uA₂, max uB₁ uB₂} where
  hMul := prod

@[simp] lemma prod_eq_mul (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) :
    P.prod Q = P * Q := rfl

end prod

end PFunctor
