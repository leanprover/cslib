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

This file defines additional constructions on `PFunctor` that don't belong in core mathlib.
The main definitions is `monomial A B` for the `PFunctor` with constant family `B` over `A`,
as well as special cases of this such as a canonical choice of `0` and `1`.

We also define the sum `P + Q` whose shapes are a sum of the shapes of `P` and `Q`,
with a type family defined by sum elimination into the individual child types of `P` and `Q`.
-/

@[expose] public section

universe uA uB uA₁ uA₂

namespace PFunctor

section monomial

/-- The monomial `PFunctor` with head type `A` and constant `B` for any `a : A`. -/
@[reducible] def monomial (A : Type uA) (B : Type uB) : PFunctor := ⟨A, fun _ => B⟩

lemma monomial_A (A : Type uA) (B : Type uB) : (monomial A B).A = A := rfl

lemma monomial_B (A : Type uA) (B : Type uB) (a : (monomial A B).A) :
    (monomial A B).B a = B := rfl

end monomial

section zero

/-- The zero polynomial functor, defined as `A = PEmpty` and `B _ = PEmpty`, is the identity with
  respect to sum (up to equivalence) -/
@[reducible] protected def zero : PFunctor := monomial PEmpty PEmpty

instance instZeroPFunctor : Zero PFunctor where zero := PFunctor.zero

@[simp] lemma zero_A : (0 : PFunctor).A = PEmpty := rfl

@[simp] lemma zero_B (a : (0 : PFunctor).A) : (0 : PFunctor).B a = PEmpty := rfl

end zero

section one

/-- The unit polynomial functor, defined as `A = PUnit` and `B _ = PEmpty`, is the identity with
  respect to product (up to equivalence) -/
@[reducible] protected def one : PFunctor := monomial PUnit PEmpty

instance instOnePFunctor : One PFunctor where one := PFunctor.one

@[simp] lemma one_A : (1 : PFunctor).A = PUnit := rfl

@[simp] lemma one_B (a : (1 : PFunctor).A) : (1 : PFunctor).B a = PEmpty := rfl

end one

/-- The constant polynomial functor `P(X) = A X^ PEmpty = A` -/
abbrev const (A : Type uA) : PFunctor := monomial A PEmpty

/-- The linear polynomial functor `P(X) = A X` -/
abbrev linear (A : Type uA) : PFunctor := monomial A PUnit

/-- The self monomial polynomial functor `P(X) = S X^ S` -/
abbrev selfMonomial (S : Type uA) : PFunctor.{uA, uA} := monomial S S

/-- The pure power polynomial functor `P(X) = X^ B` -/
abbrev purePower (B : Type uB) : PFunctor := monomial PUnit B

section add

/-- The sum of two polynomial functors `P` and `Q`, written as `P + Q`,
defined as the sum of the head types and the sum case analysis for the child types. -/
def add (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) :
    PFunctor.{max uA₁ uA₂, uB} := ⟨P.A ⊕ Q.A, Sum.elim P.B Q.B⟩

instance instHAddPFunctor :
  HAdd PFunctor.{uA₁, uB} PFunctor.{uA₂, uB} PFunctor.{max uA₁ uA₂, uB} where
  hAdd := add

@[simp] lemma add_A (P Q : PFunctor) : (add P Q).A = (P.A ⊕ Q.A) := rfl

@[simp] lemma add_B_inl (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) (a : P.A) :
    (add P Q).B (.inl a) = P.B a := rfl

@[simp] lemma add_B_inr (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) (a : Q.A) :
    (add P Q).B (.inr a) = Q.B a := rfl

end add

end PFunctor
