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
- `P + Q`: shapes are a disjoint sum, directions are define by sum elimination on `a : P.A ⊕ Q.A`
- `P * Q`: shapes are pairs of underlying shapes, directions are a disjoint sum over both shapes.

Special cases `const`, `linear`, `selfMonomial`, `purePower`, the indeterminate `X`,
and canonical choices of `0` and `1` are defined as `abbrev` or instances over `monomial`.
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

/-- The constant polynomial functor `P(X) = A X^ PEmpty = A` -/
abbrev const (A : Type uA) : PFunctor := monomial A PEmpty

/-- The linear polynomial functor `P(X) = A X` -/
abbrev linear (A : Type uA) : PFunctor := monomial A PUnit

/-- The self monomial polynomial functor `P(X) = S X^ S` -/
abbrev selfMonomial (S : Type uA) : PFunctor.{uA, uA} := monomial S S

/-- The pure power polynomial functor `P(X) = X^ B` -/
abbrev purePower (B : Type uB) : PFunctor := monomial PUnit B

/-- The indeterminate polynomial functor `P(X) = X`, the identity with respect to
composition and tensor product (up to equivalence). -/
abbrev X : PFunctor := monomial PUnit PUnit

/- Note: no explicit `IsEmpty`/`Unique` instances are needed for the positions and directions
of the abbreviations above: being reducible, they unfold to `PEmpty`/`PUnit` during instance
search. Only `0` and `1` need the explicit instances above, since the `Zero`/`One` instance
projections are not reducible. -/

@[simp] lemma const_pempty : const PEmpty = 0 := rfl

@[simp] lemma const_punit : const PUnit = 1 := rfl

@[simp] lemma linear_punit : linear PUnit = X := rfl

@[simp] lemma selfMonomial_punit : selfMonomial PUnit = X := rfl

@[simp] lemma purePower_punit : purePower PUnit = X := rfl

section add

/-- The sum of two polynomial functors `P` and `Q`, written as `P + Q`,
defined as the sum of the head types and the sum case analysis for the child types.

This is kept as a `def` alongside the `HAdd` instance below, even though that instance is
exactly as universe-general as `add` itself: the `binop%` elaborator behind `+` eagerly
unifies the types of both operands with the expected type, so when the expected type carries
universe metavariables (e.g. inside `PFunctor.W (P.add (.const α))` with `α : Type v`),
`P + Q` can fail to elaborate where `P.add Q` succeeds; see `CslibTests/PFunctor.lean`. -/
@[simps] def add (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) :
    PFunctor.{max uA₁ uA₂, uB} := ⟨P.A ⊕ Q.A, Sum.elim P.B Q.B⟩

/-- Addition of polynomial functors, defined as the sum construction. -/
instance instHAddPFunctor :
    HAdd PFunctor.{uA₁, uB} PFunctor.{uA₂, uB} PFunctor.{max uA₁ uA₂, uB} where
  hAdd := add

/-- Normalize addition of `PFunctor`s to avoid `simp` mismatches between the notations. -/
@[simp] lemma add_def (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) :
    P + Q = P.add Q := rfl

end add

section prod

/-- The product of two polynomial functors `P` and `Q`, written as `P * Q`,
defined as the product of the head types and the sum of the child types.
Unlike `add`, the child types of `P` and `Q` may live in different universes,
since they are combined with `⊕` rather than `Sum.elim`. -/
@[simps] def prod (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) :
    PFunctor.{max uA₁ uA₂, max uB₁ uB₂} := ⟨P.A × Q.A, fun ab => P.B ab.1 ⊕ Q.B ab.2⟩

/-- Multiplication of polynomial functors, defined as the product construction.
As with addition, we deliberately do not add a homogeneous `Mul` instance. -/
instance instHMulPFunctor :
    HMul PFunctor.{uA₁, uB₁} PFunctor.{uA₂, uB₂} PFunctor.{max uA₁ uA₂, max uB₁ uB₂} where
  hMul := prod

/-- Normalize multiplication of `PFunctor`s to avoid `simp` mismatches between the notations. -/
@[simp] lemma mul_def (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) :
    P * Q = P.prod Q := rfl

end prod

end PFunctor
