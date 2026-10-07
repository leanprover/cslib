/-
Copyright (c) 2026 Fabrizio Montesi, PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Devon Tuma, Quang Dao
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

The extensions of `P + Q` and `C A` are described by `addObjEquiv` and `constObjEquiv`.
The child-map API includes `const`, `Unary`, and `DecidableEqChildren`. `W.induction` is an
induction principle for `P.W` through `W.mk`.
-/

@[expose] public section

universe uA uB uA₁ uA₂ uB₁ uB₂ v w

namespace PFunctor

/-- Two polynomial functors are equal if their head types are equal and their child types
agree over that equality. -/
@[ext (iff := false)]
theorem ext {P Q : PFunctor.{uA, uB}} (h : P.A = Q.A) (h' : ∀ a, P.B a = Q.B (h ▸ a)) :
    P = Q := by
  cases P; cases Q; simp only [mk.injEq] at h h' ⊢; subst h
  simp_all only [heq_eq_eq, true_and]; funext; exact h' _

/-- The constant child map for `a`. -/
def const {P : PFunctor} (a : P.A) (x : α) : P.B a → α := fun _ => x

@[simp, scoped grind =]
theorem const_apply {P : PFunctor} (a : P.A) (x : α) (i : P.B a) : PFunctor.const a x i = x := rfl

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
respect to sum (up to equivalence). -/
@[simps] instance instZeroPFunctor : Zero PFunctor where zero := monomial PEmpty PEmpty

-- The head type is independent of the child universe. Fixing it to `0` avoids an
-- unconstrained universe metavariable when these head instances are synthesized.
instance instIsEmptyZeroPFunctor : IsEmpty (0 : PFunctor.{uA, 0}).A :=
  inferInstanceAs (IsEmpty PEmpty)

end zero

section one

/-- The unit polynomial functor, defined as `A = PUnit` and `B _ = PEmpty`, is the identity with
respect to product (up to equivalence). -/
@[simps] instance instOnePFunctor : One PFunctor where one := monomial PUnit PEmpty

instance instUniqueOneA : Unique (1 : PFunctor.{uA, 0}).A := inferInstanceAs (Unique PUnit)

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

@[simp] lemma C_pempty : C PEmpty = 0 := rfl

@[simp] lemma C_punit : C PUnit = 1 := rfl

@[simp] lemma linear_punit : linear PUnit = y := rfl

@[simp] lemma selfMonomial_punit : selfMonomial PUnit = y := rfl

@[simp] lemma purePower_punit : purePower PUnit = y := rfl

section add

/-- The sum of two polynomial functors `P` and `Q`, written as `P + Q`,
defined as the sum of the head types and the dependent sum recursor for the child types.

The child universes must agree. The named spelling `P.add Q` can elaborate in contexts where
`P + Q` fails to infer universes, such as under `PFunctor.W`; see `CslibTests.PFunctor`. -/
@[implicit_reducible] def add (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) :
    PFunctor.{max uA₁ uA₂, uB} :=
  ⟨P.A ⊕ Q.A, @Sum.rec P.A Q.A (fun _ => Type uB) P.B Q.B⟩

@[simps!] instance instHAddPFunctor :
    HAdd PFunctor.{uA₁, uB} PFunctor.{uA₂, uB} PFunctor.{max uA₁ uA₂, uB} where
  hAdd := add

/- Both named operations and arithmetic notation are available; `simp` normalizes to the
notation, for both addition and multiplication. -/
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

section Obj

variable {X : Type v} {Y : Type w}

@[simp]
theorem map_id' (P : PFunctor.{uA, uB}) : P.map (id : X → X) = id :=
  funext P.id_map

@[simp]
theorem map_comp_map (P : PFunctor.{uA, uB}) {Z : Type*} (f : X → Y) (g : Y → Z) :
    P.map g ∘ P.map f = P.map (g ∘ f) :=
  funext (P.map_map f g)

/-- The extension of a sum of polynomial functors is the sum of their extensions. -/
def addObjEquiv (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) (X : Type v) :
    (P + Q).Obj X ≃ P.Obj X ⊕ Q.Obj X where
  toFun
    | .mk (.inl a) f => .inl (.mk a f)
    | .mk (.inr a) f => .inr (.mk a f)
  invFun
    | .inl (.mk a f) => .mk (.inl a) f
    | .inr (.mk a f) => .mk (.inr a) f
  left_inv x := by cases x with | mk s f => cases s <;> rfl
  right_inv x := by rcases x with (x | x) <;> cases x <;> rfl

@[simp]
theorem addObjEquiv_mk_inl (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) (a : P.A)
    (f : P.B a → X) : addObjEquiv P Q X (.mk (.inl a) f) = .inl (.mk a f) := rfl

@[simp]
theorem addObjEquiv_mk_inr (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) (a : Q.A)
    (f : Q.B a → X) : addObjEquiv P Q X (.mk (.inr a) f) = .inr (.mk a f) := rfl

theorem addObjEquiv_map (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) (f : X → Y)
    (x : (P + Q).Obj X) :
    addObjEquiv P Q Y ((P + Q).map f x) = Sum.map (P.map f) (Q.map f) (addObjEquiv P Q X x) := by
  cases x with | mk s g => cases s <;> rfl

/-- The extension of a constant polynomial functor is the constant. -/
def constObjEquiv (A : Type uA) (X : Type v) : (C.{uA, uB} A).Obj X ≃ A where
  toFun x := x.fst
  invFun a := .mk a PEmpty.elim
  left_inv x := by cases x with | mk a f => exact congrArg (Obj.mk a) (funext (·.elim))
  right_inv _ := rfl

@[simp]
theorem constObjEquiv_mk (A : Type uA) (a : A) (f : PEmpty.{uB + 1} → X) :
    constObjEquiv A X (.mk a f) = a := rfl

@[simp]
theorem constObjEquiv_map (A : Type uA) (f : X → Y) (x : (C.{uA, uB} A).Obj X) :
    constObjEquiv A Y ((C A).map f x) = constObjEquiv A X x := rfl

end Obj

section W

variable {P : PFunctor.{uA, uB}}

/-- Induction on `P.W` through `W.mk`, keeping subtrees typed as `P.W` rather than `WType P.B`. -/
@[elab_as_elim, induction_eliminator]
protected theorem W.induction {motive : P.W → Prop}
    (mk : ∀ (a : P.A) (f : P.B a → P.W), (∀ i, motive (f i)) → motive (W.mk (.mk a f)))
    (w : P.W) : motive w := by
  induction w using WType.rec with
  | mk a f ih => exact mk a f ih

end W

section Unary

/-- A polynomial functor is unary if all child types have exactly one element. -/
class Unary (P : PFunctor) where
  unary (a : P.A) : Unique (P.B a)

attribute [instance_reducible, instance] PFunctor.Unary.unary

theorem Unary.fun_eq_const [Unary P]
    (a : P.A) (f : P.B a → α) : f = fun _ => f default := by
  funext i
  exact congrArg f (Subsingleton.elim i default)

/-- A polynomial functor has children with decidable equality. -/
class DecidableEqChildren (P : PFunctor) where
  decidableEq (a : P.A) : DecidableEq (P.B a)

attribute [instance_reducible, instance] DecidableEqChildren.decidableEq

/-- A unary polynomial functor has decidable child equality. -/
instance (P : PFunctor) [P.Unary] : P.DecidableEqChildren where
  decidableEq _ _ _ := isTrue (Subsingleton.elim _ _)

/-- Constructs a unary polynomial functor. -/
abbrev mkUnary (A : Type*) : PFunctor where
  A := A
  B := fun _ => Unit

instance (A : Type uA) : (linear.{uA, uB} A).Unary where
  unary _ := inferInstanceAs (Unique PUnit)

end Unary

end PFunctor
