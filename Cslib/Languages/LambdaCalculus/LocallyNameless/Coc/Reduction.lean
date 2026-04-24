/-
Copyright (c) 2026 Matt Hunzinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Hunzinger
-/

module

public import Cslib.Foundations.Data.HasFresh
public import Cslib.Foundations.Syntax.HasAlphaEquiv
public import Cslib.Foundations.Data.Relation
public import Cslib.Foundations.Syntax.HasSubstitution
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Coc.Opening

@[expose] public section

/-! # Calculus of Constructions

The Calculus of Constructions

## References

* [T. Coquand, *An algorithm for type-checking dependent types*][Coquand1996]

* [A. Chargueraud, *The Locally Nameless Representation*][Chargueraud2012]

-/

namespace Cslib

universe u

namespace LambdaCalculus.LocallyNameless.Coc

variable {Var : Type*}

open Term

/-- A relation on terms is `RedRefl` if it is reflexive. -/
def RedRefl (R : Term Var → Term Var → Prop) : Prop :=
  ∀ T, R T T

/-- A relation on terms is `RedIn` if it is compatible with substitution in the
    argument position, i.e., reducing the substituted term propagates. -/
def RedIn [DecidableEq Var] (R : Term Var → Term Var → Prop) : Prop :=
  ∀ (t : Term Var) (x : Var) (u u' : Term Var), R u u' → R (t[x:=u]) (t[x:=u'])

/-- A relation on terms is `RedAll` if it is compatible with substitution in both
    the reduced term and argument positions simultaneously. -/
def RedAll [DecidableEq Var] (R : Term Var → Term Var → Prop) : Prop :=
  ∀ (x : Var) (t t' : Term Var), R t t' → ∀ (u u' : Term Var), R u u' → R (t[x:=u]) (t'[x:=u'])

/-- A relation on terms is `RedOut` if it is closed under substitution, i.e., reduction
propagates through outer substitution. -/
def RedOut [DecidableEq Var] (R : Term Var → Term Var → Prop) : Prop :=
  ∀ (a b : Term Var), R a b → ∀ (x : Var) (u : Term Var), u.LC → R (a[x:=u]) (b[x:=u])

lemma RedAll_to_out [DecidableEq Var] {R : Term Var → Term Var → Prop}
    (hall : RedAll R) (hrefl : RedRefl R) : RedOut R := by
  intro a b h x u _
  exact hall x a b h u u (hrefl u)

/-- A relation is `RedRegular` if it relates only locally closed terms. -/
def RedRegular (R : Term Var → Term Var → Prop) : Prop :=
  ∀ t t', R t t' → t.LC ∧ t'.LC

/-- A relation satisfies `RedThrough` if reduction commutes with simultaneous opening:
    opening bodies with related terms yields related terms. -/
def RedThrough [DecidableEq Var] (R : Term Var → Term Var → Prop) : Prop :=
  ∀ (x : Var) (t₁ t₂ u₁ u₂ : Term Var),
    x ∉ t₁.fv → x ∉ u₁.fv →
    R (t₁ ^ᵗ fvar x) (u₁ ^ᵗ fvar x) → R t₂ u₂ →
    R (t₁ ^ᵗ t₂) (u₁ ^ᵗ u₂)

lemma redAll_to_through [DecidableEq Var] {R : Term Var → Term Var → Prop}
    (_ : RedRegular R) (hall : RedAll R) : RedThrough R := by
  intro x t₁ t₂ u₁ u₂ hx₁ hx₂ hopen htu
  rw [subst_intro x t₂ t₁ hx₁, subst_intro x u₂ u₁ hx₂]
  exact hall x _ _ hopen _ _ htu

/-- A relation satisfies `RedRename` if reduction is stable under renaming of the
    opening variable, provided the variable is fresh for both terms. -/
def RedRename [DecidableEq Var] (R : Term Var → Term Var → Prop) : Prop :=
  ∀ (x : Var) (t t' : Term Var) (y : Var),
    R (t ^ᵗ fvar x) (t' ^ᵗ fvar x) →
    x ∉ t.fv → x ∉ t'.fv →
    R (t ^ᵗ fvar y) (t' ^ᵗ fvar y)

lemma redOut_to_rename [DecidableEq Var] {R : Term Var → Term Var → Prop}
    (hout : RedOut R) : RedRename R := by
  intro x t t' y h hmemt hmemt'
  rw [subst_intro x (fvar y) t hmemt, subst_intro x (fvar y) t' hmemt']
  exact hout _ _ h x (fvar y) .var

/-- β-equivalence. -/
@[reduction_sys "β"]
inductive BetaEquiv : Term Var → Term Var → Prop
  /-- β-redex: `(λ A. B) N ⟶ B ^ᵗ N`. -/
  | red : (abs A B).LC → N.LC → BetaEquiv (.app (.abs A B) N) (B ^ᵗ N)
  /-- Congruence in the function position of an application. -/
  | app₁ : t₂.LC → BetaEquiv t₁ t₁' → BetaEquiv (.app t₁ t₂) (.app t₁' t₂)
  /-- Congruence in the argument position of an application. -/
  | app₂ : t₁.LC → BetaEquiv t₂ t₂' → BetaEquiv (.app t₁ t₂) (.app t₁ t₂')
  /-- Congruence in the type annotation of an abstraction. -/
  | abs₁ : t₂.body → BetaEquiv t₁ t₁' → BetaEquiv (.abs t₁ t₂) (.abs t₁' t₂)
  /-- Congruence in the body of an abstraction. -/
  | abs₂ (ρ : Finset Var) :
      t₁.LC →
      (∀ x ∉ ρ, BetaEquiv (t₂ ^ᵗ .fvar x) (t₂' ^ᵗ .fvar x)) →
      BetaEquiv (.abs t₁ t₂) (.abs t₁ t₂')
  /-- Congruence in the domain of a pi type. -/
  | pi₁ : t₂.body → BetaEquiv t₁ t₁' → BetaEquiv (.pi t₁ t₂) (.pi t₁' t₂)
  /-- Congruence in the codomain of a pi type. -/
  | pi₂ (ρ : Finset Var) :
      t₁.LC →
      (∀ x ∉ ρ, BetaEquiv (t₂ ^ᵗ .fvar x) (t₂' ^ᵗ .fvar x)) →
      BetaEquiv (.pi t₁ t₂) (.pi t₁ t₂')

lemma beta_red_out [DecidableEq Var] [HasFresh Var] : RedOut (@BetaEquiv Var) := by
  intro a b h x u hu
  induction h with
  | red hlc hn =>
    simp only [open_subst _ _ hu]
    exact .red (subst_lc hlc hu x) (subst_lc hn hu x)
  | app₁ => exact .app₁ (subst_lc ‹_› hu x) ‹_›
  | app₂ => exact .app₂ (subst_lc ‹_› hu x) ‹_›
  | abs₁ hbody _ ih =>
    obtain ⟨L, hL⟩ := hbody
    refine BetaEquiv.abs₁ ⟨free_union Var, fun y hy => ?_⟩ ih
    rw [subst_open_var x y u _ (by grind) hu]
    exact subst_lc (hL y (by grind)) hu x
  | abs₂ ρ hlc _ ih =>
    apply BetaEquiv.abs₂ (free_union Var) (subst_lc hlc hu x)
    intro y hy
    rw [subst_open_var x y u _ (by grind) hu, subst_open_var x y u _ (by grind) hu]
    exact ih y (by grind)
  | pi₁ hbody _ ih =>
    obtain ⟨L, hL⟩ := hbody
    refine BetaEquiv.pi₁ ⟨free_union Var, fun y hy => ?_⟩ ih
    rw [subst_open_var x y u _ (by grind) hu]
    exact subst_lc (hL y (by grind)) hu x
  | pi₂ ρ hlc _ ih =>
    apply BetaEquiv.pi₂ (free_union Var) (subst_lc hlc hu x)
    intro y hy
    rw [subst_open_var x y u _ (by grind) hu, subst_open_var x y u _ (by grind) hu]
    exact ih y (by grind)

lemma beta_red_rename [DecidableEq Var] [HasFresh Var] : RedRename (@BetaEquiv Var) :=
  redOut_to_rename beta_red_out

end LambdaCalculus.LocallyNameless.Coc

end Cslib
