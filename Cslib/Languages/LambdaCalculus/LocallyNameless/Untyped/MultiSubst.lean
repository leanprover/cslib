/-
Copyright (c) 2025 David Wegmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wegmann
-/


module

public import Cslib.Foundations.Data.Relation
public import Cslib.Foundations.Data.HasFresh
public import Cslib.Foundations.Syntax.HasSubstitution
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Stlc.Basic
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta

@[expose] public section

namespace Cslib

universe u v


namespace LambdaCalculus.LocallyNameless.Untyped.Term

variable {Var : Type u} {Base : Type v} [DecidableEq Var]

/-- An environment in context of multi substition is a list of pairs of
    variable targets and terms to be substituted for that target -/
abbrev Environment (Var : Type u) := Context Var (Term Var)

/-- multi-substitution substitutes all target variables
    in an environment by their corresponding terms -/
def multiSubst (σ : Environment Var) (M : Term Var) : Term Var :=
  match σ with
  | [] => M
  | ⟨ i, sub ⟩ :: σ' => (multiSubst σ' M) [ i := sub ]

/-- the free variables of an environment are the union of
    the free variables of all terms in the environment.
    The target variables are not necessarily included -/
def Environment.fv (E : Environment Var) : Finset Var :=
  match E with
  | [] => {}
  | ⟨ _, sub ⟩ :: E' => sub.fv ∪ Environment.fv E'

/-- an environment is locally closed if all terms in the environment are locally closed -/
@[simp, grind .]
def env_LC (Γ : Environment Var) : Prop := ∀ {x M}, ⟨ x, M ⟩ ∈ Γ → LC M

omit [DecidableEq Var] in
/-- adding a locally closed term to an environment preserves local closure -/
lemma env_LC_cons {Γ : Environment Var} {x : Var} {sub : Term Var}
  (lc_sub : LC sub) (lc_Γ : env_LC Γ)
  : env_LC (⟨ x, sub ⟩ :: Γ) := by
  intro y M h_mem
  cases h_mem <;> aesop

/-- multi-substitution of a fresh variable does nothing -/
lemma multiSubst_fvar_fresh (E : Environment Var) :
    ∀ x ∉ E.dom, multiSubst E (Term.fvar x) = Term.fvar x := by
  induction E
  · case nil => simp [multiSubst]
  · case cons N E ih => cases N; simp_all; grind[multiSubst]

/-- when x is neither a free variable of an environment Ns or a term M, then
    x is also not a free variable of the multi-substitution of Ns into M -/
lemma multiSubst_preserves_not_fvar {x : Var}
  (M : Term Var)
  (E : Environment Var)
  (nmem : x ∉ M.fv ∪ E.fv) :
    x ∉ (multiSubst E M).fv := by
  induction E <;> grind[multiSubst, subst_preserve_not_fvar, Environment.fv]

/-- multi-substitution propagates recursively through an application -/
lemma multiSubst_app (M N : Term Var) (E : Environment Var) :
      multiSubst E (Term.app M N) = Term.app (multiSubst E M) (multiSubst E N) := by
  induction E <;> grind[multiSubst]

/-- multi-substitution propagates recursively through an abstraction -/
lemma multiSubst_abs (M : Term Var) (E : Environment Var) :
      multiSubst E (Term.abs M) = Term.abs (multiSubst E M) := by
  induction E <;> grind[multiSubst]

/-- multi-substitution commutes with opening a term with a fresh variable,
    provided that the variable is not in the domain of the environment
    and the environment is locally closed -/
lemma multiSubst_open_var [HasFresh Var] (M : Term Var) (E : Environment Var) (x : Var)
  (h_ndom : x ∉ E.dom)
  (h_lc : env_LC E) :
    (multiSubst E (M ^ (Term.fvar x))) = (multiSubst E M) ^ (Term.fvar x) := by
  induction E with
  | nil => rfl
  | cons N E ih =>
    rw[multiSubst, multiSubst]
    rw[ih]
    · rw[subst_open_var]
      · cases N
        simp_all
        grind
      · grind
    · simp_all
    grind

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
