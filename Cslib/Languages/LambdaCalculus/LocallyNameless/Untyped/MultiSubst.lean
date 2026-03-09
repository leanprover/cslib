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

open scoped Context

variable {Var : Type u} {Base : Type v} [DecidableEq Var]

/-- An environment in context of multi substition is a list of pairs of
    variable targets and terms to be substituted for that target -/
abbrev Env (Var : Type u) := Context Var (Term Var)

/-- Multi-substitution substitutes all target variables
    in an environment by their corresponding terms -/
@[scoped grind =]
def multiSubst (E : Env Var) (M : Term Var) : Term Var :=
  match E with
  | [] => M
  | ⟨i, sub⟩ :: E' => (multiSubst E' M) [ i := sub ]

/-- The free variables of an environment are the union of
    the free variables of all terms in the environment.
    The target variables are not necessarily included -/
def Env.fv (E : Env Var) : Finset Var :=
  match E with
  | [] => {}
  | ⟨ _, sub ⟩ :: E' => sub.fv ∪ Env.fv E'

attribute [scoped grind =] Env.fv

/-- An environment is locally closed if all terms in the environment are locally closed -/
abbrev env_LC (E : Env Var) : Prop := ∀ {x M}, ⟨x, M⟩ ∈ E → LC M

/-- Adding a locally closed term to an environment preserves local closure -/
lemma env_LC_cons (lc_sub : LC sub) (lc_E : env_LC E) : env_LC (⟨ x, sub ⟩ :: E) := by
  grind

/-- Multi-substitution of a fresh variable does nothing -/
lemma multiSubst_fvar_fresh (E : Env Var) : ∀ x ∉ E.dom, multiSubst E (fvar x) = fvar x := by
  induction E with grind

/-- If x is neither a free variable of an environment Ns or a term M, then
    x is also not a free variable of the multi-substitution of Ns into M -/
lemma multiSubst_preserves_not_fvar (M : Term Var) (E : Env Var) (nmem : x ∉ M.fv ∪ E.fv) :
    x ∉ (multiSubst E M).fv := by
  induction E with grind [subst_preserve_not_fvar]

/-- Multi-substitution propagates recursively through an application -/
lemma multiSubst_app (M N : Term Var) (E : Env Var) :
    multiSubst E (app M N) = app (multiSubst E M) (multiSubst E N) := by
  induction E with grind

/-- Multi-substitution propagates recursively through an abstraction -/
lemma multiSubst_abs (M : Term Var) (E : Env Var) :
    multiSubst E (abs M) = abs (multiSubst E M) := by
  induction E with grind

/-- Multi-substitution commutes with opening a term with a fresh variable,
    provided that the variable is not in the domain of the environment
    and the environment is locally closed -/
lemma multiSubst_open_var [HasFresh Var] (M : Term Var) (E : Env Var) (x : Var)
  (h_ndom : x ∉ E.dom) (h_lc : env_LC E) :
    multiSubst E (M ^ fvar x) = multiSubst E M ^ fvar x := by
  induction E with grind

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
