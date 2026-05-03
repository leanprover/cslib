/-
Copyright (c) 2025 David Wegmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wegmann
-/

module

public import Cslib.Foundations.Data.HasFresh
public import Cslib.Foundations.Data.Relation
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Stlc.Basic
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.StrongNorm
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LcAt
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.MultiSubst

/-! Strong normalization (termination) for full beta-reduction of simply typed lambda calculus. -/

@[expose] public section

set_option linter.unusedDecidableInType false

namespace Cslib

universe u v

namespace LambdaCalculus.LocallyNameless.Stlc

open Untyped Typing LambdaCalculus.LocallyNameless.Untyped.Term

variable {Var : Type u} {Base : Type v} [DecidableEq Var] [HasFresh Var]

open LambdaCalculus.LocallyNameless.Stlc
open scoped Term

/-- A set of terms is called saturated if it

    1. only contains locally closed terms,
    2. only contains strongly normalizing terms,
    3. contains all neutral locally closed terms, and
    4. is closed under top-level β-reduction of the form (λ M) N P₁ … Pₙ → M ^ N P₁ … Pₙ.
-/
@[scoped grind]
structure Saturated (S : Set (Term Var)) : Prop where
  lc : ∀ M ∈ S, LC M
  sn : ∀ M ∈ S, SN M
  neutal_lc : ∀ M, Neutral M → LC M → M ∈ S
  multiApp : ∀ M N P, LC N → SN N → multiApp (M ^ N) P ∈ S → multiApp (M.abs.app N) P ∈ S

/-- The semantic map maps each type to a corresponding saturated set of terms.
    For the strong normalization proof to work, we must ensure that
    Γ ⊢ t ∶ τ implies that t is in the set of terms corresponding to τ.

    Strong normalization later follows from the fact that terms in saturated
    sets are strongly normalizing.
-/
@[simp, scoped grind =]
def semanticMap : Ty Base → Set (Term Var)
  | .base _ => { t | SN t ∧ LC t }
  | .arrow τ₁ τ₂ => { t | ∀ s, s ∈ semanticMap τ₁ → app t s ∈ semanticMap τ₂ }

/-- The sets constructed by semanticMap are saturated -/
lemma semanticMap_saturated (τ : Ty Base) : @Saturated Var (semanticMap τ) := by
  induction τ with
  | base => grind [sn_abs_app_multiApp, sn_neutral, open_abs_lc]
  | arrow τ₁ τ₂ ih₁ ih₂ =>
    constructor
    · grind [ih₁.neutal_lc (fvar <| fresh {}) (.fvar <| fresh {}) (.fvar <| fresh {}), cases LC]
    · grind [sn_app_left (Var := Var) (N := fvar <| fresh {})]
    · grind
    · intro M N P _ _ _ s _
      grind [ih₂.multiApp M N (s :: P)]

/-- The `entails_context` predicate ensures that each variable in the context
    is mapped to a term in the corresponding semantic map. -/
abbrev entails_context (E : Term.Env Var) (Γ : Context Var (Ty Base)) :=
  ∀ {x τ}, ⟨x, τ⟩ ∈ Γ → (multiSubst E (fvar x)) ∈ semanticMap τ

/-- The empty context is entailed by any environment. -/
lemma entails_context_empty {Γ : Context Var (Ty Base)} : entails_context [] Γ := by
  have := semanticMap_saturated (Var := Var) (Base := Base)
  grind

open scoped Context in
omit [HasFresh Var] in
/-- The `entails_context` predicate is preserved when extending the context
    with a new variable, provided the new variable is fresh and its
    substitution is in the corresponding semantic map. -/
lemma entails_context_cons (E : Term.Env Var) (Γ : Context Var (Ty Base))
    (x : Var) (τ : Ty Base) (sub : Term Var)
    (h_fresh : x ∉ E.dom ∪ E.fv ∪ Γ.dom)
    (h_mem : sub ∈ semanticMap τ) :
    entails_context E Γ → entails_context (⟨ x, sub ⟩ :: E) (⟨ x, τ ⟩ :: Γ) := by
  grind [multiSubst_fvar_fresh, subst_fresh, multiSubst_preserves_not_fvar]

/-- The `entails` predicate states that a term `t` is
    semantically valid with respect to a context `Γ` and a type `τ` -/
abbrev entails (Γ : Context Var (Ty Base)) (t : Term Var) (τ : Ty Base) :=
    ∀ E, env_LC E → (entails_context E Γ) → (multiSubst E t) ∈ semanticMap τ

/-- The `soundness` lemma states that if a term `t` has type `τ` in context `Γ`,
    then `t` is semantically valid with respect to `Γ` and `τ` -/
lemma soundness {Γ : Context Var (Ty Base)} (derivation_t : Γ ⊢ t ∶ τ) : entails Γ t τ := by
  induction derivation_t with
  | var Γ xσ_mem_Γ => grind
  | @abs σ Γ t τ L HL IH =>
    intro E _ _ s
    have sat_semMap_σ := semanticMap_saturated (Var := Var) σ
    have sat_semMap_τ := semanticMap_saturated (Var := Var) τ
    have := sat_semMap_τ.multiApp (multiSubst E t) s []
    let := multiSubst E t
    have ⟨x, _⟩ := fresh_exists <| E.dom ∪ free_union [fv, Context.dom, Env.fv] Var
    have := IH (x := x) (E := ⟨x,s⟩ :: E)
    grind [multiSubst_abs, entails_context_cons, multiSubst_open_var]
  | app => grind [multiSubst_app]

/-- Using soundness and the fact that the empty context
    is entailed by any environment, we can conclude that
    a well-typed term is strongly normalizing. -/
theorem strong_norm {t : Term Var} {τ : Ty Base} (der : Γ ⊢ t ∶ τ) : SN t := by
  apply (semanticMap_saturated τ).sn
  apply (soundness der [] (by grind) entails_context_empty)

end LambdaCalculus.LocallyNameless.Stlc

end Cslib
