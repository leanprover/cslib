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
inductive saturated (S : Set (Term Var)) : Prop where
| intro : (∀ M ∈ S, LC M) →
          (∀ M ∈ S, SN M) →
          (∀ M, neutral M → LC M → M ∈ S) →
          (∀ M N P, LC N →
                    SN N →
                    multiApp (M ^ N) P ∈ S →
                      multiApp ((Term.abs M).app N) P ∈ S) →
            saturated S

/-- The semantic map maps each type to a corresponding saturated set of terms.
    For the strong normalization proof to work, we must ensure that
    Γ ⊢ t ∶ τ implies that t is in the set of terms corresponding to τ.

    Strong normalization later follows from the fact that terms in saturated
    sets are strongly normalizing.
-/
@[simp]
def semanticMap (τ : Ty Base) : Set (Term Var) :=
  match τ with
  | Ty.base _ => { t : Term Var | SN t ∧ LC t }
  | Ty.arrow τ₁ τ₂ =>
    { t : Term Var | ∀ s : Term Var, s ∈ semanticMap τ₁ → (Term.app t s) ∈ semanticMap τ₂ }


/-- The sets constructed by semanticMap are saturated -/
def semanticMap_saturated (τ : Ty Base) :
    @saturated Var (semanticMap τ) := by
  induction τ
  · case base b =>
      constructor
      · simp_all
      · simp_all
      · simp_all[sn_neutral]
      · intro M N P lc_N sn_N h_app
        constructor
        · simp_all[sn_multiApp]
        · have H := h_app.2
          rw[multiApp_lc] at *
          grind[open_abs_lc]
  · case arrow τ₁ τ₂ ih₁ ih₂ =>
      constructor
      · intro M hM
        have H := ih₁.3 (.fvar (fresh {})) (.fvar (fresh {})) (.fvar (fresh {}))
        specialize (hM (fvar (fresh {})) H)
        apply (ih₂.1) at hM
        cases hM
        assumption
      · intro M hM
        apply sn_app_left M (Term.fvar (fresh {}))
        · constructor
        · have H := ih₁.3 (.fvar (fresh {})) (.fvar (fresh {})) (.fvar (fresh {}))
          specialize (hM (fvar (fresh {})) H)
          apply ih₂.2 ; assumption
      · intro M hneut mlc s hs
        apply ih₂.3
        · constructor
          · assumption
          · apply ih₁.2
            assumption
        · constructor
          · assumption
          · apply ih₁.1
            assumption
      · intro M N P lc_N sn_N h_app s hs
        apply ih₂.4 M N (s::P)
        · apply lc_N
        · apply sn_N
        · apply h_app
          assumption




/-- The `entails_context` predicate ensures that each variable in the context
    is mapped to a term in the corresponding semantic map. -/
def entails_context (E : Term.Environment Var) (Γ : Context Var (Ty Base)) :=
  ∀ {x τ}, ⟨ x, τ ⟩ ∈ Γ → (multiSubst E (Term.fvar x)) ∈ semanticMap τ

/-- The empty context is entailed by any environment. -/
lemma entails_context_empty {Γ : Context Var (Ty Base)} :
  entails_context [] Γ := by
  intro x τ h_mem
  rw[multiSubst]
  apply (semanticMap_saturated τ).3 <;> constructor

omit [HasFresh Var] in
/-- The `entails_context` predicate is preserved when extending the context
    with a new variable, provided the new variable is fresh and its
    substitution is in the corresponding semantic map. -/
lemma entails_context_cons (E : Term.Environment Var) (Γ : Context Var (Ty Base))
  (x : Var) (τ : Ty Base) (sub : Term Var) :
  x ∉ E.dom ∪ E.fv ∪ Γ.dom →
  sub ∈ semanticMap τ →
  entails_context E Γ → entails_context (⟨ x, sub ⟩ :: E) (⟨ x, τ ⟩ :: Γ) := by
  intro h_fresh h_mem h_entails y σ h_mem
  rw[multiSubst]
  rw[entails_context] at h_entails
  cases h_mem
  · case head =>
    rw[multiSubst_fvar_fresh]
    · rw[subst_fvar]
      simp_all
    · simp_all
  · case tail h_mem =>
    specialize (h_entails h_mem)
    rw [subst_fresh]
    · assumption
    · apply multiSubst_preserves_not_fvar
      apply List.mem_keys_of_mem at h_mem
      aesop

/-- The `entails` predicate states that a term `t` is
    semantically valid with respect to a context `Γ` and a type `τ` -/
def entails (Γ : Context Var (Ty Base)) (t : Term Var) (τ : Ty Base) :=
  ∀ E, env_LC E → (entails_context E Γ) → (multiSubst E t) ∈ semanticMap τ

/-- The `soundness` lemma states that if a term `t` has type `τ` in context `Γ`,
    then `t` is semantically valid with respect to `Γ` and `τ` -/
lemma soundness {Γ : Context Var (Ty Base)} {t : Term Var} {τ : Ty Base} :
  Γ ⊢ t ∶ τ → entails Γ t τ := by
  intro derivation_t
  induction derivation_t
  · case var Γ xσ_mem_Γ =>
      intro E lc_E hsat
      apply hsat xσ_mem_Γ
  · case' abs σ Γ t τ L IH derivation_t =>
      intro E lc_E hsat s hsat_s
      rw[multiSubst_abs]
      apply (semanticMap_saturated _).4 _ _ []
      · apply (semanticMap_saturated _).1
        assumption
      · apply (semanticMap_saturated _).2
        assumption
      · rw[multiApp]
        set x := fresh (t.fv ∪ L ∪ E.dom ∪ E.fv ∪ Context.dom Γ ∪ (multiSubst E t).fv)
        have hfresh : x ∉ t.fv ∪ L ∪ E.dom ∪ E.fv ∪ Context.dom Γ  ∪ (multiSubst E t).fv
          := by apply fresh_notMem
        have hfreshL : x ∉ L := by simp_all
        have H1 := derivation_t x hfreshL
        rw[entails] at H1
        specialize H1 (⟨x,s⟩ :: E)
        rw [multiSubst, multiSubst_open_var, ←subst_intro] at H1
        · apply H1
          · apply env_LC_cons
            · apply (semanticMap_saturated _).1
              assumption
            · assumption
          · apply entails_context_cons <;> simp_all
        · simp_all
        · apply (semanticMap_saturated σ).1
          assumption
        · simp_all
        · aesop
  · case app derivation_t derivation_t' IH IH' =>
      intro E lc_E hsat
      rw[multiSubst_app]
      apply IH E lc_E hsat
      apply IH' E lc_E hsat

/-- Using soundness and the fact that the empty context
    is entailed by any environment, we can conclude that
    a well-typed term is strongly normalizing. -/
theorem strong_norm {Γ} {t : Term Var} {τ : Ty Base} (der : Γ ⊢ t ∶ τ) : SN t := by
  have H := soundness der [] (by aesop) entails_context_empty
  apply (semanticMap_saturated τ).2
  assumption

end LambdaCalculus.LocallyNameless.Stlc

end Cslib
