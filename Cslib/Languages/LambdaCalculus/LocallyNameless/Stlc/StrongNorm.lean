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
abbrev saturated (S : Set (Term Var)) : Prop :=
          (∀ M ∈ S, LC M) ∧
          (∀ M ∈ S, SN M) ∧
          (∀ M, Neutral M → LC M → M ∈ S) ∧
          (∀ M N P, LC N →
                    SN N →
                    multiApp (M ^ N) P ∈ S →
                      multiApp ((Term.abs M).app N) P ∈ S)

/-- The semantic map maps each type to a corresponding saturated set of terms.
    For the strong normalization proof to work, we must ensure that
    Γ ⊢ t ∶ τ implies that t is in the set of terms corresponding to τ.

    Strong normalization later follows from the fact that terms in saturated
    sets are strongly normalizing.
-/
@[simp, grind]
def semanticMap (τ : Ty Base) : Set (Term Var) :=
  match τ with
  | Ty.base _ => { t : Term Var | SN t ∧ LC t }
  | Ty.arrow τ₁ τ₂ =>
    { t : Term Var | ∀ s : Term Var, s ∈ semanticMap τ₁ → (Term.app t s) ∈ semanticMap τ₂ }


/-- The sets constructed by semanticMap are saturated -/
lemma semanticMap_saturated (τ : Ty Base) :
    @saturated Var (semanticMap τ) := by
  induction τ
  · case base b => grind[sn_abs_app_multiApp, sn_neutral, multiApp_lc, open_abs_lc]
  · case arrow τ₁ τ₂ ih₁ ih₂ =>
      constructor
      · intro M hM
        have H := ih₁.2.2.1 (.fvar (fresh {})) (.fvar (fresh {})) (.fvar (fresh {}))
        specialize (hM (fvar (fresh {})) H)
        apply (ih₂.1) at hM
        cases hM
        assumption
      · constructor
        · intro M hM
          apply sn_app_left M (Term.fvar (fresh {})) <;> grind
        · constructor
          · grind
          · intro M N P lc_N sn_N h_app s hs
            apply ih₂.2.2.2 M N (s::P) <;> grind




/-- The `entails_context` predicate ensures that each variable in the context
    is mapped to a term in the corresponding semantic map. -/
abbrev entails_context (E : Term.Env Var) (Γ : Context Var (Ty Base)) :=
  ∀ {x τ}, ⟨ x, τ ⟩ ∈ Γ → (multiSubst E (Term.fvar x)) ∈ semanticMap τ

/-- The empty context is entailed by any environment. -/
lemma entails_context_empty {Γ : Context Var (Ty Base)} :
  entails_context [] Γ := by
  intro x τ h_mem
  have Hsat := (@semanticMap_saturated Var Base _ _ τ)
  grind

omit [HasFresh Var] in
/-- The `entails_context` predicate is preserved when extending the context
    with a new variable, provided the new variable is fresh and its
    substitution is in the corresponding semantic map. -/
lemma entails_context_cons (E : Term.Env Var) (Γ : Context Var (Ty Base))
  (x : Var) (τ : Ty Base) (sub : Term Var)
  (h_fresh : x ∉ E.dom ∪ E.fv ∪ Γ.dom)
  (h_mem : sub ∈ semanticMap τ) :
    entails_context E Γ → entails_context (⟨ x, sub ⟩ :: E) (⟨ x, τ ⟩ :: Γ) := by
  intro h_entails y σ h_mem
  rw[multiSubst]
  rw[entails_context] at h_entails
  cases h_mem
  · case head       => grind [multiSubst_fvar_fresh]
  · case tail h_mem =>
    specialize (h_entails h_mem)
    rw [subst_fresh]
    · assumption
    · apply multiSubst_preserves_not_fvar
      apply List.mem_keys_of_mem at h_mem
      aesop

/-- The `entails` predicate states that a term `t` is
    semantically valid with respect to a context `Γ` and a type `τ` -/
abbrev entails (Γ : Context Var (Ty Base)) (t : Term Var) (τ : Ty Base) :=
    ∀ E, env_LC E → (entails_context E Γ) → (multiSubst E t) ∈ semanticMap τ

/-- The `soundness` lemma states that if a term `t` has type `τ` in context `Γ`,
    then `t` is semantically valid with respect to `Γ` and `τ` -/
lemma soundness {Γ : Context Var (Ty Base)} {t : Term Var} {τ : Ty Base}
    (derivation_t : Γ ⊢ t ∶ τ) : entails Γ t τ := by
  induction derivation_t
  · case var Γ xσ_mem_Γ => grind
  · case' abs σ Γ t τ L HL IH =>
      have sat_semMap_τ := (@semanticMap_saturated Var Base _ _ τ)
      have sat_semMap_σ := (@semanticMap_saturated Var Base _ _ σ)
      intro E lc_E hsat s hsat_s
      have ⟨x, Hfresh⟩ :=
        fresh_exists <| (t.fv ∪ L ∪ E.dom ∪ E.fv ∪ Context.dom Γ ∪ (multiSubst E t).fv)
      specialize IH x (by simp_all) (⟨x,s⟩ :: E)
      rw[multiSubst_abs]
      apply sat_semMap_τ.2.2.2 _ _ [] <;> grind[entails_context_cons, multiSubst_open_var]
  · case app derivation_t derivation_t' IH IH' => grind[multiSubst_app]

/-- Using soundness and the fact that the empty context
    is entailed by any environment, we can conclude that
    a well-typed term is strongly normalizing. -/
theorem strong_norm {t : Term Var} {τ : Ty Base} (der : Γ ⊢ t ∶ τ) : SN t := by
  apply (semanticMap_saturated τ).2.1
  apply (soundness der [] (by grind) entails_context_empty)

end LambdaCalculus.LocallyNameless.Stlc

end Cslib
