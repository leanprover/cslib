module

import Cslib.Foundations.Data.Relation
import Cslib.Languages.LambdaCalculus.LocallyNameless.Stlc.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.StrongNorm
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LcAt
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.MultiSubst

namespace Cslib

universe u v

namespace LambdaCalculus.LocallyNameless.Stlc

open Untyped Typing LambdaCalculus.LocallyNameless.Untyped.Term

variable {Var : Type u} {Base : Type v} [DecidableEq Var] [HasFresh Var]

open LambdaCalculus.LocallyNameless.Stlc
open scoped Term



inductive saturated (S : Set (Term Var)) : Prop :=
| intro : (∀ M ∈ S, LC M) →
          (∀ M ∈ S, SN M) →
          (∀ M, neutral M → LC M → M ∈ S) →
          (∀ M N P, LC N → SN N → multiApp (M ^ N) P ∈ S → multiApp ((Term.abs M).app N) P ∈ S) →
          saturated S


@[simp]
def semanticMap (τ : Ty Base) : Set (Term Var) :=
  match τ with
  | Ty.base _ => { t : Term Var | SN t ∧ LC t }
  | Ty.arrow τ₁ τ₂ =>
    { t : Term Var | ∀ s : Term Var, s ∈ semanticMap τ₁ → (Term.app t s) ∈ semanticMap τ₂ }



def semanticMap_saturated (τ : Ty Base) :
    @saturated Var (semanticMap τ) := by
  induction τ
  · case base b =>
      constructor
      · simp_all
      · simp_all
      · simp_all[neutral_sn]
      · intro M N P lc_N sn_N h_app
        constructor
        · simp_all[multiApp_sn]
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





def entails_context (Ns : Term.Environment Var) (Γ : Context Var (Ty Base)) :=
  ∀ {x τ}, ⟨ x, τ ⟩ ∈ Γ → (multiSubst Ns (Term.fvar x)) ∈ semanticMap τ

lemma entails_context_empty {Γ : Context Var (Ty Base)} :
  entails_context [] Γ := by
  intro x τ h_mem
  rw[multiSubst]
  apply (semanticMap_saturated τ).3 <;> constructor


lemma entails_context_cons (Ns : Term.Environment Var) (Γ : Context Var (Ty Base))
  (x : Var) (τ : Ty Base) (sub : Term Var) :
  x ∉ Ns.dom ∪ Ns.fv ∪ Γ.dom →
  sub ∈ semanticMap τ →
  entails_context Ns Γ → entails_context (⟨ x, sub ⟩ :: Ns) (⟨ x, τ ⟩ :: Γ) := by
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


def entails (Γ : Context Var (Ty Base)) (t : Term Var) (τ : Ty Base) :=
  ∀ Ns, env_LC Ns → (entails_context Ns Γ) → (multiSubst Ns t) ∈ semanticMap τ


theorem soundness {Γ : Context Var (Ty Base)} {t : Term Var} {τ : Ty Base} :
  Γ ⊢ t ∶ τ → entails Γ t τ := by
  intro derivation_t
  induction derivation_t
  · case var Γ xσ_mem_Γ =>
      intro Ns lc_Ns hsat
      apply hsat xσ_mem_Γ
  · case' abs σ Γ t τ L IH derivation_t =>
      intro Ns lc_Ns hsat s hsat_s
      rw[multiSubst_abs]
      apply (semanticMap_saturated _).4 _ _ []
      · apply (semanticMap_saturated _).1
        assumption
      · apply (semanticMap_saturated _).2
        assumption
      · rw[multiApp]
        set x := fresh (t.fv ∪ L ∪ Ns.dom ∪ Ns.fv ∪ Context.dom Γ ∪ (multiSubst Ns t).fv)
        have hfresh : x ∉ t.fv ∪ L ∪ Ns.dom ∪ Ns.fv ∪ Context.dom Γ  ∪ (multiSubst Ns t).fv := by apply fresh_notMem
        have hfreshL : x ∉ L := by simp_all
        have H1 := derivation_t x hfreshL
        rw[entails] at H1
        specialize H1 (⟨x,s⟩ :: Ns)
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
      intro Ns lc_Ns hsat
      rw[multiSubst_app]
      apply IH Ns lc_Ns hsat
      apply IH' Ns lc_Ns hsat

theorem strong_norm {Γ} {t : Term Var} {τ : Ty Base} (der : Γ ⊢ t ∶ τ) : SN t := by
  have H := soundness der [] (by aesop) entails_context_empty
  apply (semanticMap_saturated τ).2
  assumption

end LambdaCalculus.LocallyNameless.Stlc

end Cslib
