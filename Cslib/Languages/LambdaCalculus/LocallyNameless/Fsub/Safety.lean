/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Languages.LambdaCalculus.LocallyNameless.Fsub.Typing

public section

/-! # λ-calculus

The λ-calculus with polymorphism and subtyping, with a locally nameless representation of syntax.
This file proves type safety.

## References

* [A. Chargueraud, *The Locally Nameless Representation*][Chargueraud2012]
* See also <https://www.cis.upenn.edu/~plclub/popl08-tutorial/code/>, from which
  this is adapted

-/

namespace Cslib

variable {Var : Type*} [HasFresh Var] [DecidableEq Var]

namespace LambdaCalculus.LocallyNameless.Fsub

open Context List Env.Wf Term Ty

variable {t : Term Var}

/-- Any reduction step preserves typing. -/
lemma Typing.preservation (der : Typing Γ t τ) (step : t ⭢βᵛ t') : Typing Γ t' τ := by
  induction der generalizing t'
  case app Γ _ σ τ _ _ _ _ _ =>
    cases step
    case appₗ | appᵣ => grind
    case abs der _ _ =>
      have sub : Sub Γ (σ.arrow τ) (σ.arrow τ) := by grind [Sub.refl]
      have ⟨_, _, ⟨_, _⟩⟩ := der.abs_inv sub
      grind [fresh_exists <| free_union [fv_tm] Var, open_tm_subst_tm_intro, subst_tm, Sub.weaken]
  case tapp Γ _ σ τ σ' _ _ _ =>
    cases step
    case tabs der _ _ =>
      have sub : Sub Γ (σ.all τ) (σ.all τ) := by grind [Sub.refl]
      have ⟨_, _, ⟨_, _⟩⟩ := der.tabs_inv sub
      have ⟨X, mem⟩ := fresh_exists <| free_union [Ty.fv, fv_ty] Var
      simp at mem
      have : Γ = (Context.map_val (·[X:=σ']) []) ++ Γ := by grind
      rw [open_ty_subst_ty_intro (X := X), open_subst_intro (X := X)] <;> grind [subst_ty]
    case tapp => grind
  case let' Γ _ _ _ _ L der _ ih₁ _ =>
    cases step
    case let_bind red₁ _ => apply Typing.let' L (ih₁ red₁); grind
    case let_body =>
      grind [fresh_exists <| free_union [fv_tm] Var, open_tm_subst_tm_intro, subst_tm]
  case case Γ _ σ τ _ _ _ L _ _ _ ih₁ _ _ =>
    have sub : Sub Γ (σ.sum τ) (σ.sum τ) := by grind [Sub.refl]
    have : Γ = [] ++ Γ := by rfl
    cases step
    case «case» red₁ _ _ => apply Typing.case L (ih₁ red₁) <;> grind
    case case_inl der _ _ =>
      have ⟨_, ⟨_, _⟩⟩ := der.inl_inv sub
      grind [fresh_exists <| free_union [fv_tm] Var, open_tm_subst_tm_intro, subst_tm]
    case case_inr der _ _ =>
      have ⟨_, ⟨_, _⟩⟩ := der.inr_inv sub
      grind [fresh_exists <| free_union [fv_tm] Var, open_tm_subst_tm_intro, subst_tm]
  all_goals grind [cases Red]

/-- Any typable term either has a reduction step or is a value. -/
lemma Typing.progress (der : Typing [] t τ) : t.Value ∨ ∃ t', t ⭢βᵛ t' := by
  generalize eq : [] = Γ at der
  have der' : Typing Γ t τ := by assumption
  induction der <;> subst eq <;> simp only [forall_const] at *
  case var mem => grind
  case app t₁ _ _ t₂ l r ih_l ih_r =>
    right
    cases ih_l l with
    | inl val_l =>
        cases ih_r r with
        | inl val_r =>
            have ⟨σ, t₁, eq⟩ := l.canonical_form_abs val_l
            exists t₁ ^ᵗᵗ t₂
            grind
        | inr red_r =>
            obtain ⟨t₂', _⟩ := red_r
            exists t₁.app t₂'
            grind
    | inr red_l =>
        obtain ⟨t₁', _⟩ := red_l
        exists t₁'.app t₂
        grind
  case tapp σ' der _ ih =>
    right
    specialize ih der
    cases ih with
    | inl val =>
        obtain ⟨_, t, _⟩ := der.canonical_form_tabs val
        exists t ^ᵗᵞ σ'
        grind
    | inr red =>
        obtain ⟨t', _⟩ := red
        exists .tapp t' σ'
        grind
  case let' t₁ σ t₂ τ L der _ _ ih =>
    right
    cases ih der with
    | inl _ =>
        exists t₂ ^ᵗᵗ t₁
        grind
    | inr red =>
        obtain ⟨t₁', _⟩ := red
        exists t₁'.let' t₂
        grind
  case inl der _ ih =>
    cases (ih der) with
    | inl val => grind
    | inr red =>
        right
        obtain ⟨t', _⟩ := red
        exists .inl t'
        grind
  case inr der _ ih =>
    cases (ih der) with
    | inl val => grind
    | inr red =>
        right
        obtain ⟨t', _⟩ := red
        exists .inr t'
        grind
  case case t₁ _ _ t₂ _ t₃ _ der _ _ _ _ ih =>
    right
    cases ih der with
    | inl val =>
        have ⟨t₁, lr⟩ := der.canonical_form_sum val
        cases lr <;> [exists t₂ ^ᵗᵗ t₁; exists t₃ ^ᵗᵗ t₁] <;> grind
    | inr red =>
        obtain ⟨t₁', _⟩ := red
        exists t₁'.case t₂ t₃
        grind
  case sub => grind
  case abs σ _ τ L _ _=>
    left
    constructor
    apply LC.abs L <;> grind [cases Env.Wf, cases Term.LC]
  case tabs L _ _=>
    left
    constructor
    apply LC.tabs L <;> grind [cases Env.Wf, cases Term.LC]

end LambdaCalculus.LocallyNameless.Fsub

end Cslib
