/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Languages.LambdaCalculus.LocallyNameless.Fsub.Typing

/-! # λ-calculus

The λ-calculus with polymorphism and subtyping, with a locally nameless representation of syntax.
This file proves type safety.

## References

* [A. Chargueraud, *The Locally Nameless Representation*][Chargueraud2012]
* See also <https://www.cis.upenn.edu/~plclub/popl08-tutorial/code/>, from which
  this is adapted

-/

public section

namespace Cslib

variable {Var : Type*} [HasFresh Var] [DecidableEq Var]

namespace LambdaCalculus.LocallyNameless.Fsub

open Context List Env.Wf Term Ty

variable {t : Term Var}

/-- Any reduction step preserves typing. -/
lemma Typing.preservation (der : Typing Γ t τ) (step : t ⭢βᵛ t') : Typing Γ t' τ := by
  induction der generalizing t' with
  | var => cases step
  | abs => cases step
  | tabs => cases step
  | app der₁ der₂ ih₁ ih₂ =>
    cases step with
    | appₗ _ step => exact Typing.app (ih₁ step) der₂
    | appᵣ _ step => exact Typing.app der₁ (ih₂ step)
    | @abs σ t₁ t₂ _ _ =>
      obtain ⟨sub, τ', L, h⟩ := der₁.abs_inv (Sub.refl der₁.wf.1 der₁.wf.2.2)
      obtain ⟨x, hx⟩ := fresh_exists (L ∪ t₁.fvTm)
      simp only [Finset.mem_union, not_or] at hx
      rw [openTm_substTm_intro t₁ _ hx.2]
      exact Typing.sub ((h x hx.1).1.subst_tm (Γ := []) (der₂.sub sub)) (h x hx.1).2
  | @tapp Γ t₁ σ τ σ' der sub ih =>
    cases step with
    | tapp _ step => exact Typing.tapp (ih step) sub
    | @tabs σ₀ t _ _ _ =>
      obtain ⟨_, τ', L, h⟩ := der.tabs_inv (Sub.refl der.wf.1 der.wf.2.2)
      obtain ⟨X, hX⟩ := fresh_exists (L ∪ t.fvTy ∪ τ.fv)
      simp only [Finset.mem_union, not_or] at hX
      rw [openTy_substTy_intro t σ' hX.1.2, open_subst_intro σ' hX.2]
      exact Typing.sub ((h X hX.1.1).1.subst_ty (Γ := []) sub)
        (Sub.map_subst (Γ := []) (h X hX.1.1).2 sub)
  | sub _ sub ih => exact Typing.sub (ih step) sub
  | @let' Γ t₁ σ t₂ τ L der h ih _ =>
    cases step with
    | let_bind step _ => exact Typing.let' L (ih step) h
    | let_body =>
      obtain ⟨x, hx⟩ := fresh_exists (L ∪ t₂.fvTm)
      simp only [Finset.mem_union, not_or] at hx
      rw [openTm_substTm_intro t₂ t₁ hx.2]
      exact (h x hx.1).subst_tm (Γ := []) der
  | inl _ wf ih =>
    cases step with
    | inl step => exact Typing.inl (ih step) wf
  | inr _ wf ih =>
    cases step with
    | inr step => exact Typing.inr (ih step) wf
  | @case Γ t₁ σ τ t₂ δ t₃ L der h₂ h₃ ih _ _ =>
    cases step with
    | case step _ _ => exact Typing.case L (ih step) h₂ h₃
    | @case_inl t _ _ _ _ _ =>
      obtain ⟨σ', ht, sub⟩ := der.inl_inv (Sub.refl der.wf.1 der.wf.2.2)
      obtain ⟨x, hx⟩ := fresh_exists (L ∪ t₂.fvTm)
      simp only [Finset.mem_union, not_or] at hx
      rw [openTm_substTm_intro t₂ t hx.2]
      exact (h₂ x hx.1).subst_tm (Γ := []) (ht.sub sub)
    | @case_inr t _ _ _ _ _ =>
      obtain ⟨τ', ht, sub⟩ := der.inr_inv (Sub.refl der.wf.1 der.wf.2.2)
      obtain ⟨x, hx⟩ := fresh_exists (L ∪ t₃.fvTm)
      simp only [Finset.mem_union, not_or] at hx
      rw [openTm_substTm_intro t₃ t hx.2]
      exact (h₃ x hx.1).subst_tm (Γ := []) (ht.sub sub)

/-- Any typable term either has a reduction step or is a value. -/
lemma Typing.progress (der : Typing [] t τ) : t.Value ∨ ∃ t', t ⭢βᵛ t' := by
  generalize eq : [] = Γ at der
  induction der with
  | var _ mem => subst eq; simp at mem
  | abs L h _ =>
    left
    exact Value.abs (Typing.abs L h).wf.2.1
  | tabs L h _ =>
    left
    exact Value.tabs (Typing.tabs L h).wf.2.1
  | app der₁ der₂ ih₁ ih₂ =>
    subst eq
    right
    rcases ih₁ rfl with val₁ | ⟨t₁', step⟩
    · rcases ih₂ rfl with val₂ | ⟨t₂', step⟩
      · obtain ⟨σ, t, rfl⟩ := der₁.canonical_form_abs val₁
        exact ⟨_, Red.abs val₁.lc val₂⟩
      · exact ⟨_, Red.appᵣ val₁ step⟩
    · exact ⟨_, Red.appₗ der₂.wf.2.1 step⟩
  | tapp der sub ih =>
    subst eq
    right
    rcases ih rfl with val | ⟨t', step⟩
    · obtain ⟨σ, t, rfl⟩ := der.canonical_form_tabs val
      exact ⟨_, Red.tabs val.lc (Sub.wf _ _ _ sub).2.1.lc⟩
    · exact ⟨_, Red.tapp (Sub.wf _ _ _ sub).2.1.lc step⟩
  | sub _ _ ih => exact ih eq
  | let' L der h ih _ =>
    subst eq
    have body := fun x hx => (h x hx).wf.2.1
    right
    rcases ih rfl with val | ⟨t', step⟩
    · exact ⟨_, Red.let_body val ⟨L, body⟩⟩
    · exact ⟨_, Red.let_bind step ⟨L, body⟩⟩
  | inl _ _ ih =>
    rcases ih eq with val | ⟨t', step⟩
    · exact Or.inl (Value.inl val)
    · exact Or.inr ⟨_, Red.inl step⟩
  | inr _ _ ih =>
    rcases ih eq with val | ⟨t', step⟩
    · exact Or.inl (Value.inr val)
    · exact Or.inr ⟨_, Red.inr step⟩
  | case L der h₂ h₃ ih _ _ =>
    subst eq
    have body₂ := fun x hx => (h₂ x hx).wf.2.1
    have body₃ := fun x hx => (h₃ x hx).wf.2.1
    right
    rcases ih rfl with val | ⟨t', step⟩
    · obtain ⟨t, heq | heq⟩ := der.canonical_form_sum val
      · subst heq
        cases val with
        | inl val => exact ⟨_, Red.case_inl val ⟨L, body₂⟩ ⟨L, body₃⟩⟩
      · subst heq
        cases val with
        | inr val => exact ⟨_, Red.case_inr val ⟨L, body₂⟩ ⟨L, body₃⟩⟩
    · exact ⟨_, Red.case step ⟨L, body₂⟩ ⟨L, body₃⟩⟩

end LambdaCalculus.LocallyNameless.Fsub

end Cslib
