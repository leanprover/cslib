/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.Relation.Attr
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Fsub.Opening

/-! # λ-calculus

The λ-calculus with polymorphism and subtyping, with a locally nameless representation of syntax.
This file defines a call-by-value reduction.

## References

* [A. Chargueraud, *The Locally Nameless Representation*][Chargueraud2012]
* See also <https://www.cis.upenn.edu/~plclub/popl08-tutorial/code/>, from which
  this is adapted

-/

@[expose] public section

set_option linter.unusedDecidableInType false

namespace Cslib

variable {Var : Type*}

namespace LambdaCalculus.LocallyNameless.Fsub

namespace Term

/-- Existential predicate for being a locally closed body of an abstraction. -/
def body (t : Term Var) := ∃ L : Finset Var, ∀ x ∉ L, LC (t ^ᵗᵗ fvar x)

section

variable {t₁ t₂ t₃ : Term Var}

variable [DecidableEq Var]

set_option linter.unusedSectionVars false in
/-- Locally closed let bindings have a locally closed body. -/
@[nolint unusedArguments]
lemma body_let : (let' t₁ t₂).LC ↔ t₁.LC ∧ t₂.body := by
  constructor
  · intro h
    cases h with
    | let' L t₁_lc h => exact ⟨t₁_lc, L, h⟩
  · rintro ⟨t₁_lc, L, h⟩
    exact LC.let' L t₁_lc h

/-- Locally closed case bindings have a locally closed bodies. -/
lemma body_case : (case t₁ t₂ t₃).LC ↔ t₁.LC ∧ t₂.body ∧ t₃.body := by
  constructor <;> intro h
  case mp => cases h with | case L t₁_lc h₂ h₃ => exact ⟨t₁_lc, ⟨L, h₂⟩, ⟨L, h₃⟩⟩
  case mpr =>
    obtain ⟨t₁_lc, ⟨L₂, h₂⟩, ⟨L₃, h₃⟩⟩ := h
    apply LC.case (L₂ ∪ L₃) t₁_lc
    · intro x hx
      exact h₂ x (fun h => hx (Finset.mem_union_left L₃ h))
    · intro x hx
      exact h₃ x (fun h => hx (Finset.mem_union_right L₂ h))

variable [HasFresh Var]

/-- Opening a body preserves local closure. -/
lemma open_tm_body (body : t₁.body) (lc : t₂.LC) : (t₁ ^ᵗᵗ t₂).LC := by
  obtain ⟨L, h⟩ := body
  obtain ⟨x, hx⟩ := fresh_exists (L ∪ t₁.fvTm)
  simp only [Finset.mem_union, not_or] at hx
  rw [openTm_substTm_intro t₁ t₂ hx.2]
  exact substTm_lc (h x hx.1) lc x

end

/-- Values are irreducible terms. -/
inductive Value : Term Var → Prop
  | abs : LC (abs σ t₁) → Value (abs σ t₁)
  | tabs : LC (tabs σ t₁) → Value (tabs σ t₁)
  | inl : Value t₁ → Value (inl t₁)
  | inr : Value t₁ → Value (inr t₁)

lemma Value.lc {t : Term Var} (val : t.Value) : t.LC := by
  induction val with
  | abs lc | tabs lc => exact lc
  | inl _ ih => exact LC.inl ih
  | inr _ ih => exact LC.inr ih

/-- The call-by-value reduction relation. -/
@[reduction_sys "βᵛ"]
inductive Red : Term Var → Term Var → Prop
  | appₗ : LC t₂ → Red t₁ t₁' → Red (app t₁ t₂) (app t₁' t₂)
  | appᵣ : Value t₁ → Red t₂ t₂' → Red (app t₁ t₂) (app t₁ t₂')
  | tapp : σ.LC → Red t₁ t₁' → Red (tapp t₁ σ) (tapp t₁' σ)
  | abs : LC (abs σ t₁) → Value t₂ → Red (app (abs σ t₁) t₂) (t₁ ^ᵗᵗ t₂)
  | tabs : LC (tabs σ t₁) → τ.LC → Red (tapp (tabs σ t₁) τ) (t₁ ^ᵗᵞ τ)
  | let_bind : Red t₁ t₁' → t₂.body → Red (let' t₁ t₂) (let' t₁' t₂)
  | let_body : Value t₁ → t₂.body → Red (let' t₁ t₂) (t₂ ^ᵗᵗ t₁)
  | inl : Red t₁ t₁' → Red (inl t₁) (inl t₁')
  | inr : Red t₁ t₁' → Red (inr t₁) (inr t₁')
  | case : Red t₁ t₁' → t₂.body → t₃.body → Red (case t₁ t₂ t₃) (case t₁' t₂ t₃)
  | case_inl : Value t₁ → t₂.body → t₃.body → Red (case (inl t₁) t₂ t₃) (t₂ ^ᵗᵗ t₁)
  | case_inr : Value t₁ → t₂.body → t₃.body → Red (case (inr t₁) t₂ t₃) (t₃ ^ᵗᵗ t₁)

variable [HasFresh Var] [DecidableEq Var] in
/-- Terms of a reduction are locally closed. -/
lemma Red.lc {t t' : Term Var} (red : t ⭢βᵛ t') : t.LC ∧ t'.LC := by
  induction red with
  | appₗ lc _ ih => exact ⟨LC.app ih.1 lc, LC.app ih.2 lc⟩
  | appᵣ val _ ih => exact ⟨LC.app val.lc ih.1, LC.app val.lc ih.2⟩
  | tapp lc _ ih => exact ⟨LC.tapp ih.1 lc, LC.tapp ih.2 lc⟩
  | abs lc val =>
    refine ⟨LC.app lc val.lc, ?_⟩
    cases lc with
    | abs L _ h => exact open_tm_body ⟨L, h⟩ val.lc
  | @tabs σ t τ lc τ_lc =>
    refine ⟨LC.tapp lc τ_lc, ?_⟩
    cases lc with
    | tabs L _ h =>
      obtain ⟨X, hX⟩ := fresh_exists (L ∪ t.fvTy)
      simp only [Finset.mem_union, not_or] at hX
      rw [openTy_substTy_intro t τ hX.2]
      exact substTy_lc (h X hX.1) τ_lc X
  | let_bind _ body ih =>
    exact ⟨body_let.mpr ⟨ih.1, body⟩, body_let.mpr ⟨ih.2, body⟩⟩
  | let_body val body =>
    exact ⟨body_let.mpr ⟨val.lc, body⟩, open_tm_body body val.lc⟩
  | inl _ ih => exact ⟨LC.inl ih.1, LC.inl ih.2⟩
  | inr _ ih => exact ⟨LC.inr ih.1, LC.inr ih.2⟩
  | case _ body₂ body₃ ih =>
    exact ⟨body_case.mpr ⟨ih.1, body₂, body₃⟩, body_case.mpr ⟨ih.2, body₂, body₃⟩⟩
  | case_inl val body₂ body₃ =>
    exact ⟨body_case.mpr ⟨LC.inl val.lc, body₂, body₃⟩, open_tm_body body₂ val.lc⟩
  | case_inr val body₂ body₃ =>
    exact ⟨body_case.mpr ⟨LC.inr val.lc, body₂, body₃⟩, open_tm_body body₃ val.lc⟩

end Term

end LambdaCalculus.LocallyNameless.Fsub

end Cslib
