/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.Data.Relation
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Fsub.Opening

@[expose] public section

set_option linter.unusedDecidableInType false

/-! # λ-calculus

The λ-calculus with polymorphism and subtyping, with a locally nameless representation of syntax.
This file defines a call-by-value reduction.

## References

* [A. Chargueraud, *The Locally Nameless Representation*][Chargueraud2012]
* See also <https://www.cis.upenn.edu/~plclub/popl08-tutorial/code/>, from which
  this is adapted

-/

namespace Cslib

variable {Var : Type*}

namespace LambdaCalculus.LocallyNameless.Fsub

namespace Term

/-- Existential predicate for being a locally closed body of an abstraction. -/
@[scoped grind =]
def body (t : Term Var) := ∃ L : Finset Var, ∀ x ∉ L, LC (t ^ᵗᵗ fvar x)

section

variable {t₁ t₂ t₃ : Term Var}

variable [DecidableEq Var]

/-- Locally closed let bindings have a locally closed body. -/
@[scoped grind _=_]
lemma body_let : (let' t₁ t₂).LC ↔ t₁.LC ∧ t₂.body := by
  constructor <;> intro h <;> cases h
  case mp.let' L t₁_lc h => exact ⟨t₁_lc, L, h⟩
  case mpr.intro body =>
    obtain ⟨_, _⟩ := body
    grind [LC.let' <| free_union Var]

/-- Locally closed case bindings have a locally closed bodies. -/
@[scoped grind _=_]
lemma body_case : (case t₁ t₂ t₃).LC ↔ t₁.LC ∧ t₂.body ∧ t₃.body := by
  constructor <;> intro h
  case mp => cases h with | case L t₁_lc h₂ h₃ => exact ⟨t₁_lc, ⟨L, h₂⟩, ⟨L, h₃⟩⟩
  case mpr =>
    obtain ⟨_, ⟨_, _⟩, ⟨_, _⟩⟩ := h
    grind [LC.case <| free_union Var]

variable [HasFresh Var]

/-- Opening a body preserves local closure. -/
@[scoped grind <=]
lemma open_tm_body (body : t₁.body) (lc : t₂.LC) : (t₁ ^ᵗᵗ t₂).LC := by
  cases body
  grind [fresh_exists <| free_union [fv_tm] Var, subst_tm_lc, open_tm_subst_tm_intro]

end

/-- Values are irreducible terms. -/
@[grind]
inductive Value : Term Var → Prop
  | abs : LC (abs σ t₁) → Value (abs σ t₁)
  | tabs : LC (tabs σ t₁) → Value (tabs σ t₁)
  | inl : Value t₁ → Value (inl t₁)
  | inr : Value t₁ → Value (inr t₁)

@[grind →]
lemma Value.lc {t : Term Var} (val : t.Value) : t.LC := by
  induction val <;> grind

/-- The call-by-value reduction relation. -/
@[grind, reduction_sys "βᵛ"]
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
  induction red
  case abs lc _ | tabs lc _ =>
    split_ands
    · grind
    · cases lc
      grind [
        fresh_exists <| free_union [fv_tm, fv_ty] Var, subst_tm_lc,
        subst_ty_lc, open_tm_subst_tm_intro, open_ty_subst_ty_intro]
  all_goals grind

end Term

end LambdaCalculus.LocallyNameless.Fsub

end Cslib
