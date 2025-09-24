/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

import Cslib.Languages.LambdaCalculus.LocallyNameless.Fsub.WellFormed
import Cslib.Languages.LambdaCalculus.LocallyNameless.Fsub.Subtype
import Cslib.Languages.LambdaCalculus.LocallyNameless.Fsub.Reduction

/-! # λ-calculus

The λ-calculus with polymorphism and subtyping, with a locally nameless representation of syntax.
This file defines the typing relation.

## References

* [A. Chargueraud, *The Locally Nameless Representation*][Chargueraud2012]
* See also <https://www.cis.upenn.edu/~plclub/popl08-tutorial/code/>, from which
  this is adapted

-/

universe u

variable {Var : Type u} [DecidableEq Var] [HasFresh Var]

namespace LambdaCalculus.LocallyNameless.Fsub

open Term Ty Ty.Wf Env.Wf Sub Context List

/-- The typing relation. -/
inductive Typing : Env Var → Term Var → Ty Var → Prop
  | var : Γ.Wf → Binding.ty σ ∈ Γ.dlookup x → Typing Γ (fvar x) σ
  | abs (L : Finset Var) :
      (∀ x ∉ L, Typing (⟨x, Binding.ty σ⟩ :: Γ) (t₁ ^ᵗᵗ fvar x) τ) →
      Typing Γ (abs σ t₁) (arrow σ τ)
  | app : Typing Γ t₁ (arrow σ τ) → Typing Γ t₂ σ → Typing Γ (app t₁ t₂) τ
  | tabs (L : Finset Var) :
      (∀ X ∉ L, Typing (⟨X, Binding.sub σ⟩ :: Γ) (t₁ ^ᵗᵞ fvar X) (τ ^ᵞ fvar X)) →
      Typing Γ (tabs σ t₁) (all σ τ)
  | tapp : Typing Γ t₁ (all σ τ) → Sub Γ σ' σ → Typing Γ (tapp t₁ σ') (τ ^ᵞ σ')
  | sub : Typing Γ t τ → Sub Γ τ τ' → Typing Γ t τ'
  | let' (L : Finset Var) :
      Typing Γ t₁ σ →
      (∀ x ∉ L, Typing (⟨x, Binding.ty σ⟩ :: Γ) (t₂ ^ᵗᵗ fvar x) τ) →
      Typing Γ (let' t₁ t₂) τ
  | inl : Typing Γ t₁ σ → τ.Wf Γ → Typing Γ (inl t₁) (sum σ τ)
  | inr : Typing Γ t₁ τ → σ.Wf Γ → Typing Γ (inr t₁) (sum σ τ)
  | case (L : Finset Var) :
      Typing Γ t₁ (sum σ τ) →
      (∀ x ∉ L, Typing (⟨x, Binding.ty σ⟩ :: Γ) (t₂ ^ᵗᵗ fvar x) δ) →
      (∀ x ∉ L, Typing (⟨x, Binding.ty τ⟩ :: Γ) (t₃ ^ᵗᵗ fvar x) δ) →
      Typing Γ (case t₁ t₂ t₃) δ

namespace Typing

variable {Γ Δ Θ : Env Var} {σ τ δ : Ty Var}

attribute [grind] Typing.var Typing.app Typing.tapp Typing.sub Typing.inl Typing.inr

/-- Typings have well-formed contexts and types. -/
@[grind →]
lemma wf {Γ : Env Var} {t : Term Var} {τ : Ty Var} (der : Typing Γ t τ) :
    Γ.Wf ∧ t.LC ∧ τ.Wf Γ := by
  induction der
  case tabs => 
    let ⟨X,mem⟩ := fresh_exists <| free_union Var
    split_ands
    · grind [cases Env.Wf]
    · apply LC.tabs (free_union Var) <;> grind [cases Env.Wf]
    · apply Ty.Wf.all (free_union Var) <;> grind [cases Env.Wf]
  case abs σ Γ _ _ _ _ _ => 
    let ⟨X,_⟩ := fresh_exists <| free_union Var
    split_ands
    · grind [cases Env.Wf]
    · apply LC.abs (free_union Var) <;> grind [cases Env.Wf]
    · have eq : ⟨X, Binding.ty σ⟩ :: Γ = [] ++ [⟨X, Binding.ty σ⟩] ++ Γ := by rfl
      grind [Ty.Wf.strengthen, cases Env.Wf]
  case let' Γ _ σ _ _ _ _ _ _ _ => 
    let ⟨X,_⟩ := fresh_exists <| free_union Var
    split_ands
    · grind
    · apply LC.let' (free_union Var) <;> grind
    · have eq : ⟨X, Binding.ty σ⟩ :: Γ = [] ++ [⟨X, Binding.ty σ⟩] ++ Γ := by rfl
      grind [Ty.Wf.strengthen]
  case case Γ _ σ _ _ _ _ _ _ _ _ _ _ _ => 
    let ⟨X,_⟩ := fresh_exists <| free_union Var
    split_ands
    · grind
    · apply LC.case (free_union Var) <;> grind
    · have eq : ⟨X, Binding.ty σ⟩ :: Γ = [] ++ [⟨X, Binding.ty σ⟩] ++ Γ := by rfl
      grind [Ty.Wf.strengthen]
  all_goals grind [of_bind_ty, open_lc, cases Env.Wf, cases Ty.Wf]

/-- Weakening of typings. -/
lemma weaken (der : Typing (Γ ++ Δ) t τ) (wf : (Γ ++ Θ ++ Δ).Wf) : 
    Typing (Γ ++ Θ ++ Δ) t τ := by
  generalize eq : Γ ++ Δ = ΓΔ at der
  induction der generalizing Γ
  case' abs  => apply Typing.abs  ((Γ ++ Θ ++ Δ).dom ∪ free_union Var)
  case' tabs => apply Typing.tabs ((Γ ++ Θ ++ Δ).dom ∪ free_union Var)
  case' let' der _ => apply Typing.let' ((Γ ++ Θ ++ Δ).dom ∪ free_union Var) (der wf eq)
  case' case der _ _ => apply Typing.case ((Γ ++ Θ ++ Δ).dom ∪ free_union Var) (der wf eq)
  all_goals 
    grind [Wf.weaken, Sub.weaken, Wf.of_env_ty, Wf.of_env_sub, Sub.refl, sublist_dlookup]

/-- Narrowing of typings. -/
lemma narrow (sub : Sub Δ δ δ') (der : Typing (Γ ++ ⟨X, Binding.sub δ'⟩ :: Δ) t τ) :
    Typing (Γ ++ ⟨X, Binding.sub δ⟩ :: Δ) t τ := sorry

/-- Term substitution within a typing. -/
lemma subst_tm (der : Typing (Γ ++ ⟨X, Binding.ty σ⟩ :: Δ) t τ) (der_sub : Typing Δ s σ) :
    Typing (Γ ++ Δ) (t[X := s]) τ := sorry

/-- Type substitution within a typing. -/
lemma subst_ty (der : Typing (Γ ++ ⟨X, Binding.sub δ'⟩ :: Δ) t τ) (sub : Sub Δ δ δ') : 
    Typing (Γ.map_val (·[X := δ]) ++ Δ) (t[X := δ]) (τ[X := δ]) := sorry

open Term Ty

omit [HasFresh Var]

/-- Invert the typing of an abstraction. -/
lemma abs_inv (der : Typing Γ (.abs γ' t) τ) (sub : Sub Γ τ (arrow γ δ)) :
     Sub Γ γ γ'
  ∧ ∃ δ' L, ∀ x ∉ (L : Finset Var), 
    Typing (⟨x, Binding.ty γ'⟩ :: Γ) (t ^ᵗᵗ .fvar x) δ' ∧ Sub Γ δ' δ := by
  generalize eq : Term.abs γ' t = e at der
  induction der generalizing t γ' γ δ
  case abs τ L _ _ => 
    cases eq
    cases sub
    split_ands
    · assumption
    · exists τ, L
      grind
  case sub Γ _ τ τ' _ _ ih => 
    subst eq
    have sub' : Sub Γ τ (γ.arrow δ) := by grind
    obtain ⟨_, δ', L, _⟩ := ih sub' (by rfl)
    split_ands
    · assumption
    · exists δ', L
  all_goals grind

variable [HasFresh Var] in
/-- Invert the typing of a type abstraction. -/
lemma tabs_inv (der : Typing Γ (.tabs γ' t) τ) (sub : Sub Γ τ (all γ δ)) :
     Sub Γ γ γ'
  ∧ ∃ δ' L, ∀ X ∉ (L : Finset Var),
     Typing (⟨X, Binding.sub γ⟩ :: Γ) (t ^ᵗᵞ fvar X) (δ' ^ᵞ fvar X)
     ∧ Sub (⟨X, Binding.sub γ⟩ :: Γ) (δ' ^ᵞ fvar X) (δ ^ᵞ fvar X) := by
  generalize eq : Term.tabs γ' t = e at der
  induction der generalizing γ δ t γ'
  case tabs σ Γ _ τ L der _ =>
    cases sub with | all L' sub => 
    split_ands
    · grind
    · exists τ, L ∪ L'
      intro X _
      have eq : ⟨X, Binding.sub γ⟩ :: Γ = [] ++ ⟨X, Binding.sub γ⟩ :: Γ := by rfl
      grind [Typing.narrow]
  case sub Γ _ τ τ' _ _ ih => 
    subst eq
    have sub' : Sub Γ τ (γ.all δ) := by trans τ' <;> grind
    obtain ⟨_, δ', L, _⟩ := ih sub' (by rfl)
    split_ands
    · assumption
    · exists δ', L
  all_goals grind

/-- Invert the typing of a left case. -/
lemma inl_inv (der : Typing Γ (.inl t) τ) (sub : Sub Γ τ (sum γ δ)) :
    ∃ γ', Typing Γ t γ' ∧ Sub Γ γ' γ := by
  generalize eq : t.inl =t at der
  induction der generalizing γ δ <;> grind [cases Sub]

/-- Invert the typing of a right case. -/
lemma inr_inv (der : Typing Γ (.inr t) T) (sub : Sub Γ T (sum γ δ)) :
    ∃ δ', Typing Γ t δ' ∧ Sub Γ δ' δ := by
  generalize eq : t.inr =t at der
  induction der generalizing γ δ <;> grind [cases Sub]

/-- A value that types as a function is an abstraction. -/
lemma canonical_form_abs (val : Value t) (der : Typing [] t (arrow σ τ)) :
    ∃ δ t', t = .abs δ t' := by
  generalize eq  : σ.arrow τ = γ at der
  generalize eq' : [] = Γ at der
  induction der generalizing σ τ <;> grind [cases Sub, cases Value]

/-- A value that types as a quantifier is a type abstraction. -/
lemma canonical_form_tabs (val : Value t) (der : Typing [] t (all σ τ)) :
    ∃ δ t', t = .tabs δ t' := by
  generalize eq  : σ.all τ = γ at der
  generalize eq' : [] = Γ at der
  induction der generalizing σ τ <;> grind [cases Sub, cases Value]

/-- A value that types as a sum is a left or right case. -/
lemma canonical_form_sum (val : Value t) (der : Typing [] t (sum σ τ)) :
    ∃ t', t = .inl t' ∨ t = .inr t' := by
  generalize eq  : σ.sum τ = γ at der
  generalize eq' : [] = Γ at der
  induction der generalizing σ τ <;> grind [cases Sub, cases Value]

end Typing

end LambdaCalculus.LocallyNameless.Fsub
