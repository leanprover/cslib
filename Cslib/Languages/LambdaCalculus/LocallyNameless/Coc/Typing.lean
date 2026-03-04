/-
Copyright (c) 2026 Matt Hunzinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Hunzinger
-/

module

public import Cslib.Foundations.Data.HasFresh
public import Cslib.Foundations.Syntax.HasAlphaEquiv
public import Cslib.Foundations.Data.Relation
public import Cslib.Foundations.Syntax.HasSubstitution
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Coc.Opening

@[expose] public section

/-! # Calculus of Constructions

The Calculus of Constructions

## References

* [T. Coquand, *An algorithm for type-checking dependent types*][Coquand1996]

* [A. Chargueraud, *The Locally Nameless Representation*][Chargueraud2012]

-/

namespace Cslib

universe u

namespace LambdaCalculus.LocallyNameless.Coc

open Term

/-- β-reduction. -/
@[reduction_sys "β"]
inductive BetaEquiv : Term Var → Term Var → Prop
  /-- β-redex: `(λ A. B) N ⟶ B ^ᵗ N`. -/
  | red : (abs A B).LC → N.LC → BetaEquiv (.app (.abs A B) N) (B ^ᵗ N)
  /-- Congruence in the function position of an application. -/
  | app₁ : t₂.LC → BetaEquiv t₁ t₁' → BetaEquiv (.app t₁ t₂) (.app t₁' t₂)
  /-- Congruence in the argument position of an application. -/
  | app₂ : t₁.LC → BetaEquiv t₂ t₂' → BetaEquiv (.app t₁ t₂) (.app t₁ t₂')
  /-- Congruence in the type annotation of an abstraction. -/
  | abs₁ : t₂.body → BetaEquiv t₁ t₁' → BetaEquiv (.abs t₁ t₂) (.abs t₁' t₂)
  /-- Congruence in the body of an abstraction. -/
  | abs₂ (ρ : Finset Var) :
      t₁.LC →
      (∀ x ∉ ρ, BetaEquiv (t₂ ^ᵗ .fvar x) (t₂' ^ᵗ .fvar x)) →
      BetaEquiv (.abs t₁ t₂) (.abs t₁ t₂')
  /-- Congruence in the domain of a pi type. -/
  | pi₁ : t₂.body → BetaEquiv t₁ t₁' → BetaEquiv (.pi t₁ t₂) (.pi t₁' t₂)
  /-- Congruence in the codomain of a pi type. -/
  | pi₂ (ρ : Finset Var) :
      t₁.LC →
      (∀ x ∉ ρ, BetaEquiv (t₂ ^ᵗ .fvar x) (t₂' ^ᵗ .fvar x)) →
      BetaEquiv (.pi t₁ t₂) (.pi t₁ t₂')

variable [DecidableEq Var]

namespace Term

/-- Well-formedness of terms. -/
inductive Wf : Env Var → Term Var → Prop
  | var : ⟨x, _⟩ ∈ Γ → Wf Γ (fvar x)
  | app : Wf Γ f → Wf Γ a → Wf Γ (app f a)
  | abs (L : Finset Var) :
      Wf Γ σ →
      (∀ X ∉ L, Wf ({⟨X,σ⟩} ∪ Γ) (τ ^ᵗ fvar X)) →
      Wf Γ (abs σ τ)
  | pi (L : Finset Var) :
      Wf Γ σ →
      (∀ X ∉ L, Wf ({⟨X,σ⟩} ∪ Γ) (τ ^ᵗ fvar X)) →
      Wf Γ (pi σ τ)
  | type : Wf Γ (type _)

end Term

mutual

/-- An environment is well-formed if it binds each variable exactly once to a well-formed type. -/
inductive Env.Wf : Env Var → Prop
  | nil : Env.Wf {}
  | cons : Env.Wf Γ → Typing Γ τ (.type i) → x ∉ Γ.dom → Env.Wf ({⟨x, τ⟩} ∪ Γ)

/-- Typing judgement -/
inductive Typing : Env Var → Term Var → Term Var → Prop
  /-- Variable lookup in Γ -/
  | var : Γ.Wf → ⟨x, A⟩ ∈ Γ → Typing Γ (.fvar x) A
  /-- Function application -/
  | app : Typing Γ M (.pi A B) → Typing Γ N A → Typing Γ (.app M N) (B ^ᵗ N)
  /-- Lambda abstraction -/
  | abs (ρ : Finset Var) :
      Typing Γ A K →
      (∀ x ∉ ρ, Typing ({⟨x, A⟩} ∪ Γ) (N ^ᵗ .fvar x) (B ^ᵗ .fvar x)) →
      Typing Γ (.abs A N) (.pi A B)
  /-- Pi type -/
  | pi (ρ : Finset Var) :
      Typing Γ A (.type k) →
      (∀ x ∉ ρ, Typing ({⟨x, A⟩} ∪ Γ) (B ^ᵗ .fvar x) (.type i)) →
      (i = k ∨ i = 0) →
      Typing Γ (.pi A B) (.type i)
  /-- Type universe -/
  | type : Typing Γ (.type s) (.type (s + 1))
  /-- β-conversion -/
  | conv : Typing Γ M A → A ↠β B → Typing Γ B (.type i) → Typing Γ M B

end

end LambdaCalculus.LocallyNameless.Coc

end Cslib
