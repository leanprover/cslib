/-
Copyright (c) 2026 Matt Hunzinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Hunzinger
-/

module

public import Cslib.Foundations.Data.HasFresh
public import Cslib.Foundations.Syntax.HasAlphaEquiv
public import Cslib.Foundations.Syntax.HasBetaEquiv
public import Cslib.Foundations.Syntax.HasSubstitution
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Coc.WellFormed

@[expose] public section

/-! # Calculus of Constructions

The Calculus of Constructions

## References

* [T. Coquand, *An algorithm for type-checking dependent types*][Coquand1996]

-/

namespace Cslib

universe u

namespace LambdaCalculus.LocallyNameless.Coc

open Term

/-- β-equivalence. -/
inductive BetaEquiv : Term Var → Term Var → Prop
  /-- Equivalance -/
  | eq : BetaEquiv (.app (.abs A B) N) (B ^ᵗ N)
  /-- Congruence -/
  | cong : BetaEquiv B A → BetaEquiv N M → BetaEquiv (.app B N) (.app A M)

instance instHasBetaEquivTerm : HasBetaEquiv (Term Var) where
  BetaEquiv := BetaEquiv

/-- Typing judgement -/
inductive Typing [DecidableEq Var] : Env Var → Term Var → Term Var → Prop
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
      Typing Γ A K →
      (∀ x ∉ ρ, Typing ({⟨x, A⟩} ∪ Γ) (B ^ᵗ .fvar x) L) →
      Typing Γ (.pi A B) L
  /-- Type universe -/
  | type : Typing Γ .type .type
  /-- β-conversion -/
  | conv : Typing Γ M A → A =β B → Typing Γ M B

end LambdaCalculus.LocallyNameless.Coc

end Cslib
