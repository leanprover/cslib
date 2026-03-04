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

@[expose] public section

/-! # Calculus of Constructions

The Calculus of Constructions

## References

* [T. Coquand, *An algorithm for type-checking dependent types*][Coquand1996]

-/

namespace Cslib

universe u

variable {Var : Type u}

namespace LambdaCalculus.LocallyNameless.Coc

/-- Syntax of locally nameless terms, with free variables over `Var`. -/
inductive Term (Var : Type u) : Type u
  /-- Bound term variables using a de-Bruijn index. -/
  | bvar : ℕ → Term Var
  /-- Free term variables. -/
  | fvar : Var → Term Var
  /-- Function application. -/
  | app : Term Var → Term Var → Term Var
  /-- Lambda abstraction. -/
  | abs : Term Var → Term Var → Term Var
  /-- Pi type. -/
  | pi : Term Var → Term Var → Term Var
  /-- Type universe. -/
  | type : Term Var
deriving DecidableEq

namespace Term

/-- Free variables. -/
def fv [DecidableEq Var] : Term Var → Finset Var
  | .bvar _ => ∅
  | .fvar z => {z}
  | .app f a => f.fv ∪ a.fv
  | .abs t b => t.fv ∪ b.fv
  | .pi t b => t.fv ∪ b.fv
  | .type => ∅

/-- Variable opening of the ith bound variable. -/
def openingRec (i : ℕ) (s : Term Var) : Term Var → Term Var
  | .bvar y => if i = y then s else (bvar y)
  | .fvar x => fvar x
  | .app f a => .app (openingRec i s f) (openingRec i s a)
  | .abs σ t₁ => abs σ (openingRec (i + 1) s t₁)
  | .pi σ t₁ => .pi σ (openingRec (i + 1) s t₁)
  | .type => .type

/-- Variable opening of the closest binding. -/
def opening (s : Term Var) : Term Var → Term Var := openingRec 0 s

@[inherit_doc]
scoped infixr:80 " ^ᵗ " => opening

/--
Capture-avoiding substitution.
`m.subst x r` replaces the free occurrences of variable `x` in `m` with `r`.
-/
def subst [DecidableEq Var] (m : Term Var) (x : Var) (r : Term Var) : Term Var :=
  match m with
  | .bvar n => .bvar n
  | .fvar z => if z = x then r else .fvar z
  | .app f a => .app (f.subst x r) (a.subst x r)
  | .abs t b => .abs (t.subst x r) (b.subst x r)
  | .pi t b => .pi (t.subst x r) (b.subst x r)
  | .type => .type

/-- `Term.subst` is a substitution for λ-terms. Gives access to the notation `m[x := n]`. -/
instance instHasSubstitutionTerm [DecidableEq Var] :
    HasSubstitution (Term Var) Var (Term Var) where
  subst := Term.subst

/-- β-equivalence. -/
inductive BetaEquiv : Term Var → Term Var → Prop
  /-- Equivalance -/
  | eq : BetaEquiv (.app (.abs A B) N) (B ^ᵗ N)
  /-- Congruence -/
  | cong : BetaEquiv B A → BetaEquiv N M → BetaEquiv (.app B N) (.app A M)

instance instHasBetaEquivTerm : HasBetaEquiv (Term Var) where
  BetaEquiv := BetaEquiv

/-- Typing judgement -/
inductive Typing [DecidableEq v] : List (v × Term v) → Term v → Term v → Prop
  /-- Variable lookup in Γ -/
  | var : ⟨x, A⟩ ∈ Γ → Typing Γ (.fvar x) A
  /-- Function application -/
  | app : Typing Γ M (.pi A B) → Typing Γ N A → Typing Γ (.app M N) (B ^ᵗ N)
  /-- Lambda abstraction -/
  | abs (ρ : Finset v) :
      Typing Γ A K →
      (∀ x ∉ ρ, Typing (⟨x, A⟩ :: Γ) (N ^ᵗ .fvar x) (B ^ᵗ .fvar x)) →
      Typing Γ (.abs A N) (.pi A B)
  /-- Pi type -/
  | pi (ρ : Finset v) :
      Typing Γ A K →
      (∀ x ∉ ρ, Typing (⟨x, A⟩ :: Γ) (B ^ᵗ .fvar x) L) →
      Typing Γ (.pi A B) L
  /-- Type universe -/
  | type : Typing Γ .type .type
  /-- β-conversion -/
  | conv : Typing Γ M A → A =β B → Typing Γ M B

end Term

end LambdaCalculus.LocallyNameless.Coc

end Cslib
