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

namespace LambdaCalculus.Named.Coc

/-- Syntax of terms. -/
inductive Term (Var : Type u) : Type u
  | var : Var → Term Var
  | app : Term Var → Term Var → Term Var
  | abs : Var → Term Var → Term Var → Term Var
  | pi : Var → Term Var → Term Var → Term Var
  | type : Term Var
deriving DecidableEq

namespace Term

/-- Renaming, or variable substitution. `m.rename x y` renames `x` into `y` in `m`. -/
def rename [DecidableEq Var] (m : Term Var) (x : Var) (y : Var) : Term Var := match m with
  | .var z => if z = x then .var y else .var z
  | .app f a => .app (f.rename x y) (a.rename x y)
  | .abs v t b => .abs v (t.rename x y) (b.rename x y)
  | .pi v t b => .pi v (t.rename x y) (b.rename x y)
  | .type => .type

/-- Renaming preserves size. -/
theorem rename.eq_sizeOf {m : Term Var} {x y : Var} [DecidableEq Var] :
    sizeOf (m.rename x y) = sizeOf m := by
  induction m <;> simp_all [Term.rename] ; split <;> simp_all

/-- Free variables. -/
def fv [DecidableEq Var] : Term Var → Finset Var
  | .var z => {z}
  | .app f a => f.fv ∪ a.fv
  | .abs v t b => (t.fv ∪ b.fv).erase v
  | .pi v t b => (t.fv ∪ b.fv).erase v
  | .type => ∅

/-- Bound variables. -/
def bv [DecidableEq Var] : Term Var → Finset Var
  | .var _ => ∅
  | .app f a => f.bv ∪ a.bv
  | .abs v t b => (t.bv ∪ b.bv) ∪ {v}
  | .pi v t b => (t.bv ∪ b.bv) ∪ {v}
  | .type => ∅

/-- Variable names (free and bound) in a term. -/
def vars [DecidableEq Var] (t : Term Var) : Finset Var := t.fv ∪ t.bv

/--
Capture-avoiding substitution.
`m.subst x r` replaces the free occurrences of variable `x` in `m` with `r`.
-/
def subst [DecidableEq Var] [HasFresh Var] (m : Term Var) (x : Var) (r : Term Var) : Term Var :=
  match m with
  | .var z => if z = x then r else .var z
  | .app f a => .app (f.subst x r) (a.subst x r)
  | .abs y t b =>
    if y = x then
      .abs y (t.subst x r) b
    else if y ∉ r.fv then
      .abs y (t.subst x r) (b.subst x r)
    else
      let z := HasFresh.fresh (t.vars ∪ b.vars ∪ r.vars ∪ {y})
      .abs z ((t.rename y z).subst x r) ((b.rename y z).subst x r)
  | .pi y t b =>
    if y = x then
      .pi y (t.subst x r) b
    else if y ∉ r.fv then
      .pi y (t.subst x r) (b.subst x r)
    else
      let z := HasFresh.fresh (t.vars ∪ b.vars ∪ r.vars ∪ {y})
      .pi z ((t.rename y z).subst x r) ((b.rename y z).subst x r)
  | .type => .type
  termination_by m
  decreasing_by all_goals grind [rename.eq_sizeOf]

/-- `Term.subst` is a substitution for λ-terms. Gives access to the notation `m[x := n]`. -/
instance instHasSubstitutionTerm [DecidableEq Var] [HasFresh Var] :
    HasSubstitution (Term Var) Var (Term Var) where
  subst := Term.subst

/-- β-equivalence. -/
inductive BetaEquiv [DecidableEq Var] [HasFresh Var] : Term Var → Term Var → Prop
  /-- Equivalance -/
  | eq : BetaEquiv (B [x := N]) (.app (.abs x A B) N)
  /-- Congruence -/
  | cong : BetaEquiv B A → BetaEquiv N M → BetaEquiv (.app B N) (.app A M)

instance instHasBetaEquivTerm [DecidableEq Var] [HasFresh Var] : HasBetaEquiv (Term Var) where
  BetaEquiv := BetaEquiv

/-- Typing judgement -/
inductive Typing [DecidableEq v] [HasFresh v] : List (v × Term v) → Term v → Term v → Prop
  /-- Variable lookup in Γ -/
  | var : ⟨x, A⟩ ∈ Γ → Typing Γ (.var x) A
  /-- Function application -/
  | app : Typing Γ M (.pi x A B) → Typing Γ N A → Typing Γ (.app M N) (B[x := N])
  /-- Lambda -/
  | abs : Typing Γ A K → Typing (⟨x, A⟩ :: Γ) N B → Typing Γ (.abs x A N) (.pi x A B)
  /-- Pi -/
  | pi : Typing Γ A K → Typing (⟨x, A⟩ :: Γ) B L → Typing Γ (.pi x A B) L
  /-- Type -/
  | type : Typing Γ .type .type
  /-- Conversion -/
  | conv : Typing Γ M A → A =β B → Typing Γ M B

end Term

end LambdaCalculus.Named.Coc

end Cslib
