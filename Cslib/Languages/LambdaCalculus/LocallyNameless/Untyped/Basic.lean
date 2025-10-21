/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

import Cslib.Foundations.Data.HasFresh
import Cslib.Foundations.Syntax.HasSubstitution

/-! # λ-calculus

The untyped λ-calculus, with a locally nameless representation of syntax.

## References

* [A. Chargueraud, *The Locally Nameless Representation*][Chargueraud2012]
* See also <https://www.cis.upenn.edu/~plclub/popl08-tutorial/code/>, from which
  this is partially adapted

-/

namespace Cslib

universe u

variable {Var : Type u} [HasFresh Var] [DecidableEq Var]

namespace LambdaCalculus.LocallyNameless.Untyped

/-- Syntax of locally nameless lambda terms, with free variables over `Var`. -/
inductive Term (Var : Type u)
/-- Bound variables that appear under a lambda abstraction, using a de-Bruijn index. -/
| bvar : ℕ → Term Var
/-- Free variables. -/
| fvar : Var → Term Var
/-- Lambda abstraction, introducing a new bound variable. -/
| abs  : Term Var → Term Var
/-- Function application. -/
| app  : Term Var → Term Var → Term Var

namespace Term

/-- Variable opening of the ith bound variable. -/
@[scoped grind =]
def openRec (i : ℕ) (sub : Term Var) : Term Var → Term Var
| bvar i' => if i = i' then sub else bvar i'
| fvar x  => fvar x
| app l r => app (openRec i sub l) (openRec i sub r)
| abs M   => abs <| openRec (i+1) sub M

scoped notation:68 e "⟦" i " ↝ " sub "⟧"=> Term.openRec i sub e

lemma openRec_bvar : (bvar i')⟦i ↝ s⟧ = if i = i' then s else bvar i' := by rfl

lemma openRec_fvar : (fvar x)⟦i ↝ s⟧ = fvar x := by rfl

lemma openRec_app : (app l r)⟦i ↝ s⟧ = app (l⟦i ↝ s⟧) (r⟦i ↝ s⟧) := by rfl

lemma openRec_abs : M.abs⟦i ↝ s⟧ = M⟦i + 1 ↝ s⟧.abs := by rfl

/-- Variable opening of the closest binding. -/
@[scoped grind =]
def open' {X} (e u):= @Term.openRec X 0 u e

scoped infixr:80 " ^ " => Term.open'

/-- Variable closing, replacing a free `fvar x` with `bvar k` -/
@[scoped grind =]
def closeRec (k : ℕ) (x : Var) : Term Var → Term Var
| fvar x' => if x = x' then bvar k else fvar x'
| bvar i  => bvar i
| app l r => app (closeRec k x l) (closeRec k x r)
| abs t   => abs <| closeRec (k+1) x t

scoped notation:68 e "⟦" k " ↜ " x "⟧"=> Term.closeRec k x e

variable {x : Var}

/-- Variable closing of the closest binding. -/
@[scoped grind =]
def close {Var} [DecidableEq Var] (e u):= @Term.closeRec Var _ 0 u e

scoped infixr:80 " ^* " => Term.close

/- Substitution of a free variable to a term. -/
@[scoped grind =]
def subst (m : Term Var) (x : Var) (sub : Term Var) : Term Var :=
  match m with
  | bvar i  => bvar i
  | fvar x' => if x = x' then sub else fvar x'
  | app l r => app (l.subst x sub) (r.subst x sub)
  | abs M   => abs <| M.subst x sub

/-- `Term.subst` is a substitution for λ-terms. Gives access to the notation `m[x := n]`. -/
instance instHasSubstitutionTerm : HasSubstitution (Term Var) Var (Term Var) where
  subst := Term.subst

/-- Free variables of a term. -/
@[simp, scoped grind =]
def fv : Term Var → Finset Var
| bvar _ => {}
| fvar x => {x}
| abs e1 => e1.fv
| app l r => l.fv ∪ r.fv

/-- Locally closed terms. -/
inductive LC : Term Var → Prop
| fvar (x)  : LC (fvar x)
| abs (L : Finset Var) (e : Term Var) : (∀ x ∉ L, LC (e ^ fvar x)) → LC (abs e)
| app {l r} : l.LC → r.LC → LC (app l r)

attribute [scoped grind .] LC.fvar LC.app

inductive Value : Term Var → Prop
| abs (e : Term Var) : e.abs.LC → e.abs.Value

section

omit [HasFresh Var]

lemma closeRec_bvar : (bvar i)⟦k ↜ x⟧ = bvar i := by rfl

lemma closeRec_fvar : (fvar x')⟦k ↜ x⟧ = if x = x' then bvar k else fvar x' := by rfl

lemma closeRec_app : (app l r)⟦k ↜ x⟧ = app (l⟦k ↜ x⟧) (r⟦k ↜ x⟧) := by rfl

lemma closeRec_abs : t.abs⟦k ↜ x⟧ = t⟦k + 1 ↜ x⟧.abs := by rfl

variable {x : Var} {n : Term Var}

lemma subst_bvar : (bvar i : Term Var)[x := n] = bvar i := by rfl

lemma subst_fvar : (fvar x')[x := n] = if x = x' then n else fvar x' := by rfl

lemma subst_app {l r : Term Var} : (app l r)[x := n] = app (l[x := n]) (r[x := n]) := by rfl

lemma subst_abs {M : Term Var} : M.abs[x := n] = M[x := n].abs := by rfl

lemma subst_def (m : Term Var) (x : Var) (n : Term Var) : m.subst x n = m[x := n] := by rfl

attribute [scoped grind =] subst_bvar subst_fvar subst_app subst_abs subst_def

end

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
