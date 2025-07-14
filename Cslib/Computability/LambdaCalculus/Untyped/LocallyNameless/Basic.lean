/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

import Cslib.Data.HasFresh

/-! # λ-calculus

The untyped λ-calculus, with a locally nameless representation of syntax.

## References

* [A. Chargueraud, *The Locally Nameless Representation*] [Chargueraud2012]
* See also https://www.cis.upenn.edu/~plclub/popl08-tutorial/code/, from which
  this is partially adapted

-/

universe u

variable {Var : Type u} [HasFresh Var] [DecidableEq Var]

namespace LambdaCalculus.LocallyNameless

/-- Syntax of locally nameless absbda terms, with free variables over `Var`. -/
inductive Term (Var : Type u)
/-- Bound variables that appear under a absbda abstraction, using a de-Bruijn index. -/
| bvar : ℕ → Term Var
/-- Free variables. -/
| fvar : Var → Term Var
/-- Lambda abstraction, introducing a new bound variable. -/
| abs  : Term Var → Term Var
/-- Function application. -/
| app  : Term Var → Term Var → Term Var

/-- Variable opening of the ith bound variable. -/
@[simp]
def Term.openRec (i : ℕ) (sub : Term Var) : Term Var → Term Var
| bvar i' => if i = i' then sub else bvar i'
| fvar x  => fvar x
| app l r => app (openRec i sub l) (openRec i sub r)
| abs M   => abs $ openRec (i+1) sub M

scoped notation:68 e "⟦" i " ↝ " sub "⟧"=> Term.openRec i sub e 

/-- Variable opening of the closest binding. -/
@[simp]
def Term.open' {X} (e u):= @Term.openRec X 0 u e

infixr:80 " ^ " => Term.open'

/-- Variable closing, replacing a free `fvar x` with `bvar k` -/
@[simp]
def Term.closeRec (k : ℕ) (x : Var) : Term Var → Term Var
| fvar x' => if x = x' then bvar k else fvar x'
| bvar i  => bvar i
| app l r => app (closeRec k x l) (closeRec k x r)
| abs t   => abs $ closeRec (k+1) x t

scoped notation:68 e "⟦" k " ↜ " x "⟧"=> Term.closeRec k x e 

/-- Variable closing of the closest binding. -/
@[simp]
def Term.close {Var} [DecidableEq Var] (e u):= @Term.closeRec Var _ 0 u e

infixr:80 " ^* " => Term.close

/- Substitution of a free variable to a term. -/
@[simp]
def Term.subst (m : Term Var) (x : Var) (sub : Term Var) : Term Var :=
  match m with
  | bvar i  => bvar i
  | fvar x' => if x = x' then sub else fvar x'
  | app l r => app (l.subst x sub) (r.subst x sub)
  | abs M   => abs $ M.subst x sub

scoped notation:67 e "[" x ":=" sub "]" => Term.subst e x sub

/-- Free variables of a term. -/
@[simp]
def Term.fv : Term Var → Finset Var
| bvar _ => {}
| fvar x => {x}
| abs e1 => e1.fv
| app l r => l.fv ∪ r.fv

/-- Locally closed terms. -/
inductive Term.LC : Term Var → Prop
| fvar (x)  : LC (fvar x)
| abs (L : Finset Var) (e : Term Var) : (∀ x : Var, x ∉ L → LC (e ^ fvar x)) → LC (abs e)
| app {l r} : l.LC → r.LC → LC (app l r)
