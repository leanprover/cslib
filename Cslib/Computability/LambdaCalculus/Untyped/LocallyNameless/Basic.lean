/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

import Cslib.Data.HasFresh

/-! # λ-calculus

The untyped λ-calculus, with a locally nameless representation of syntax.

## References

* [A. Chargueraud2012, *The Locally Nameless Representation*] [Chargueraud2012]
* See also https://www.cis.upenn.edu/~plclub/popl08-tutorial/code/, from which
  this is partially adapted

-/

universe u

variable {Var : Type u} [HasFresh Var] [DecidableEq Var]

namespace LambdaCalculus.LocallyNameless

/-- Syntax of locally nameless lambda terms, with free variables over `Var`. -/
inductive Term (Var : Type u)
| bvar : ℕ → Term Var
| fvar : Var → Term Var
| lam  : Term Var → Term Var
| app  : Term Var → Term Var → Term Var

/-- Variable opening of the ith bound variable. -/
@[simp]
def Term.open_rec (i : ℕ) (sub : Term Var) : Term Var → Term Var
| bvar i' => if i = i' then sub else bvar i'
| fvar x  => fvar x
| app l r => app (open_rec i sub l) (open_rec i sub r)
| lam M   => lam $ open_rec (i+1) sub M

scoped notation:68 e "⟦" i " ↝ " sub "⟧"=> Term.open_rec i sub e 

/-- Variable opening of the closest binding. -/
@[simp]
def Term.open' {X} (e u):= @Term.open_rec X 0 u e

infixr:80 " ^ " => Term.open'

/-- Variable closing, replacing a free `fvar x` with `bvar k` -/
@[simp]
def Term.close_rec (k : ℕ) (x : Var) : Term Var → Term Var
| fvar x' => if x = x' then bvar k else fvar x'
| bvar i  => bvar i
| app l r => app (close_rec k x l) (close_rec k x r)
| lam t   => lam $ close_rec (k+1) x t

scoped notation:68 e "⟦" k " ↜ " x "⟧"=> Term.close_rec k x e 

/-- Variable closing of the closest binding. -/
@[simp]
def Term.close {Var} [DecidableEq Var] (e u):= @Term.close_rec Var _ 0 u e

infixr:80 " ^* " => Term.close

/- Substitution of a free variable to a term. -/
@[simp]
def Term.subst (x : Var) (sub : Term Var) : Term Var → Term Var
| bvar i  => bvar i
| fvar x' => if x = x' then sub else fvar x'
| app l r => app (subst x sub l) (subst x sub r)
| lam M   => lam $ subst x sub M

scoped notation:67 e "[" x ":=" sub "]" => Term.subst x sub e 

/-- Free variables of a term. -/
@[simp]
def Term.fv : Term Var → Finset Var
| bvar _ => {}
| fvar x => {x}
| lam e1 => e1.fv
| app l r => l.fv ∪ r.fv

/-- Locally closed terms. -/
inductive Term.LC : Term Var → Prop
| fvar (x)  : LC (fvar x)
| lam (L : Finset Var) (e : Term Var) : (∀ x : Var, x ∉ L → LC (e ^ fvar x)) → LC (lam e)
| app {l r} : l.LC → r.LC → LC (app l r)
