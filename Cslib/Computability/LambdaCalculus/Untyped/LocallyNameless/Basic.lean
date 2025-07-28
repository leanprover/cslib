/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

import Cslib.Data.HasFresh
import Cslib.Syntax.HasSubstitution
import Cslib.Computability.LambdaCalculus.Untyped.LocallyNameless.AesopRuleset

/-! # λ-calculus

The untyped λ-calculus, with a locally nameless representation of syntax.

## References

* [A. Chargueraud, *The Locally Nameless Representation*][Chargueraud2012]
* See also <https://www.cis.upenn.edu/~plclub/popl08-tutorial/code/>, from which
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

namespace Term

/-- Variable opening of the ith bound variable. -/
def openRec (i : ℕ) (sub : Term Var) : Term Var → Term Var
| bvar i' => if i = i' then sub else bvar i'
| fvar x  => fvar x
| app l r => app (openRec i sub l) (openRec i sub r)
| abs M   => abs $ openRec (i+1) sub M

scoped notation:68 e "⟦" i " ↝ " sub "⟧"=> Term.openRec i sub e

@[aesop norm (rule_sets := [LambdaCalculus.LocallyNameless.ruleSet])]
lemma openRec_bvar : (bvar i')⟦i ↝ s⟧ = if i = i' then s else bvar i' := by rfl

@[aesop norm (rule_sets := [LambdaCalculus.LocallyNameless.ruleSet])]
lemma openRec_fvar : (fvar x)⟦i ↝ s⟧ = fvar x := by rfl

@[aesop norm (rule_sets := [LambdaCalculus.LocallyNameless.ruleSet])]
lemma openRec_app : (app l r)⟦i ↝ s⟧ = app (l⟦i ↝ s⟧) (r⟦i ↝ s⟧) := by rfl

@[aesop norm (rule_sets := [LambdaCalculus.LocallyNameless.ruleSet])]
lemma openRec_abs : M.abs⟦i ↝ s⟧ = M⟦i + 1 ↝ s⟧.abs := by rfl

/-- Variable opening of the closest binding. -/
def open' {X} (e u):= @Term.openRec X 0 u e

infixr:80 " ^ " => Term.open'

/-- Variable closing, replacing a free `fvar x` with `bvar k` -/
def closeRec (k : ℕ) (x : Var) : Term Var → Term Var
| fvar x' => if x = x' then bvar k else fvar x'
| bvar i  => bvar i
| app l r => app (closeRec k x l) (closeRec k x r)
| abs t   => abs $ closeRec (k+1) x t

scoped notation:68 e "⟦" k " ↜ " x "⟧"=> Term.closeRec k x e

variable {x : Var}

omit [HasFresh Var] in
@[aesop norm (rule_sets := [LambdaCalculus.LocallyNameless.ruleSet])]
lemma closeRec_bvar : (bvar i)⟦k ↜ x⟧ = bvar i := by rfl

omit [HasFresh Var] in
@[aesop norm (rule_sets := [LambdaCalculus.LocallyNameless.ruleSet])]
lemma closeRec_fvar : (fvar x')⟦k ↜ x⟧ = if x = x' then bvar k else fvar x' := by rfl

omit [HasFresh Var] in
@[aesop norm (rule_sets := [LambdaCalculus.LocallyNameless.ruleSet])]
lemma closeRec_app : (app l r)⟦k ↜ x⟧ = app (l⟦k ↜ x⟧) (r⟦k ↜ x⟧) := by rfl

omit [HasFresh Var] in
@[aesop norm (rule_sets := [LambdaCalculus.LocallyNameless.ruleSet])]
lemma closeRec_abs : t.abs⟦k ↜ x⟧ = t⟦k + 1 ↜ x⟧.abs := by rfl

/-- Variable closing of the closest binding. -/
def close {Var} [DecidableEq Var] (e u):= @Term.closeRec Var _ 0 u e

infixr:80 " ^* " => Term.close

/- Substitution of a free variable to a term. -/
def subst (m : Term Var) (x : Var) (sub : Term Var) : Term Var :=
  match m with
  | bvar i  => bvar i
  | fvar x' => if x = x' then sub else fvar x'
  | app l r => app (l.subst x sub) (r.subst x sub)
  | abs M   => abs $ M.subst x sub

/-- `Term.subst` is a substitution for λ-terms. Gives access to the notation `m[x := n]`. -/
instance instHasSubstitutionTerm : HasSubstitution (Term Var) Var where
  subst := Term.subst

omit [HasFresh Var] in
@[aesop norm (rule_sets := [LambdaCalculus.LocallyNameless.ruleSet])]
lemma subst_bvar {n : Term Var} : (bvar i)[x := n] = bvar i := by rfl

omit [HasFresh Var] in
@[aesop norm (rule_sets := [LambdaCalculus.LocallyNameless.ruleSet])]
lemma subst_fvar : (fvar x')[x := n] = if x = x' then n else fvar x' := by rfl

omit [HasFresh Var] in
@[aesop norm (rule_sets := [LambdaCalculus.LocallyNameless.ruleSet])]
lemma subst_app {l r : Term Var} : (app l r)[x := n] = app (l[x := n]) (r[x := n]) := by rfl

omit [HasFresh Var] in
@[aesop norm (rule_sets := [LambdaCalculus.LocallyNameless.ruleSet])]
lemma subst_abs {M : Term Var} : M.abs[x := n] = M[x := n].abs := by rfl

omit [HasFresh Var] in
@[aesop norm (rule_sets := [LambdaCalculus.LocallyNameless.ruleSet])]
lemma subst_def (m : Term Var) (x : Var) (n : Term Var) : m.subst x n = m[x := n] := by rfl

/-- Free variables of a term. -/
@[simp]
def fv : Term Var → Finset Var
| bvar _ => {}
| fvar x => {x}
| abs e1 => e1.fv
| app l r => l.fv ∪ r.fv

/-- Locally closed terms. -/
@[aesop safe (rule_sets := [LambdaCalculus.LocallyNameless.ruleSet]) [constructors]]
inductive LC : Term Var → Prop
| fvar (x)  : LC (fvar x)
| abs (L : Finset Var) (e : Term Var) : (∀ x : Var, x ∉ L → LC (e ^ fvar x)) → LC (abs e)
| app {l r} : l.LC → r.LC → LC (app l r)
