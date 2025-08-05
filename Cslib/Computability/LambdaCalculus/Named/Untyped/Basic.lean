/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Data.HasFresh
import Cslib.Syntax.HasAlphaEquiv
import Cslib.Syntax.HasSubstitution
import Mathlib.Data.Finset.Basic

/-! # λ-calculus

The untyped λ-calculus.

## References

* [H. Barendregt, *Introduction to Lambda Calculus*][Barendregt1984]

-/

universe u

variable {Var : Type u}

namespace LambdaCalculus.Named

/-- Syntax of terms. -/
inductive Term (Var : Type u) : Type u where
  | var (x : Var)
  | abs (x : Var) (m : Term Var)
  | app (m n : Term Var)
deriving DecidableEq

/-- Free variables. -/
def Term.fv [DecidableEq Var] : Term Var → Finset Var
  | var x => {x}
  | abs x m => m.fv.erase x
  | app m n => m.fv ∪ n.fv

/-- Bound variables. -/
def Term.bv [DecidableEq Var] : Term Var → Finset Var
  | var _ => ∅
  | abs x m => m.bv ∪ {x} -- Could also be `insert x m.bv`
  | app m n => m.bv ∪ n.bv

/-- Variable names (free and bound) in a term. -/
def Term.vars [DecidableEq Var] (m : Term Var) : Finset Var :=
  m.fv ∪ m.bv

/-- Capture-avoiding substitution, as an inference system. -/
inductive Term.Subst [DecidableEq Var] : Term Var → Var → Term Var → Term Var → Prop where
  | varHit : (var x).Subst x r r
  | varMiss : x ≠ y → (var y).Subst x r (var y)
  | absShadow : (abs x m).Subst x r (abs x m)
  | absIn : x ≠ y → y ∉ r.fv → m.Subst x r m' → (abs y m).Subst x r (abs y m')
  | app : m.Subst x r m' → n.Subst x r n' → (app m n).Subst x r (app m' n')

/-- Renaming, or variable substitution. `m.rename x y` renames `x` into `y` in `m`. -/
def Term.rename [DecidableEq Var] (m : Term Var) (x y : Var) : Term Var :=
  match m with
  | var z => if z = x then (var y) else (var z)
  | abs z m' =>
    if z = x then
      -- Shadowing
      abs z m'
    else
      abs z (m'.rename x y)
  | app n1 n2 => app (n1.rename x y) (n2.rename x y)

/-- Renaming preserves size. -/
@[simp]
theorem Term.rename.eq_sizeOf {m : Term Var} {x y : Var} [DecidableEq Var] :
  sizeOf (m.rename x y) = sizeOf m := by
  induction m <;> aesop (add simp [Term.rename])

/-- Capture-avoiding substitution. `m.subst x r` replaces the free occurrences of variable `x`
in `m` with `r`. -/
def Term.subst [DecidableEq Var] [HasFresh Var] (m : Term Var) (x : Var) (r : Term Var) :
  Term Var :=
  match m with
  | var y => if y = x then r else var y
  | abs y m' =>
    if y = x then
      abs y m'
    else if y ∉ r.fv then
      abs y (m'.subst x r)
    else
      let z := HasFresh.fresh (abs y m').vars
      abs z ((m'.rename y z).subst x r)
  | app m1 m2 => app (m1.subst x r) (m2.subst x r)
termination_by m
decreasing_by all_goals grind [rename.eq_sizeOf, abs.sizeOf_spec, app.sizeOf_spec]

/-- `Term.subst` is a substitution for λ-terms. Gives access to the notation `m[x := n]`. -/
instance instHasSubstitutionTerm [DecidableEq Var] [HasFresh Var] :
    HasSubstitution (Term Var) Var where
  subst := Term.subst

-- TODO
-- theorem Term.subst_comm
--   [DecidableEq Var] [HasFresh Var]
--   {m : Term Var} {x : Var} {n1 : Term Var} {y : Var} {n2 : Term Var} :
--   (m[x := n1])[y := n2] = (m[y := n2])[x := n1] := by
--   induction m
--   -- case var z =>
--   sorry

/-- Contexts. -/
inductive Context (Var : Type u) : Type u where
  | hole
  | abs (x : Var) (c : Context Var)
  | appL (c : Context Var) (m : Term Var)
  | appR (m : Term Var) (c : Context Var)
deriving DecidableEq

/-- Replaces the hole in a `Context` with a `Term`. -/
def Context.fill (c : Context Var) (m : Term Var) : Term Var :=
  match c with
  | hole => m
  | abs x c => Term.abs x (c.fill m)
  | appL c n => Term.app (c.fill m) n
  | appR n c => Term.app n (c.fill m)

/-- Any `Term` can be obtained by filling a `Context` with a variable. This proves that `Context`
completely captures the syntax of terms. -/
theorem Context.complete (m : Term Var) :
    ∃ (c : Context Var) (x : Var), m = (c.fill (Term.var x)) := by
  induction m with
  | var x => exists hole, x
  | abs x n ih =>
    obtain ⟨c', y, ih⟩ := ih
    exists Context.abs x c', y
    rw [ih, fill]
  | app n₁ n₂ ih₁ ih₂ =>
    obtain ⟨c₁, x₁, ih₁⟩ := ih₁
    exists Context.appL c₁ n₂, x₁
    rw [ih₁, fill]

open Term

/-- α-equivalence. -/
inductive Term.AlphaEquiv [DecidableEq Var] : Term Var → Term Var → Prop where
-- The α-axiom
| ax {m : Term Var} {x y : Var} :
  y ∉ m.fv → AlphaEquiv (abs x m) (abs y (m.rename x y))
-- Equivalence relation rules
| refl : AlphaEquiv m m
| symm : AlphaEquiv m n → AlphaEquiv n m
| trans : AlphaEquiv m1 m2 → AlphaEquiv m2 m3 → AlphaEquiv m1 m3
-- Context closure
| ctx {c : Context Var} {m n : Term Var} : AlphaEquiv m n → AlphaEquiv (c.fill m) (c.fill n)

/-- Instance for the notation `m =α n`. -/
instance instHasAlphaEquivTerm [DecidableEq Var] : HasAlphaEquiv (Term Var) where
  AlphaEquiv := Term.AlphaEquiv

end LambdaCalculus.Named
