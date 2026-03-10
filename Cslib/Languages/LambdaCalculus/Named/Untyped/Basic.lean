/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Haoxuan Yin
-/

module

public import Cslib.Foundations.Data.HasFresh
public import Cslib.Foundations.Syntax.HasAlphaEquiv
public import Cslib.Foundations.Syntax.HasSubstitution

@[expose] public section

/-! # λ-calculus

The untyped λ-calculus.

## References

* [H. Barendregt, *Introduction to Lambda Calculus*][Barendregt1984]
* Definition of α-equivalence [A. Pitts, *Nominal Techniques*][Pitts2015]

-/

namespace Cslib

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
def Term.vars [DecidableEq Var] : Term Var → Finset Var
  | var x => {x}
  | abs x m => m.vars ∪ {x}
  | app m n => m.vars ∪ n.vars

/-- Variable renaming, applying to both free and bound variables.
    `m.rename x y` changes all occurrences of `x` into `y` in `m`. -/
def Term.rename [DecidableEq Var] (m : Term Var) (x y : Var) : Term Var :=
  match m with
  | var z => if z = x then (var y) else (var z)
  | abs z m' => abs (if z = x then y else z) (m'.rename x y)
  | app n1 n2 => app (n1.rename x y) (n2.rename x y)

/-- Renaming preserves size. -/
@[simp]
theorem Term.rename.eq_sizeOf {m : Term Var} {x y : Var} [DecidableEq Var] :
  sizeOf (m.rename x y) = sizeOf m := by
  induction m <;> aesop (add simp [Term.rename])

open Term

/-- α-equivalence. -/
inductive Term.AlphaEquiv [DecidableEq Var] : Term Var → Term Var → Prop where
| var {x} : AlphaEquiv (var x) (var x)
| abs {y x1 x2 m1 m2} : y ≠ x1 → y ≠ x2 → y ∉ m1.vars → y ∉ m2.vars →
  AlphaEquiv (m1.rename x1 y) (m2.rename x2 y) → AlphaEquiv (abs x1 m1) (abs x2 m2)
| app {m1 n1 m2 n2} : AlphaEquiv m1 n1 → AlphaEquiv m2 n2 → AlphaEquiv (app m1 m2) (app n1 n2)

/-- Instance for the notation `m =α n`. -/
instance instHasAlphaEquivTerm [DecidableEq Var] : HasAlphaEquiv (Term Var) where
  AlphaEquiv := Term.AlphaEquiv

/-- Capture-avoiding substitution, as an inference system. -/
inductive Term.Subst [DecidableEq Var] : Term Var → Var → Term Var → Term Var → Prop where
  | varHit : (var x).Subst x r r
  | varMiss : x ≠ y → (var y).Subst x r (var y)
  | absShadow : (abs x m).Subst x r (abs x m)
  | absIn : x ≠ y → y ∉ r.fv → m.Subst x r m' → (abs y m).Subst x r (abs y m')
  | app : m.Subst x r m' → n.Subst x r n' → (app m n).Subst x r (app m' n')
  | alpha : m =α m' → r =α r' → n =α n' → Subst m x r n → m'.Subst x r' n'

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
      let z := HasFresh.fresh (m'.vars ∪ r.vars ∪ {x})
      abs z ((m'.rename y z).subst x r)
  | app m1 m2 => app (m1.subst x r) (m2.subst x r)
termination_by m
decreasing_by all_goals grind [rename.eq_sizeOf, abs.sizeOf_spec, app.sizeOf_spec]

/-- `Term.subst` is a substitution for λ-terms. Gives access to the notation `m[x := n]`. -/
instance instHasSubstitutionTerm [DecidableEq Var] [HasFresh Var] :
    HasSubstitution (Term Var) Var (Term Var) where
  subst := Term.subst

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

end LambdaCalculus.Named

end Cslib
