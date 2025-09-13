/-
Copyright (c) 2025 Yichen Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yichen Xu.
-/

/-
# Parallel substitution for System F<:

This module defines parallel substitution operations, which allow simultaneous
substitution of multiple variables.
This provides a uniform way to handle variable binding and substitution.

The module defines:
- `Subst`: A parallel substitution that maps variables from signature s₁ to
  expressions/types in signature s₂
- Lifting operations that extend substitutions to work under binders
- Opening operations for single-variable substitution
- Identity substitution and conversion from renamings

Parallel substitutions generalize both renamings and single-variable substitutions.
The lifting operations extend substitutions to work under binders
while respecting the scoping disciplines of the intrinsically scoped syntax.

A substitution σ : s₁ → s₂ assigns to each variable x ∈ s₁ an expression σ(x)
with variables in s₂, and to each type variable X ∈ s₁ a type σ(X) with variables in s₂.
-/

import Cslib.Computability.LambdaCalculus.WellScoped.FSub.Syntax.Core

/-- A parallel substitution maps term variables to expressions and type variables
    to types. This allows simultaneous substitution of multiple variables while
    preserving well-scopedness. -/
structure Subst (s1 s2 : Sig) where
  /-- How to substitute term variables -/
  var : Var s1 -> Exp s2
  /-- How to substitute type variables -/
  tvar : TVar s1 -> Ty s2

/-- Lift a substitution to work under a term variable binder. The newly bound
    variable is mapped to itself, while existing variables are substituted and
    then weakened to account for the new binding. -/
def Subst.liftVar (s : Subst s1 s2) : Subst (s1,x) (s2,x) :=
  { var := fun x => match x with
      | .here => .var .here
      | .there_var x0 => (s.var x0).rename Rename.succVar
    tvar := fun X => match X with
      | .there_var X0 => (s.tvar X0).rename Rename.succVar }

/-- Lift a substitution to work under a type variable binder. The newly bound
    type variable is mapped to itself, while existing variables are substituted
    and then weakened to account for the new binding. -/
def Subst.liftTVar (s : Subst s1 s2) : Subst (s1,X) (s2,X) :=
  { tvar := fun X => match X with
      | .here => .tvar .here
      | .there_tvar X0 => (s.tvar X0).rename Rename.succTVar
    var := fun x => match x with
      | .there_tvar x0 => (s.var x0).rename Rename.succTVar }

/-- Create a substitution that replaces the outermost term variable with the given
    expression, while leaving all other variables unchanged. This is used for
    function application (beta reduction). -/
def Subst.open_var (e : Exp s) : Subst (s,x) s :=
  { var := fun x => match x with
      | .here => e
      | .there_var x0 => .var x0
    tvar := fun X => match X with
      | .there_var X0 => .tvar X0 }

/-- Create a substitution that replaces the outermost type variable with the given
    type, while leaving all other variables unchanged. This is used for
    type application in polymorphic functions. -/
def Subst.open_tvar (T : Ty s) : Subst (s,X) s :=
  { var := fun x => match x with
      | .there_tvar x0 => .var x0
    tvar := fun X => match X with
      | .here => T
      | .there_tvar X0 => .tvar X0 }

/-- Convert a renaming into a substitution. Every variable is mapped to the
    correspondingly renamed variable. -/
def Rename.asSubst (f : Rename s1 s2) : Subst s1 s2 :=
  { var := fun x => .var (f.var x)
    tvar := fun X => .tvar (f.tvar X) }

/-- Functional extensionality for substitutions: two substitutions are equal
    if they map all variables in the same way. -/
theorem Subst.funext {σ1 σ2 : Subst s1 s2}
  (var : ∀ x, σ1.var x = σ2.var x)
  (tvar : ∀ X, σ1.tvar X = σ2.tvar X) : σ1 = σ2 := by
  cases σ1; cases σ2
  simp
  constructor
  { funext x; aesop }
  { funext X; aesop }

/-- Lift a substitution to work under multiple binders specified by a signature.
    This generalizes `liftVar` and `liftTVar` to arbitrary sequences of binders. -/
def Subst.lift : Subst s1 s2 -> (s : Sig) -> Subst (s1 ++ s) (s2 ++ s)
| σ, .empty => σ
| σ, .push_var s => (σ.lift s).liftVar
| σ, .push_tvar s => (σ.lift s).liftTVar

/-- The identity substitution that maps each variable to itself. -/
def Subst.id : Subst s s :=
  { var := fun x => .var x
    tvar := fun X => .tvar X }
