/-
Copyright (c) 2025 Yichen Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yichen Xu.
-/

/-
# Operational semantics for System F<:

This module defines the small-step operational semantics for System F<:.
-/

import Cslib.Computability.LambdaCalculus.WellScoped.FSub.Syntax

/-- The small-step reduction relation for System F<:. `Reduce e₁ e₂` means that
    expression `e₁` can take a single computational step to become `e₂`. -/
inductive Reduce : Exp s -> Exp s -> Prop where
/-- Evaluate function position: if e₁ ⟶ e₁', then (e₁ e₂) ⟶ (e₁' e₂) -/
| red_app_fun :
  Reduce e1 e1' ->
  Reduce (.app e1 e2) (.app e1' e2)
/-- Evaluate argument position: if v₁ is a value and e₂ ⟶ e₂', then (v₁ e₂) ⟶ (v₁ e₂') -/
| red_app_arg :
  Exp.IsVal v1 ->
  Reduce e2 e2' ->
  Reduce (.app v1 e2) (.app v1 e2')
/-- Beta reduction: (λx:T.e₁) e₂ ⟶ e₁[x := e₂] -/
| red_app :
  Reduce (.app (.abs T e1) e2) (e1.open_var e2)
/-- Evaluate polymorphic expression: if e ⟶ e', then (e [T]) ⟶ (e' [T]) -/
| red_tapp_fun :
  Reduce e e' ->
  Reduce (.tapp e T) (.tapp e' T)
/-- Type application: (ΛX<:T'.e) [T] ⟶ e[X := T] -/
| red_tapp :
  Reduce (.tapp (.tabs T' e) T) (e.open_tvar T)
