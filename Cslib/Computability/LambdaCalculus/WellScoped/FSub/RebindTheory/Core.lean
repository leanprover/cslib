/-
Copyright (c) 2025 Yichen Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yichen Xu.
-/

/-
# Rebinding morphisms

This module defines rebinding morphisms, which enable systematic reasoning about
context transformations in the well-scoped approach to System F<:.
Rebinding morphisms are structure-preserving maps between typing contexts
that maintain relationships between variables and their types.

A rebinding morphism `ρ : Rebind Γ f Δ` consists of:
- A renaming `f : s₁ → s₂` between signatures
- Contexts `Γ : Ctx s₁` and `Δ : Ctx s₂`
- Proofs that bound types are preserved under renaming

If `x : T ∈ Γ` then `f(x) : f(T) ∈ Δ`, where `f(T)` denotes the renaming of type `T` under `f`.

Rebinding theory forms the first layer in a hierarchy of context morphisms.
Retyping morphisms build upon this foundation.
-/

import Cslib.Computability.LambdaCalculus.WellScoped.FSub.Syntax

/-- A rebinding morphism `Rebind Γ f Δ` witnesses that contexts `Γ` and `Δ` are
    related by the renaming `f` in a type-preserving way.

    This structure encodes the fundamental principle that context transformations
    must preserve the variable and type bindings in the context. -/
structure Rebind (Γ : Ctx s1) (f : Rename s1 s2) (Δ : Ctx s2) where
  /-- Term variable preservation: x:T in Γ implies f(x):f(T) in Δ -/
  var : ∀ x T,
    (hb : Ctx.LookupVar Γ x T) →
    Ctx.LookupVar Δ (f.var x) (T.rename f)
  /-- Type variable preservation: X<:T in Γ implies f(X)<:f(T) in Δ -/
  tvar : ∀ X T,
    (hb : Ctx.LookupTVar Γ X T) →
    Ctx.LookupTVar Δ (f.tvar X) (T.rename f)

/-- **Lifting rebinding morphisms over term variable binders**.

    If ρ witnesses that Γ and Δ are related by f, then ρ.liftVar witnesses
    that Γ,x:T and Δ,x:f(T) are related by f.liftVar. -/
def Rebind.liftVar (ρ : Rebind Γ f Δ) : Rebind (Γ,x:T) (f.liftVar) (Δ,x:T.rename f) where
  var := fun x P hb => by
    cases hb
    case here => simp only [←Ty.rename_succVar_comm]; constructor
    case there_var hb =>
      simp only [←Ty.rename_succVar_comm]
      constructor
      apply ρ.var _ _ hb
  tvar := fun X S hb => by
    cases hb
    case there_var hb =>
      simp only [←Ty.rename_succVar_comm]
      constructor
      apply ρ.tvar _ _ hb

/-- **Lifting rebinding morphisms over type variable binders**.

    If ρ witnesses that Γ and Δ are related by f, then ρ.liftTVar witnesses
    that Γ,X<:T and Δ,X<:f(T) are related by f.liftTVar. -/
def Rebind.liftTVar (ρ : Rebind Γ f Δ) : Rebind (Γ,X<:T) (f.liftTVar) (Δ,X<:T.rename f) where
  tvar := fun X S hb => by
    cases hb
    case here => simp only [←Ty.rename_succTVar_comm]; constructor
    case there_tvar hb =>
      simp only [←Ty.rename_succTVar_comm]
      constructor
      apply ρ.tvar _ _ hb
  var := fun x P hb => by
    cases hb
    case there_tvar hb => simp only [←Ty.rename_succTVar_comm]; constructor; apply ρ.var _ _ hb

/-- **Term variable weakening morphism**.

    The standard weakening operation that extends a context with a new term variable
    is a rebinding morphism. -/
def Rebind.succVar : Rebind Γ Rename.succVar (Γ,x:T) where
  var := by intro x P hb; constructor; exact hb
  tvar := by intro X S hb; constructor; exact hb

/-- **Type variable weakening morphism**.

    The standard weakening operation that extends a context with a new type variable
    is a rebinding morphism. -/
def Rebind.succTVar : Rebind Γ Rename.succTVar (Γ,X<:T) where
  tvar := by intro X S hb; constructor; exact hb
  var := by intro x P hb; constructor; exact hb
