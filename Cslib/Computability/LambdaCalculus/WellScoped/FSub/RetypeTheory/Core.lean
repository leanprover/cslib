/-
Copyright (c) 2025 Yichen Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yichen Xu.
-/

/-
# Retyping morphisms

This module defines retyping morphisms, which are the second layer in the hierarchy
of context morphisms for System F<:.
Retyping morphisms extend rebinding morphisms by mapping variables to typing derivations
rather than just renamed variables.

A retyping morphism `ρ : Retype Γ σ Δ` consists of:
- A parallel substitution `σ : s₁ → s₂`
- Contexts `Γ : Ctx s₁` and `Δ : Ctx s₂`
- Proofs that each variable in Γ maps to a well-typed term in Δ
- Proofs that each type variable in Γ maps to a subtype in Δ

More precisely, if `x : T ∈ Γ` then `Δ ⊢ σ(x) : σ(T)`,
and if `X <: S ∈ Γ` then `Δ ⊢ σ(X) <: σ(S)`.
-/

import Cslib.Computability.LambdaCalculus.WellScoped.FSub.TypeSystem
import Cslib.Computability.LambdaCalculus.WellScoped.FSub.Substitution.Properties
import Cslib.Computability.LambdaCalculus.WellScoped.FSub.RebindTheory.TypeSystem

/-- A retyping morphism `Retype Γ σ Δ` witnesses that contexts `Γ` and `Δ` are
    related by the substitution `σ` in a type-preserving way.

    Unlike rebinding morphisms, retyping morphisms map variables to typing derivations. -/
structure Retype (Γ : Ctx s1) (σ : Subst s1 s2) (Δ : Ctx s2) where
  var : ∀ x T, Γ.LookupVar x T -> HasType Δ (σ.var x) (T.subst σ)
  tvar : ∀ X S, Γ.LookupTVar X S -> Subtyp Δ (σ.tvar X) (S.subst σ)

/-- Extends a retyping morphism to contexts with an additional term variable. -/
def Retype.liftVar (ρ : Retype Γ σ Δ) : Retype (Γ,x:P) (σ.liftVar) (Δ,x:P.subst σ) where
  var := fun x T hb => by
    cases hb
    case here =>
      apply HasType.var
      simp only [<-Ty.subst_succVar_comm_base]
      constructor
    case there_var hb0 =>
      have h0 := ρ.var _ _ hb0
      simp only [<-Ty.subst_succVar_comm_base]
      apply h0.rebind Rebind.succVar
  tvar := fun X S hb => by
    cases hb
    case there_var hb0 =>
      have h0 := ρ.tvar _ _ hb0
      simp only [<-Ty.subst_succVar_comm_base]
      apply h0.rebind Rebind.succVar

/-- Extends a retyping morphism to contexts with an additional type variable. -/
def Retype.liftTVar (ρ : Retype Γ σ Δ) : Retype (Γ,X<:P) (σ.liftTVar) (Δ,X<:P.subst σ) where
  var := fun x T hb => by
    cases hb
    case there_tvar hb0 =>
      have h0 := ρ.var _ _ hb0
      simp only [<-Ty.subst_succTVar_comm_base]
      apply h0.rebind Rebind.succTVar
  tvar := fun X S hb => by
    cases hb
    case here =>
      apply Subtyp.tvar
      grind [Ty.subst_succTVar_comm_base]
    case there_tvar hb0 =>
      have h0 := ρ.tvar _ _ hb0
      simp only [<-Ty.subst_succTVar_comm_base]
      apply h0.rebind Rebind.succTVar

/-- Creates a retyping morphism that substitutes an expression for the newest term variable. -/
def Retype.open_var
  (ht : HasType Γ e T) :
  Retype (Γ,x:T) (Subst.open_var e) Γ where
  var := fun x T hb => by
    cases hb
    case here => simpa [Ty.rename_succVar_open_var]
    case there_var hb0 => apply HasType.var; simpa [Ty.rename_succVar_open_var]
  tvar := fun X S hb => by
    cases hb
    case there_var hb0 => apply Subtyp.tvar; simpa [Ty.rename_succVar_open_var]

/-- Creates a retyping morphism that narrows the bound of the newest type variable. -/
def Retype.narrow_tvar
  (hs : Subtyp Γ S1 S2) :
  Retype (Γ,X<:S2) Subst.id (Γ,X<:S1) where
  var := fun x T hb => by cases hb; constructor; grind [Ty.subst_id]
  tvar := fun X S hb => by
    cases hb
    case here =>
      apply Subtyp.trans
      { apply Subtyp.tvar; constructor }
      { simp only [Ty.subst_id]; apply hs.rebind Rebind.succTVar }
    case there_tvar hb0 => apply Subtyp.tvar; grind [Ty.subst_id]

/-- Creates a retyping morphism that substitutes a type for the newest type variable. -/
def Retype.open_tvar
  (hs : Subtyp Γ R S) :
  Retype (Γ,X<:S) (Subst.open_tvar R) Γ where
  var := fun x T hb => by
    cases hb
    case there_tvar hb0 => apply HasType.var; grind [Ty.rename_succTVar_open_tvar]
  tvar := fun X0 S0 hb => by
    cases hb
    case here => simpa [Ty.rename_succTVar_open_tvar]
    case there_tvar hb0 => apply Subtyp.tvar; simpa [Ty.rename_succTVar_open_tvar]
