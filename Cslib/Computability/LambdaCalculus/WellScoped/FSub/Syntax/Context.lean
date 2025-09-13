/-
# Typing contexts for System F<:

This module defines typing contexts and variable lookup relations for System F<:.
-/

import Cslib.Computability.LambdaCalculus.WellScoped.FSub.Syntax.Core

/-- A typing context assigns types to term variables and upper bounds to type variables. -/
inductive Ctx : Sig -> Type where
/-- Empty context -/
| empty : Ctx {}
/-- Extend with term variable x : T -/
| cons_var : Ctx s -> Ty s -> Ctx (s,x)
/-- Extend with type variable X <: T -/
| cons_tvar : Ctx s -> Ty s -> Ctx (s,X)

/-- Convenient notation for extending context with a term variable -/
infixl:50 ",x:" => Ctx.cons_var
/-- Convenient notation for extending context with a type variable -/
infixl:50 ",X<:" => Ctx.cons_tvar

/-- Variable lookup relation. `Ctx.LookupVar Γ x T` means that term variable `x`
    has type `T` in context `Γ`. -/
@[grind]
inductive Ctx.LookupVar : Ctx s -> Var s -> Ty s -> Prop where
/-- Look up the most recently bound term variable -/
| here :
  Ctx.LookupVar (Γ,x:T) .here (T.rename Rename.succVar)
/-- Skip over a more recent term variable binding -/
| there_var :
  Ctx.LookupVar Γ x T ->
  Ctx.LookupVar (Γ,x:U) (x.there_var) (T.rename Rename.succVar)
/-- Skip over a more recent type variable binding -/
| there_tvar :
  Ctx.LookupVar Γ x T ->
  Ctx.LookupVar (Γ,X<:S) (x.there_tvar) (T.rename Rename.succTVar)

/-- Type variable lookup relation. `Ctx.LookupTVar Γ X T` means that type variable `X`
    has upper bound `T` in context `Γ`. -/
@[grind]
inductive Ctx.LookupTVar : Ctx s -> TVar s -> Ty s -> Prop where
/-- Look up the most recently bound type variable -/
| here :
  Ctx.LookupTVar (Γ,X<:T) .here (T.rename Rename.succTVar)
/-- Skip over a more recent term variable binding -/
| there_var :
  Ctx.LookupTVar Γ X T ->
  Ctx.LookupTVar (Γ,x:U) X.there_var (T.rename Rename.succVar)
/-- Skip over a more recent type variable binding -/
| there_tvar :
  Ctx.LookupTVar Γ X T ->
  Ctx.LookupTVar (Γ,X<:S) X.there_tvar (T.rename Rename.succTVar)

@[simp]
instance : EmptyCollection (Ctx {}) := ⟨Ctx.empty⟩
