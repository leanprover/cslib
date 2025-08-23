import Cslib.Computability.LambdaCalculus.WellScoped.FSub.Syntax.Core

inductive Ctx : Sig -> Type where
| empty : Ctx {}
| cons_var : Ctx s -> Ty s -> Ctx (s,x)
| cons_tvar : Ctx s -> Ty s -> Ctx (s,X)

infixl:50 ",x:" => Ctx.cons_var
infixl:50 ",X<:" => Ctx.cons_tvar

inductive Ctx.LookupVar : Ctx s -> Var s -> Ty s -> Prop where
| here :
  Ctx.LookupVar (Γ,x:T) .here (T.rename Rename.succVar)
| there_var :
  Ctx.LookupVar Γ x T ->
  Ctx.LookupVar (Γ,x:U) (x.there_var) (T.rename Rename.succVar)
| there_tvar :
  Ctx.LookupVar Γ x T ->
  Ctx.LookupVar (Γ,X<:S) (x.there_tvar) (T.rename Rename.succTVar)

inductive Ctx.LookupTVar : Ctx s -> TVar s -> Ty s -> Prop where
| here :
  Ctx.LookupTVar (Γ,X<:T) .here (T.rename Rename.succTVar)
| there_var :
  Ctx.LookupTVar Γ X T ->
  Ctx.LookupTVar (Γ,x:U) X.there_var (T.rename Rename.succVar)
| there_tvar :
  Ctx.LookupTVar Γ X T ->
  Ctx.LookupTVar (Γ,X<:S) X.there_tvar (T.rename Rename.succTVar)

@[simp]
instance : EmptyCollection (Ctx {}) := ⟨Ctx.empty⟩
