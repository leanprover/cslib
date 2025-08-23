import Cslib.Computability.LambdaCalculus.WellScoped.FSub.Syntax

inductive Subtyp : Ctx s -> Ty s -> Ty s -> Prop where
| top :
  Subtyp Γ T .top
| refl :
  Subtyp Γ T T
| trans :
  Subtyp Γ A B ->
  Subtyp Γ B C ->
  Subtyp Γ A C
| tvar :
  Ctx.LookupTVar Γ X T ->
  Subtyp Γ (.tvar X) T
| arrow :
  Subtyp Γ T2 T1 ->
  Subtyp Γ U1 U2 ->
  Subtyp Γ (.arrow T1 U1) (.arrow T2 U2)
| poly :
  Subtyp Γ T2 T1 ->
  Subtyp (Γ,X<:T2) U1 U2 ->
  Subtyp Γ (.poly T1 U1) (.poly T2 U2)

inductive HasType : Ctx s -> Exp s -> Ty s -> Prop where
| var :
  Ctx.LookupVar Γ x T ->
  HasType Γ (.var x) T
| sub :
  Subtyp Γ T1 T2 ->
  HasType Γ t T1 ->
  HasType Γ t T2
| abs :
  HasType (Γ,x:T) t (U.rename Rename.succVar) ->
  HasType Γ (.abs T t) (.arrow T U)
| tabs :
  HasType (Γ,X<:T) t U ->
  HasType Γ (.tabs T t) (.poly T U)
| app :
  HasType Γ t1 (.arrow T1 U1) ->
  HasType Γ t2 T1 ->
  HasType Γ (.app t1 t2) U1
| tapp :
  HasType Γ t (.poly T U) ->
  HasType Γ (.tapp t T) (U.open_tvar T)
