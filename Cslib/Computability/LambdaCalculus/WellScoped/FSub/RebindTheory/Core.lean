import Cslib.Computability.LambdaCalculus.WellScoped.FSub.Syntax

structure Rebind (Γ : Ctx s1) (f : Rename s1 s2) (Δ : Ctx s2) where
  var : ∀ x T, Ctx.LookupVar Γ x T -> Ctx.LookupVar Δ (f.var x) (T.rename f)
  tvar : ∀ X T, Ctx.LookupTVar Γ X T -> Ctx.LookupTVar Δ (f.tvar X) (T.rename f)

def Rebind.liftVar (ρ : Rebind Γ f Δ) : Rebind (Γ,x:T) (f.liftVar) (Δ,x:T.rename f) := by
  constructor
  case var =>
    intro x P hb
    cases hb
    case here => simp [<-Ty.rename_succVar_comm]; constructor
    case there_var hb =>
      simp [<-Ty.rename_succVar_comm]
      constructor
      apply ρ.var _ _ hb
  case tvar =>
    intro X S hb
    cases hb
    case there_var hb =>
      simp [<-Ty.rename_succVar_comm]
      constructor
      apply ρ.tvar _ _ hb

def Rebind.liftTVar (ρ : Rebind Γ f Δ) : Rebind (Γ,X<:T) (f.liftTVar) (Δ,X<:T.rename f) := by
  constructor
  case tvar =>
    intro X S hb
    cases hb
    case here => simp [<-Ty.rename_succTVar_comm]; constructor
    case there_tvar hb =>
      simp [<-Ty.rename_succTVar_comm]
      constructor
      apply ρ.tvar _ _ hb
  case var =>
    intro x P hb
    cases hb
    case there_tvar hb =>
      simp [<-Ty.rename_succTVar_comm]
      constructor
      apply ρ.var _ _ hb

def Rebind.succVar : Rebind Γ Rename.succVar (Γ,x:T) := by
  constructor
  case var =>
    intro x P hb
    constructor
    exact hb
  case tvar =>
    intro X S hb
    constructor
    exact hb

def Rebind.succTVar : Rebind Γ Rename.succTVar (Γ,X<:T) := by
  constructor
  case tvar =>
    intro X S hb
    constructor
    exact hb
  case var =>
    intro x P hb
    constructor
    exact hb
