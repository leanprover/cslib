import Cslib.Computability.LambdaCalculus.WellScoped.FSub.TypeSystem
import Cslib.Computability.LambdaCalculus.WellScoped.FSub.Substitution.Properties
import Cslib.Computability.LambdaCalculus.WellScoped.FSub.RebindTheory.TypeSystem

structure Retype (Γ : Ctx s1) (σ : Subst s1 s2) (Δ : Ctx s2) where
  var :
    ∀ x T,
      Γ.LookupVar x T ->
      HasType Δ (σ.var x) (T.subst σ)

  tvar :
    ∀ X S,
      Γ.LookupTVar X S ->
      Subtyp Δ (σ.tvar X) (S.subst σ)

def Retype.liftVar (ρ : Retype Γ σ Δ) : Retype (Γ,x:P) (σ.liftVar) (Δ,x:P.subst σ) := by
  constructor
  case var =>
    intro x T hb
    cases hb
    case here =>
      apply HasType.var
      simp [<-Ty.subst_succVar_comm_base]
      constructor
    case there_var hb0 =>
      have h0 := ρ.var _ _ hb0
      simp [<-Ty.subst_succVar_comm_base]
      apply h0.rebind Rebind.succVar
  case tvar =>
    intro X S hb
    cases hb
    case there_var hb0 =>
      have h0 := ρ.tvar _ _ hb0
      simp [<-Ty.subst_succVar_comm_base]
      apply h0.rebind Rebind.succVar

def Retype.liftTVar (ρ : Retype Γ σ Δ) : Retype (Γ,X<:P) (σ.liftTVar) (Δ,X<:P.subst σ) := by
  constructor
  case var =>
    intro x T hb
    cases hb
    case there_tvar hb0 =>
      have h0 := ρ.var _ _ hb0
      simp [<-Ty.subst_succTVar_comm_base]
      apply h0.rebind Rebind.succTVar
  case tvar =>
    intro X S hb
    cases hb
    case here =>
      apply Subtyp.tvar
      simp [<-Ty.subst_succTVar_comm_base]
      constructor
    case there_tvar hb0 =>
      have h0 := ρ.tvar _ _ hb0
      simp [<-Ty.subst_succTVar_comm_base]
      apply h0.rebind Rebind.succTVar

def Retype.open_var
  (ht : HasType Γ e T) :
  Retype (Γ,x:T) (Subst.open_var e) Γ := by
  constructor
  case var =>
    intro x T hb
    cases hb
    case here =>
      simp [Ty.rename_succVar_open_var]
      exact ht
    case there_var hb0 =>
      simp [Ty.rename_succVar_open_var]
      apply HasType.var
      exact hb0
  case tvar =>
    intro X S hb
    cases hb
    case there_var hb0 =>
      simp [Ty.rename_succVar_open_var]
      apply Subtyp.tvar
      exact hb0

def Retype.narrow_tvar
  (hs : Subtyp Γ S1 S2) :
  Retype (Γ,X<:S2) Subst.id (Γ,X<:S1) := by
  constructor
  case var =>
    intro x T hb
    simp [Ty.subst_id]
    constructor
    cases hb
    constructor
    trivial
  case tvar =>
    intro X S hb
    cases hb
    case here =>
      apply Subtyp.trans
      { apply Subtyp.tvar; constructor }
      { simp [Ty.subst_id]; apply hs.rebind Rebind.succTVar }
    case there_tvar hb0 =>
      apply Subtyp.tvar
      simp [Ty.subst_id]
      constructor
      exact hb0

def Retype.open_tvar
  (hs : Subtyp Γ R S) :
  Retype (Γ,X<:S) (Subst.open_tvar R) Γ := by
  constructor
  case var =>
    intro x T hb
    cases hb
    case there_tvar hb0 =>
      simp [Ty.rename_succTVar_open_tvar]
      apply HasType.var
      exact hb0
  case tvar =>
    intro X0 S0 hb
    cases hb
    case here =>
      simp [Ty.rename_succTVar_open_tvar]
      exact hs
    case there_tvar hb0 =>
      simp [Ty.rename_succTVar_open_tvar]
      apply Subtyp.tvar
      exact hb0
