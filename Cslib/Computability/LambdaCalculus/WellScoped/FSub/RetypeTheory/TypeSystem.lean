import Cslib.Computability.LambdaCalculus.WellScoped.FSub.RetypeTheory.Core

def Subtyp.retype {σ : Subst s1 s2}
  (hsub : Subtyp Γ T1 T2)
  (ρ : Retype Γ σ Δ) :
  Subtyp Δ (T1.subst σ) (T2.subst σ) := by
  induction hsub generalizing s2
  case top => constructor
  case refl => constructor
  case trans ih1 ih2 =>
    apply Subtyp.trans <;> aesop
  case tvar hb =>
    apply ρ.tvar _ _ hb
  case arrow => apply arrow <;> aesop
  case poly ih1 ih2 =>
    apply poly
    { apply ih1 ρ }
    { apply ih2 ρ.liftTVar }

theorem HasType.retype {σ : Subst s1 s2}
  (ht : HasType Γ t T)
  (ρ : Retype Γ σ Δ) :
  HasType Δ (t.subst σ) (T.subst σ) := by
  induction ht generalizing s2
  case var hb => apply ρ.var _ _ hb
  case sub hsub _ ih =>
    apply sub
    { apply hsub.retype ρ }
    { apply ih ρ }
  case abs ih =>
    apply HasType.abs
    simp [Ty.subst_succVar_comm_base]
    apply ih ρ.liftVar
  case tabs ih =>
    apply HasType.tabs
    apply ih ρ.liftTVar
  case app ih1 ih2 =>
    apply HasType.app
    { apply ih1 ρ }
    { apply ih2 ρ }
  case tapp ih =>
    simp [Ty.open_tvar_subst_comm]
    apply HasType.tapp
    apply ih ρ
