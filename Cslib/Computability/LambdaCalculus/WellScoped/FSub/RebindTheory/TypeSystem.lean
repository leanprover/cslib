import Cslib.Computability.LambdaCalculus.WellScoped.FSub.RebindTheory.Core
import Cslib.Computability.LambdaCalculus.WellScoped.FSub.TypeSystem
import Cslib.Computability.LambdaCalculus.WellScoped.FSub.Substitution.Properties

theorem Subtyp.rebind {f : Rename s1 s2}
  (hs : Subtyp Γ T1 T2)
  (ρ : Rebind Γ f Δ) :
  Subtyp Δ (T1.rename f) (T2.rename f) := by
  induction hs generalizing s2
  case top => constructor
  case refl => constructor
  case trans =>
    apply Subtyp.trans <;> aesop
  case tvar hb =>
    apply Subtyp.tvar
    apply ρ.tvar _ _ hb
  case arrow ih1 ih2 =>
    apply Subtyp.arrow
    { apply ih1 ρ }
    { apply ih2 ρ }
  case poly ih1 ih2 =>
    apply Subtyp.poly
    { apply ih1 ρ }
    { apply ih2 ρ.liftTVar }

theorem HasType.rebind {f : Rename s1 s2}
  (ht : HasType Γ t T)
  (ρ : Rebind Γ f Δ) :
  HasType Δ (t.rename f) (T.rename f) := by
  induction ht generalizing s2
  case var hb =>
    apply HasType.var
    apply ρ.var _ _ hb
  case sub hsub _ ih =>
    apply sub
    { apply hsub.rebind ρ }
    { apply ih ρ }
  case abs ih =>
    apply HasType.abs
    simp [Ty.rename_succVar_comm]
    apply ih ρ.liftVar
  case tabs ih =>
    apply HasType.tabs
    apply ih ρ.liftTVar
  case app ih1 ih2 =>
    apply HasType.app
    { apply ih1 ρ }
    { apply ih2 ρ }
  case tapp ih =>
    simp [Ty.open_tvar_rename_comm]
    apply tapp
    aesop
