import Cslib.Computability.LambdaCalculus.WellScoped.FSub.TypeSystem
import Cslib.Computability.LambdaCalculus.WellScoped.FSub.Reduce
import Cslib.Computability.LambdaCalculus.WellScoped.FSub.RetypeTheory.Core
import Cslib.Computability.LambdaCalculus.WellScoped.FSub.RetypeTheory.TypeSystem
import Cslib.Computability.LambdaCalculus.WellScoped.FSub.TypeSoundness.Canonical

theorem preservation
  (ht : HasType .empty t T)
  (hred : Reduce t t') :
  HasType .empty t' T := by
  induction hred generalizing T
  case red_app_fun ih =>
    have ⟨T1, T2, ht1, ht2, hs0⟩ := HasType.app_inv ht
    have ih := ih ht1
    apply HasType.sub hs0
    apply HasType.app ih ht2
  case red_app_arg ih =>
    have ⟨T1, T2, ht1, ht2, hs0⟩ := HasType.app_inv ht
    have ih := ih ht2
    apply HasType.sub hs0
    apply HasType.app ht1 ih
  case red_app =>
    have ⟨T1, T2, ht1, ht2, hs0⟩ := HasType.app_inv ht
    have ⟨U0, h1, h2, h3⟩  := HasType.abs_inv ht1
    have ht2' := HasType.sub h2 ht2
    have h1' := h1.retype (Retype.open_var ht2')
    simp [Ty.rename_succVar_open_var] at h1'
    apply HasType.sub _ h1'
    apply Subtyp.trans h3 hs0
  case red_tapp_fun ih =>
    have ⟨T2, ht1, hs2⟩ := HasType.tapp_inv ht
    have ih := ih ht1
    apply HasType.sub hs2
    apply HasType.tapp ih
  case red_tapp =>
    have ⟨T2, ht1, hs2⟩ := HasType.tapp_inv ht
    have ⟨U0, h1, h2, h3⟩ := HasType.tabs_inv ht1
    have h1' := h1.retype (Retype.open_tvar h2)
    rename_i R
    have h3' := h3.retype (Retype.open_tvar Subtyp.refl)
    apply HasType.sub _ h1'
    apply Subtyp.trans h3' hs2
