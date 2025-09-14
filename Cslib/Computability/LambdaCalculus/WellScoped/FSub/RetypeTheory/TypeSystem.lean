/-
Copyright (c) 2025 Yichen Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yichen Xu.
-/

import Cslib.Computability.LambdaCalculus.WellScoped.FSub.RetypeTheory.Core

/-- Context retyping preserves subtyping judgments. -/
def Subtyp.retype {σ : Subst s1 s2}
  (hsub : Subtyp Γ T1 T2)
  (ρ : Retype Γ σ Δ) :
  Subtyp Δ (T1.subst σ) (T2.subst σ) := by
  induction hsub generalizing s2 <;> try (solve | constructor)
  case trans ih1 ih2 => apply Subtyp.trans <;> aesop
  case tvar hb => apply ρ.tvar _ _ hb
  case arrow => apply arrow <;> aesop
  case poly ih1 ih2 =>
    apply poly <;> try grind
    · apply ih2 ρ.liftTVar

/-- Context retyping preserves typing judgments. -/
theorem HasType.retype {σ : Subst s1 s2}
  (ht : HasType Γ t T)
  (ρ : Retype Γ σ Δ) :
  HasType Δ (t.subst σ) (T.subst σ) := by
  induction ht generalizing s2
  case var hb => apply ρ.var _ _ hb
  case sub hsub _ ih =>
    apply sub <;> try aesop
    apply hsub.retype ρ
  case abs ih => apply HasType.abs; simpa [Ty.subst_succVar_comm_base] using ih ρ.liftVar
  case tabs ih => apply HasType.tabs; apply ih ρ.liftTVar
  case app ih1 ih2 => apply HasType.app <;> aesop
  case tapp ih => simp only [Ty.open_tvar_subst_comm]; apply HasType.tapp; aesop
