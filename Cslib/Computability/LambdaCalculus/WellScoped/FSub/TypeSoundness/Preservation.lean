/-
Copyright (c) 2025 Yichen Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yichen Xu.
-/

/-
# Preservation theorem for System F<:

This module proves the preservation theorem for System F<:.
Preservation states that if a well-typed expression takes a reduction step,
the result is still well-typed with the same type.
-/

import Cslib.Computability.LambdaCalculus.WellScoped.FSub.TypeSystem
import Cslib.Computability.LambdaCalculus.WellScoped.FSub.Reduce
import Cslib.Computability.LambdaCalculus.WellScoped.FSub.RetypeTheory.Core
import Cslib.Computability.LambdaCalculus.WellScoped.FSub.RetypeTheory.TypeSystem
import Cslib.Computability.LambdaCalculus.WellScoped.FSub.TypeSoundness.Canonical

/-- **Preservation theorem**: Well-typed expressions remain
    well-typed after taking reduction steps.

    If `∅ ⊢ e : T` and `e ⟶ e'`, then `∅ ⊢ e' : T`.

    This is the fundamental type safety theorem establishing that computation
    preserves typing invariants. Together with progress, this constitutes
    the complete proof of type soundness for System F<:. -/
theorem preservation
  (ht : HasType .empty t T)
  (hred : Reduce t t') :
  HasType .empty t' T := by
  induction hred generalizing T
  case red_app_fun ih =>
    have ⟨T1, T2, ht1, ht2, hs0⟩ := HasType.app_inv ht
    apply HasType.sub hs0
    apply HasType.app (ih ht1) ht2
  case red_app_arg ih =>
    have ⟨T1, T2, ht1, ht2, hs0⟩ := HasType.app_inv ht
    apply HasType.sub hs0
    apply HasType.app ht1 (ih ht2)
  case red_app =>
    have ⟨T1, T2, ht1, ht2, hs0⟩ := HasType.app_inv ht
    have ⟨U0, h1, h2, h3⟩  := HasType.abs_inv ht1
    have ht2' := HasType.sub h2 ht2
    have h1' := h1.retype (Retype.open_var ht2')
    simp only [Ty.rename_succVar_open_var] at h1'
    apply HasType.sub _ h1'
    apply Subtyp.trans h3 hs0
  case red_tapp_fun ih =>
    have ⟨T2, ht1, hs2⟩ := HasType.tapp_inv ht
    apply HasType.sub hs2
    apply HasType.tapp (ih ht1)
  case red_tapp =>
    have ⟨T2, ht1, hs2⟩ := HasType.tapp_inv ht
    have ⟨U0, h1, h2, h3⟩ := HasType.tabs_inv ht1
    have h1' := h1.retype (Retype.open_tvar h2)
    have h3' := h3.retype (Retype.open_tvar Subtyp.refl)
    apply HasType.sub _ h1'
    apply Subtyp.trans h3' hs2
