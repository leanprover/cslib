/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/

import Cslib.Logics.Bimodal.Metalogic.Algebraic.ParametricCanonical
import Cslib.Logics.Bimodal.Metalogic.Bundle.BFMCS
import Cslib.Logics.Bimodal.Semantics.WorldHistory
import Cslib.Logics.Bimodal.Semantics.Truth

/-!
# D-Parametric History Conversion

Converts FMCS (Family of MCS) to WorldHistory for the D-parametric canonical TaskFrame.

## References

* Ported from BimodalLogic/Theories/Bimodal/Metalogic/Algebraic/ParametricHistory.lean
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Cslib.Logic.Bimodal.Metalogic.Algebraic.ParametricHistory

open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Metalogic.Core
open Cslib.Logic.Bimodal.Metalogic.Bundle
open Cslib.Logic.Bimodal.Metalogic.Algebraic.ParametricCanonical

variable {Atom : Type} {fc : FrameClass} {D : Type*} [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]

/-- Convert an FMCS to a WorldHistory in the parametric canonical TaskFrame. -/
def parametric_to_history (fam : FMCS Atom D fc) : WorldHistory (ParametricCanonicalTaskFrame (Atom := Atom) (fc := fc) (D := D)) where
  domain := fun _ => True
  convex := fun _ _ _ _ _ _ _ => True.intro
  states := fun t _ => ⟨fam.mcs t, fam.is_mcs t⟩
  respects_task := fun s t _ _ hst => by
    show parametric_canonical_task_rel _ _ _
    unfold parametric_canonical_task_rel
    by_cases h_pos : t - s > 0
    · rw [if_pos h_pos]
      intro phi h_G_phi
      exact fam.forward_G s t phi (sub_pos.mp h_pos) h_G_phi
    · have h_eq : t - s = 0 := le_antisymm (not_lt.mp h_pos) (sub_nonneg.mpr hst)
      have h_neg : ¬(t - s < 0) := not_lt.mpr (sub_nonneg.mpr hst)
      rw [if_neg h_pos, if_neg h_neg]
      have h_s_eq_t : s = t := by
        have : t = s := sub_eq_zero.mp h_eq
        exact this.symm
      subst h_s_eq_t
      rfl

/-- States of parametric_to_history at time t. -/
theorem parametric_to_history_states (fam : FMCS Atom D fc) (t : D) (ht : True) :
    (parametric_to_history fam).states t ht = ⟨fam.mcs t, fam.is_mcs t⟩ := rfl

/-- The parametric canonical Omega: the set of world-histories from bundle families. -/
def ParametricCanonicalOmega (B : BFMCS Atom D fc) : Set (WorldHistory (ParametricCanonicalTaskFrame (Atom := Atom) (fc := fc) (D := D))) :=
  { tau | ∃ fam ∈ B.families, tau = parametric_to_history fam }

/-- The shift-closed parametric canonical Omega. -/
def ShiftClosedParametricCanonicalOmega (B : BFMCS Atom D fc) :
    Set (WorldHistory (ParametricCanonicalTaskFrame (Atom := Atom) (fc := fc) (D := D))) :=
  { σ | ∃ (fam : FMCS Atom D fc) (_ : fam ∈ B.families) (delta : D),
    σ = WorldHistory.time_shift (parametric_to_history fam) delta }

private theorem time_shift_parametric_to_history_compose
    (fam : FMCS Atom D fc)
    (delta delta' : D) :
    WorldHistory.time_shift (WorldHistory.time_shift (parametric_to_history fam) delta) delta' =
    WorldHistory.time_shift (parametric_to_history fam) (delta + delta') := by
  have h_time_eq : ∀ t : D, t + delta' + delta = t + (delta + delta') := fun t => by
    rw [add_assoc, add_comm delta' delta]
  simp only [WorldHistory.time_shift, parametric_to_history]
  congr 1
  ext t ht
  simp only []
  rw [h_time_eq t]

private theorem parametric_to_history_eq_time_shift_zero (fam : FMCS Atom D fc) :
    parametric_to_history fam = WorldHistory.time_shift (parametric_to_history fam) 0 := by
  simp only [WorldHistory.time_shift, parametric_to_history, add_zero]

/-- ShiftClosedParametricCanonicalOmega is shift-closed. -/
theorem shiftClosedParametricCanonicalOmega_is_shift_closed (B : BFMCS Atom D fc) :
    ShiftClosed (ShiftClosedParametricCanonicalOmega B) := by
  intro σ h_mem Δ'
  obtain ⟨fam, hfam, delta, h_eq⟩ := h_mem
  refine ⟨fam, hfam, delta + Δ', ?_⟩
  subst h_eq
  exact time_shift_parametric_to_history_compose fam delta Δ'

/-- Every parametric canonical history is in the shift-closed parametric canonical Omega. -/
theorem parametricCanonicalOmega_subset_shiftClosed (B : BFMCS Atom D fc) :
    ParametricCanonicalOmega B ⊆ ShiftClosedParametricCanonicalOmega B := by
  intro σ h_mem
  obtain ⟨fam, hfam, h_eq⟩ := h_mem
  refine ⟨fam, hfam, 0, ?_⟩
  subst h_eq
  exact parametric_to_history_eq_time_shift_zero fam

/-- Domain of parametric_to_history is full. -/
theorem parametric_to_history_domain_full (fam : FMCS Atom D fc) (t : D) :
    (parametric_to_history fam).domain t := True.intro

/-- The underlying MCS of the world state at time t equals fam.mcs t. -/
theorem parametric_to_history_mcs_eq (fam : FMCS Atom D fc) (t : D) (ht : True) :
    ((parametric_to_history fam).states t ht).val = fam.mcs t := rfl

end Cslib.Logic.Bimodal.Metalogic.Algebraic.ParametricHistory
