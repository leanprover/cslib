/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import Cslib.Logics.Bimodal.Metalogic.Bundle.TemporalCoherence
import Cslib.Logics.Bimodal.Metalogic.Bundle.SuccRelation
import Cslib.Logics.Bimodal.Theorems.TemporalDerived

/-!
# Until/Since Coherence: Backward Direction

Backward Until and backward Since lemmas for FMCS families over Int.

## References

* Ported from BimodalLogic/Theories/Bimodal/Metalogic/Bundle/UntilSinceCoherence.lean
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Cslib.Logic.Bimodal.Metalogic.Bundle

open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Metalogic.Core

variable {Atom : Type*}

/-! ## Reflexive Base Case -/

theorem backward_until_reflexive {M : Set (Formula Atom)} (h_mcs : SetMaximalConsistent (FrameClass.Base : FrameClass) M)
    (φ ψ : Formula Atom) (h_psi : ψ ∈ M) : Formula.untl ψ φ ∈ M := by
  sorry

theorem backward_since_reflexive {M : Set (Formula Atom)} (h_mcs : SetMaximalConsistent (FrameClass.Base : FrameClass) M)
    (φ ψ : Formula Atom) (h_psi : ψ ∈ M) : Formula.snce ψ φ ∈ M := by
  sorry

/-! ## Parameterized Backward Until/Since -/

theorem backward_until_from_step (fam : FMCS Atom Int)
    (φ ψ : Formula Atom)
    (h_step : ∀ r : Int, Formula.untl ψ φ ∈ fam.mcs (r + 1) →
      φ ∈ fam.mcs r → Formula.untl ψ φ ∈ fam.mcs r)
    (t s : Int) (h_le : t ≤ s)
    (h_psi : ψ ∈ fam.mcs s)
    (h_guard : ∀ r : Int, t ≤ r → r < s → φ ∈ fam.mcs r) :
    Formula.untl ψ φ ∈ fam.mcs t := by
  suffices h : ∀ (d : Nat) (t' s' : Int), s' - t' = ↑d →
      ψ ∈ fam.mcs s' →
      (∀ r : Int, t' ≤ r → r < s' → φ ∈ fam.mcs r) →
      Formula.untl ψ φ ∈ fam.mcs t' by
    exact h (s - t).toNat t s (by omega) h_psi h_guard
  intro d
  induction d with
  | zero =>
    intro t' s' h_diff h_psi_s _
    have h_eq : s' = t' := by omega
    rw [h_eq] at h_psi_s
    exact backward_until_reflexive (fam.is_mcs t') φ ψ h_psi_s
  | succ d' ih =>
    intro t' s' h_diff h_psi_s h_phi_guard
    have h_U_next : Formula.untl ψ φ ∈ fam.mcs (t' + 1) := by
      apply ih (t' + 1) s' (by omega) h_psi_s
      intro r h_le_r h_r_lt
      exact h_phi_guard r (by omega) h_r_lt
    have h_phi_t : φ ∈ fam.mcs t' := h_phi_guard t' (le_refl t') (by omega)
    exact h_step t' h_U_next h_phi_t

theorem backward_since_from_step (fam : FMCS Atom Int)
    (φ ψ : Formula Atom)
    (h_step : ∀ r : Int, Formula.snce ψ φ ∈ fam.mcs (r - 1) →
      φ ∈ fam.mcs r → Formula.snce ψ φ ∈ fam.mcs r)
    (t s : Int) (h_le : s ≤ t)
    (h_psi : ψ ∈ fam.mcs s)
    (h_guard : ∀ r : Int, s < r → r ≤ t → φ ∈ fam.mcs r) :
    Formula.snce ψ φ ∈ fam.mcs t := by
  suffices h : ∀ (d : Nat) (t' s' : Int), t' - s' = ↑d →
      ψ ∈ fam.mcs s' →
      (∀ r : Int, s' < r → r ≤ t' → φ ∈ fam.mcs r) →
      Formula.snce ψ φ ∈ fam.mcs t' by
    exact h (t - s).toNat t s (by omega) h_psi h_guard
  intro d
  induction d with
  | zero =>
    intro t' s' h_diff h_psi_s _
    have h_eq : t' = s' := by omega
    rw [h_eq]
    exact backward_since_reflexive (fam.is_mcs s') φ ψ h_psi_s
  | succ d' ih =>
    intro t' s' h_diff h_psi_s h_phi_guard
    have h_S_prev : Formula.snce ψ φ ∈ fam.mcs (t' - 1) := by
      apply ih (t' - 1) s' (by omega) h_psi_s
      intro r h_lt_r h_r_le
      exact h_phi_guard r h_lt_r (by omega)
    have h_phi_t : φ ∈ fam.mcs t' := h_phi_guard t' (by omega) (le_refl t')
    exact h_step t' h_S_prev h_phi_t

/-! ## BFMCS Assembly -/

theorem backward_until_coherent (B : BFMCS Atom Int)
    (h_step : ∀ fam ∈ B.families, ∀ (φ ψ : Formula Atom) (r : Int),
      Formula.untl ψ φ ∈ fam.mcs (r + 1) → φ ∈ fam.mcs r →
      Formula.untl ψ φ ∈ fam.mcs r) :
    ∀ fam ∈ B.families, ∀ t : Int, ∀ φ ψ : Formula Atom,
      (∃ s : Int, t ≤ s ∧ ψ ∈ fam.mcs s ∧ ∀ r : Int, t ≤ r → r < s → φ ∈ fam.mcs r) →
      Formula.untl ψ φ ∈ fam.mcs t := by
  intro fam hfam t φ ψ ⟨s, h_le, h_psi, h_guard⟩
  exact backward_until_from_step fam φ ψ (h_step fam hfam φ ψ) t s h_le h_psi h_guard

theorem backward_since_coherent (B : BFMCS Atom Int)
    (h_step : ∀ fam ∈ B.families, ∀ (φ ψ : Formula Atom) (r : Int),
      Formula.snce ψ φ ∈ fam.mcs (r - 1) → φ ∈ fam.mcs r →
      Formula.snce ψ φ ∈ fam.mcs r) :
    ∀ fam ∈ B.families, ∀ t : Int, ∀ φ ψ : Formula Atom,
      (∃ s : Int, s ≤ t ∧ ψ ∈ fam.mcs s ∧ ∀ r : Int, s < r → r ≤ t → φ ∈ fam.mcs r) →
      Formula.snce ψ φ ∈ fam.mcs t := by
  intro fam hfam t φ ψ ⟨s, h_le, h_psi, h_guard⟩
  exact backward_since_from_step fam φ ψ (h_step fam hfam φ ψ) t s h_le h_psi h_guard

end Cslib.Logic.Bimodal.Metalogic.Bundle
