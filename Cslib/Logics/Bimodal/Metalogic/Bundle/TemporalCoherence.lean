/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/

import Cslib.Logics.Bimodal.Metalogic.Bundle.BFMCS
import Cslib.Logics.Bimodal.Metalogic.Bundle.ModalSaturation
import Cslib.Logics.Bimodal.Metalogic.Core.MaximalConsistent
import Cslib.Logics.Bimodal.Metalogic.Core.MCSProperties
import Cslib.Logics.Bimodal.Syntax.Formula
import Cslib.Logics.Bimodal.Syntax.SubformulaClosure.TemporalFormulas
import Cslib.Logics.Bimodal.Theorems.GeneralizedNecessitation
import Cslib.Logics.Bimodal.Theorems.TemporalDerived

/-!
# Temporal Coherence Core

Contains core temporal coherence definitions and backward lemmas.

## References

* Ported from BimodalLogic/Theories/Bimodal/Metalogic/Bundle/TemporalCoherence.lean
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Cslib.Logic.Bimodal.Metalogic.Bundle

open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Metalogic.Core

variable {Atom : Type*} {fc : FrameClass} {D : Type*} [Preorder D] [Zero D]

/-! ## Temporal Duality Infrastructure -/

private noncomputable def theorem_in_mcs_fc'' {fc : FrameClass} {M : Set (Formula Atom)} {phi : Formula Atom}
    (h_mcs : SetMaximalConsistent fc M)
    (h_deriv : DerivationTree fc [] phi) : phi ∈ M :=
  SetMaximalConsistent.closed_under_derivation h_mcs [] (fun _ h => by simp at h) h_deriv

noncomputable def G_dne_theorem (phi : Formula Atom) :
    DerivationTree FrameClass.Base [] ((Formula.all_future (Formula.neg (Formula.neg phi))).imp (Formula.all_future phi)) := by
  have h_dne : DerivationTree FrameClass.Base [] ((Formula.neg (Formula.neg phi)).imp phi) :=
    dne_theorem phi
  have h_G_dne : DerivationTree FrameClass.Base [] (Formula.all_future ((Formula.neg (Formula.neg phi)).imp phi)) :=
    DerivationTree.temporal_necessitation _ h_dne
  have h_K : DerivationTree FrameClass.Base [] ((Formula.all_future ((Formula.neg (Formula.neg phi)).imp phi)).imp
               ((Formula.all_future (Formula.neg (Formula.neg phi))).imp (Formula.all_future phi))) :=
    Theorems.TemporalDerived.temp_k_dist_derived (Formula.neg (Formula.neg phi)) phi
  exact DerivationTree.modus_ponens [] _ _ h_K h_G_dne

noncomputable def H_dne_theorem (phi : Formula Atom) :
    DerivationTree FrameClass.Base [] ((Formula.all_past (Formula.neg (Formula.neg phi))).imp (Formula.all_past phi)) := by
  have h_dne : DerivationTree FrameClass.Base [] ((Formula.neg (Formula.neg phi)).imp phi) :=
    dne_theorem phi
  have h_H_dne : DerivationTree FrameClass.Base [] (Formula.all_past ((Formula.neg (Formula.neg phi)).imp phi)) :=
    Theorems.past_necessitation _ h_dne
  have h_K : DerivationTree FrameClass.Base [] ((Formula.all_past ((Formula.neg (Formula.neg phi)).imp phi)).imp
               ((Formula.all_past (Formula.neg (Formula.neg phi))).imp (Formula.all_past phi))) :=
    Theorems.past_k_dist _ _
  exact DerivationTree.modus_ponens [] _ _ h_K h_H_dne

lemma neg_all_future_to_some_future_neg (M : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc M)
    (phi : Formula Atom) (h_neg_G : Formula.neg (Formula.all_future phi) ∈ M) :
    Formula.some_future (Formula.neg phi) ∈ M := by
  have h_eq : Formula.neg (Formula.all_future phi) =
              Formula.neg (Formula.neg (Formula.some_future (Formula.neg phi))) := rfl
  rw [h_eq] at h_neg_G
  have h_dne : DerivationTree fc [] ((Formula.neg (Formula.neg (Formula.some_future (Formula.neg phi)))).imp
                     (Formula.some_future (Formula.neg phi))) :=
    (dne_theorem (Formula.some_future (Formula.neg phi))).lift (FrameClass.base_le fc)
  exact SetMaximalConsistent.implication_property h_mcs (theorem_in_mcs_fc'' h_mcs h_dne) h_neg_G

lemma neg_all_past_to_some_past_neg (M : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc M)
    (phi : Formula Atom) (h_neg_H : Formula.neg (Formula.all_past phi) ∈ M) :
    Formula.some_past (Formula.neg phi) ∈ M := by
  have h_eq : Formula.neg (Formula.all_past phi) =
              Formula.neg (Formula.neg (Formula.some_past (Formula.neg phi))) := rfl
  rw [h_eq] at h_neg_H
  have h_dne : DerivationTree fc [] ((Formula.neg (Formula.neg (Formula.some_past (Formula.neg phi)))).imp
                     (Formula.some_past (Formula.neg phi))) :=
    (dne_theorem (Formula.some_past (Formula.neg phi))).lift (FrameClass.base_le fc)
  exact SetMaximalConsistent.implication_property h_mcs (theorem_in_mcs_fc'' h_mcs h_dne) h_neg_H

lemma SetMaximalConsistent.double_neg_elim {M : Set (Formula Atom)} (h_mcs : SetMaximalConsistent fc M)
    (phi : Formula Atom) (h_neg_neg : Formula.neg (Formula.neg phi) ∈ M) : phi ∈ M := by
  have h_dne : DerivationTree fc [] ((Formula.neg (Formula.neg phi)).imp phi) :=
    (dne_theorem phi).lift (FrameClass.base_le fc)
  have h_thm_in_M : (Formula.neg (Formula.neg phi)).imp phi ∈ M := theorem_in_mcs_fc'' h_mcs h_dne
  exact SetMaximalConsistent.implication_property h_mcs h_thm_in_M h_neg_neg

/-! ## TemporalCoherentFamily and Backward Lemmas -/

structure TemporalCoherentFamily (Atom : Type*) (fc : FrameClass := FrameClass.Base) (D : Type*) [Preorder D] [Zero D] extends FMCS Atom D fc where
  forward_F : ∀ t : D, ∀ φ : Formula Atom,
    Formula.some_future φ ∈ mcs t → ∃ s : D, t < s ∧ φ ∈ mcs s
  backward_P : ∀ t : D, ∀ φ : Formula Atom,
    Formula.some_past φ ∈ mcs t → ∃ s : D, s < t ∧ φ ∈ mcs s

theorem temporal_backward_G (fam : TemporalCoherentFamily Atom fc D) (t : D) (φ : Formula Atom)
    (h_all : ∀ s : D, t ≤ s → φ ∈ fam.mcs s) :
    Formula.all_future φ ∈ fam.mcs t := by
  by_contra h_not_G
  have h_mcs := fam.is_mcs t
  have h_neg_G : Formula.neg (Formula.all_future φ) ∈ fam.mcs t := by
    rcases SetMaximalConsistent.negation_complete h_mcs (Formula.all_future φ) with h_G | h_neg
    · exact absurd h_G h_not_G
    · exact h_neg
  have h_F_neg : Formula.some_future (Formula.neg φ) ∈ fam.mcs t :=
    neg_all_future_to_some_future_neg (fam.mcs t) h_mcs φ h_neg_G
  obtain ⟨s, h_lt, h_neg_phi_s⟩ := fam.forward_F t (Formula.neg φ) h_F_neg
  have h_phi_s : φ ∈ fam.mcs s := h_all s (le_of_lt h_lt)
  exact set_consistent_not_both (fam.is_mcs s).1 φ h_phi_s h_neg_phi_s

theorem temporal_backward_H (fam : TemporalCoherentFamily Atom fc D) (t : D) (φ : Formula Atom)
    (h_all : ∀ s : D, s ≤ t → φ ∈ fam.mcs s) :
    Formula.all_past φ ∈ fam.mcs t := by
  by_contra h_not_H
  have h_mcs := fam.is_mcs t
  have h_neg_H : Formula.neg (Formula.all_past φ) ∈ fam.mcs t := by
    rcases SetMaximalConsistent.negation_complete h_mcs (Formula.all_past φ) with h_H | h_neg
    · exact absurd h_H h_not_H
    · exact h_neg
  have h_P_neg : Formula.some_past (Formula.neg φ) ∈ fam.mcs t :=
    neg_all_past_to_some_past_neg (fam.mcs t) h_mcs φ h_neg_H
  obtain ⟨s, h_lt, h_neg_phi_s⟩ := fam.backward_P t (Formula.neg φ) h_P_neg
  have h_phi_s : φ ∈ fam.mcs s := h_all s (le_of_lt h_lt)
  exact set_consistent_not_both (fam.is_mcs s).1 φ h_phi_s h_neg_phi_s

theorem temporal_backward_G_with_fwd_F {D : Type*} [Preorder D]
    (fam : FMCS Atom D fc) (t : D) (φ : Formula Atom)
    (h_forward_F_neg : Formula.some_future (Formula.neg φ) ∈ fam.mcs t →
      ∃ s : D, t < s ∧ (Formula.neg φ) ∈ fam.mcs s)
    (h_all : ∀ s : D, t < s → φ ∈ fam.mcs s) :
    Formula.all_future φ ∈ fam.mcs t := by
  by_contra h_not_G
  have h_mcs := fam.is_mcs t
  have h_neg_G : Formula.neg (Formula.all_future φ) ∈ fam.mcs t := by
    rcases SetMaximalConsistent.negation_complete h_mcs (Formula.all_future φ) with h_G | h_neg
    · exact absurd h_G h_not_G
    · exact h_neg
  have h_F_neg : Formula.some_future (Formula.neg φ) ∈ fam.mcs t :=
    neg_all_future_to_some_future_neg (fam.mcs t) h_mcs φ h_neg_G
  obtain ⟨s, h_le, h_neg_phi_s⟩ := h_forward_F_neg h_F_neg
  have h_phi_s : φ ∈ fam.mcs s := h_all s h_le
  exact set_consistent_not_both (fam.is_mcs s).1 φ h_phi_s h_neg_phi_s

theorem temporal_backward_H_with_bwd_P {D : Type*} [Preorder D]
    (fam : FMCS Atom D fc) (t : D) (φ : Formula Atom)
    (h_backward_P_neg : Formula.some_past (Formula.neg φ) ∈ fam.mcs t →
      ∃ s : D, s < t ∧ (Formula.neg φ) ∈ fam.mcs s)
    (h_all : ∀ s : D, s < t → φ ∈ fam.mcs s) :
    Formula.all_past φ ∈ fam.mcs t := by
  by_contra h_not_H
  have h_mcs := fam.is_mcs t
  have h_neg_H : Formula.neg (Formula.all_past φ) ∈ fam.mcs t := by
    rcases SetMaximalConsistent.negation_complete h_mcs (Formula.all_past φ) with h_H | h_neg
    · exact absurd h_H h_not_H
    · exact h_neg
  have h_P_neg : Formula.some_past (Formula.neg φ) ∈ fam.mcs t :=
    neg_all_past_to_some_past_neg (fam.mcs t) h_mcs φ h_neg_H
  obtain ⟨s, h_le, h_neg_phi_s⟩ := h_backward_P_neg h_P_neg
  have h_phi_s : φ ∈ fam.mcs s := h_all s h_le
  exact set_consistent_not_both (fam.is_mcs s).1 φ h_phi_s h_neg_phi_s

/-! ## BFMCS Temporal Coherence Predicates -/

def BFMCS.temporally_coherent (B : BFMCS Atom D fc) : Prop :=
  ∀ fam ∈ B.families,
    (∀ t : D, ∀ φ : Formula Atom, Formula.some_future φ ∈ fam.mcs t → ∃ s : D, t < s ∧ φ ∈ fam.mcs s) ∧
    (∀ t : D, ∀ φ : Formula Atom, Formula.some_past φ ∈ fam.mcs t → ∃ s : D, s < t ∧ φ ∈ fam.mcs s)

/-! ## Restricted Temporal Coherence -/

section DecidableAtom
variable [DecidableEq Atom]

def BFMCS.restricted_temporally_coherent (B : BFMCS Atom D fc) (root : Formula Atom) : Prop :=
  ∀ fam ∈ B.families,
    (∀ t : D, ∀ φ : Formula Atom, φ ∈ deferralClosure root →
      Formula.some_future φ ∈ fam.mcs t → ∃ s : D, t < s ∧ φ ∈ fam.mcs s) ∧
    (∀ t : D, ∀ φ : Formula Atom, φ ∈ deferralClosure root →
      Formula.some_past φ ∈ fam.mcs t → ∃ s : D, s < t ∧ φ ∈ fam.mcs s)

omit [Zero D] in
theorem BFMCS.temporally_coherent_implies_restricted (B : BFMCS Atom D fc) (root : Formula Atom)
    (h_tc : B.temporally_coherent) : B.restricted_temporally_coherent root := by
  intro fam hfam
  obtain ⟨h_F, h_P⟩ := h_tc fam hfam
  exact ⟨fun t φ _ h_F_in => h_F t φ h_F_in, fun t φ _ h_P_in => h_P t φ h_P_in⟩

/-! ## Restricted Temporal Backward Lemmas -/

omit [Zero D] in
theorem restricted_temporal_backward_G
    (fam : FMCS Atom D fc) (root : Formula Atom)
    (h_forward_F : ∀ t : D, ∀ φ : Formula Atom, φ ∈ deferralClosure root →
      Formula.some_future φ ∈ fam.mcs t → ∃ s : D, t ≤ s ∧ φ ∈ fam.mcs s)
    (t : D) (φ : Formula Atom)
    (h_neg_phi_dc : Formula.neg φ ∈ deferralClosure root)
    (h_all : ∀ s : D, t ≤ s → φ ∈ fam.mcs s) :
    Formula.all_future φ ∈ fam.mcs t := by
  by_contra h_not_G
  have h_mcs := fam.is_mcs t
  have h_neg_G : Formula.neg (Formula.all_future φ) ∈ fam.mcs t := by
    rcases SetMaximalConsistent.negation_complete h_mcs (Formula.all_future φ) with h_G | h_neg
    · exact absurd h_G h_not_G
    · exact h_neg
  have h_F_neg : Formula.some_future (Formula.neg φ) ∈ fam.mcs t :=
    neg_all_future_to_some_future_neg (fam.mcs t) h_mcs φ h_neg_G
  obtain ⟨s, h_le, h_neg_phi_s⟩ := h_forward_F t (Formula.neg φ) h_neg_phi_dc h_F_neg
  have h_phi_s : φ ∈ fam.mcs s := h_all s h_le
  exact set_consistent_not_both (fam.is_mcs s).1 φ h_phi_s h_neg_phi_s

omit [Zero D] in
theorem restricted_temporal_backward_H
    (fam : FMCS Atom D fc) (root : Formula Atom)
    (h_backward_P : ∀ t : D, ∀ φ : Formula Atom, φ ∈ deferralClosure root →
      Formula.some_past φ ∈ fam.mcs t → ∃ s : D, s ≤ t ∧ φ ∈ fam.mcs s)
    (t : D) (φ : Formula Atom)
    (h_neg_phi_dc : Formula.neg φ ∈ deferralClosure root)
    (h_all : ∀ s : D, s ≤ t → φ ∈ fam.mcs s) :
    Formula.all_past φ ∈ fam.mcs t := by
  by_contra h_not_H
  have h_mcs := fam.is_mcs t
  have h_neg_H : Formula.neg (Formula.all_past φ) ∈ fam.mcs t := by
    rcases SetMaximalConsistent.negation_complete h_mcs (Formula.all_past φ) with h_H | h_neg
    · exact absurd h_H h_not_H
    · exact h_neg
  have h_P_neg : Formula.some_past (Formula.neg φ) ∈ fam.mcs t :=
    neg_all_past_to_some_past_neg (fam.mcs t) h_mcs φ h_neg_H
  obtain ⟨s, h_le, h_neg_phi_s⟩ := h_backward_P t (Formula.neg φ) h_neg_phi_dc h_P_neg
  have h_phi_s : φ ∈ fam.mcs s := h_all s h_le
  exact set_consistent_not_both (fam.is_mcs s).1 φ h_phi_s h_neg_phi_s

omit [Zero D] in
theorem restricted_temporal_backward_G_strict
    (fam : FMCS Atom D fc) (root : Formula Atom)
    (h_forward_F : ∀ t : D, ∀ φ : Formula Atom, φ ∈ deferralClosure root →
      Formula.some_future φ ∈ fam.mcs t → ∃ s : D, t < s ∧ φ ∈ fam.mcs s)
    (t : D) (φ : Formula Atom)
    (h_neg_phi_dc : Formula.neg φ ∈ deferralClosure root)
    (h_all : ∀ s : D, t < s → φ ∈ fam.mcs s) :
    Formula.all_future φ ∈ fam.mcs t := by
  by_contra h_not_G
  have h_mcs := fam.is_mcs t
  have h_neg_G : Formula.neg (Formula.all_future φ) ∈ fam.mcs t := by
    rcases SetMaximalConsistent.negation_complete h_mcs (Formula.all_future φ) with h_G | h_neg
    · exact absurd h_G h_not_G
    · exact h_neg
  have h_F_neg : Formula.some_future (Formula.neg φ) ∈ fam.mcs t :=
    neg_all_future_to_some_future_neg (fam.mcs t) h_mcs φ h_neg_G
  obtain ⟨s, h_lt, h_neg_phi_s⟩ := h_forward_F t (Formula.neg φ) h_neg_phi_dc h_F_neg
  have h_phi_s : φ ∈ fam.mcs s := h_all s h_lt
  exact set_consistent_not_both (fam.is_mcs s).1 φ h_phi_s h_neg_phi_s

omit [Zero D] in
theorem restricted_temporal_backward_H_strict
    (fam : FMCS Atom D fc) (root : Formula Atom)
    (h_backward_P : ∀ t : D, ∀ φ : Formula Atom, φ ∈ deferralClosure root →
      Formula.some_past φ ∈ fam.mcs t → ∃ s : D, s < t ∧ φ ∈ fam.mcs s)
    (t : D) (φ : Formula Atom)
    (h_neg_phi_dc : Formula.neg φ ∈ deferralClosure root)
    (h_all : ∀ s : D, s < t → φ ∈ fam.mcs s) :
    Formula.all_past φ ∈ fam.mcs t := by
  by_contra h_not_H
  have h_mcs := fam.is_mcs t
  have h_neg_H : Formula.neg (Formula.all_past φ) ∈ fam.mcs t := by
    rcases SetMaximalConsistent.negation_complete h_mcs (Formula.all_past φ) with h_H | h_neg
    · exact absurd h_H h_not_H
    · exact h_neg
  have h_P_neg : Formula.some_past (Formula.neg φ) ∈ fam.mcs t :=
    neg_all_past_to_some_past_neg (fam.mcs t) h_mcs φ h_neg_H
  obtain ⟨s, h_lt, h_neg_phi_s⟩ := h_backward_P t (Formula.neg φ) h_neg_phi_dc h_P_neg
  have h_phi_s : φ ∈ fam.mcs s := h_all s h_lt
  exact set_consistent_not_both (fam.is_mcs s).1 φ h_phi_s h_neg_phi_s

end DecidableAtom

/-! ## Until/Since Coherence -/

def BFMCS.until_since_coherent (B : BFMCS Atom D fc) : Prop :=
  ∀ fam ∈ B.families,
    (∀ t : D, ∀ φ ψ : Formula Atom,
      Formula.untl φ ψ ∈ fam.mcs t →
      ∃ s : D, t < s ∧ φ ∈ fam.mcs s ∧ ∀ r : D, t < r → r < s → ψ ∈ fam.mcs r) ∧
    (∀ t : D, ∀ φ ψ : Formula Atom,
      (∃ s : D, t < s ∧ φ ∈ fam.mcs s ∧ ∀ r : D, t < r → r < s → ψ ∈ fam.mcs r) →
      Formula.untl φ ψ ∈ fam.mcs t) ∧
    (∀ t : D, ∀ φ ψ : Formula Atom,
      Formula.snce φ ψ ∈ fam.mcs t →
      ∃ s : D, s < t ∧ φ ∈ fam.mcs s ∧ ∀ r : D, s < r → r < t → ψ ∈ fam.mcs r) ∧
    (∀ t : D, ∀ φ ψ : Formula Atom,
      (∃ s : D, s < t ∧ φ ∈ fam.mcs s ∧ ∀ r : D, s < r → r < t → ψ ∈ fam.mcs r) →
      Formula.snce φ ψ ∈ fam.mcs t)

/-! ## Split Until/Since Coherence -/

def BFMCS.backward_until_since_coherent (B : BFMCS Atom D fc) : Prop :=
  ∀ fam ∈ B.families,
    (∀ t : D, ∀ φ ψ : Formula Atom,
      (∃ s : D, t < s ∧ φ ∈ fam.mcs s ∧ ∀ r : D, t < r → r < s → ψ ∈ fam.mcs r) →
      Formula.untl φ ψ ∈ fam.mcs t) ∧
    (∀ t : D, ∀ φ ψ : Formula Atom,
      (∃ s : D, s < t ∧ φ ∈ fam.mcs s ∧ ∀ r : D, s < r → r < t → ψ ∈ fam.mcs r) →
      Formula.snce φ ψ ∈ fam.mcs t)

def BFMCS.forward_until_since_coherent (B : BFMCS Atom D fc) : Prop :=
  ∀ fam ∈ B.families,
    (∀ t : D, ∀ φ ψ : Formula Atom,
      Formula.untl φ ψ ∈ fam.mcs t →
      ∃ s : D, t < s ∧ φ ∈ fam.mcs s ∧ ∀ r : D, t < r → r < s → ψ ∈ fam.mcs r) ∧
    (∀ t : D, ∀ φ ψ : Formula Atom,
      Formula.snce φ ψ ∈ fam.mcs t →
      ∃ s : D, s < t ∧ φ ∈ fam.mcs s ∧ ∀ r : D, s < r → r < t → ψ ∈ fam.mcs r)

/-! ## Restricted forward/backward Until/Since Coherence -/

section DecidableAtom2
variable [DecidableEq Atom]

def BFMCS.restricted_forward_until_since_coherent (B : BFMCS Atom D fc) (root : Formula Atom) : Prop :=
  ∀ fam ∈ B.families,
    (∀ t : D, ∀ φ ψ : Formula Atom,
      Formula.untl φ ψ ∈ subformulaClosure root →
      Formula.untl φ ψ ∈ fam.mcs t →
      ∃ s : D, t < s ∧ φ ∈ fam.mcs s ∧ ∀ r : D, t < r → r < s → ψ ∈ fam.mcs r) ∧
    (∀ t : D, ∀ φ ψ : Formula Atom,
      Formula.snce φ ψ ∈ subformulaClosure root →
      Formula.snce φ ψ ∈ fam.mcs t →
      ∃ s : D, s < t ∧ φ ∈ fam.mcs s ∧ ∀ r : D, s < r → r < t → ψ ∈ fam.mcs r)

omit [Zero D] in
theorem BFMCS.forward_implies_restricted_forward (B : BFMCS Atom D fc) (root : Formula Atom)
    (h_fuc : B.forward_until_since_coherent) :
    B.restricted_forward_until_since_coherent root := by
  intro fam hfam
  obtain ⟨h_fwd_U, h_fwd_S⟩ := h_fuc fam hfam
  exact ⟨fun t φ ψ _ h_mem => h_fwd_U t φ ψ h_mem,
         fun t φ ψ _ h_mem => h_fwd_S t φ ψ h_mem⟩

def BFMCS.restricted_backward_until_since_coherent (B : BFMCS Atom D fc) (root : Formula Atom) : Prop :=
  ∀ fam ∈ B.families,
    (∀ t : D, ∀ φ ψ : Formula Atom,
      Formula.untl φ ψ ∈ subformulaClosure root →
      (∃ s : D, t < s ∧ φ ∈ fam.mcs s ∧ ∀ r : D, t < r → r < s → ψ ∈ fam.mcs r) →
      Formula.untl φ ψ ∈ fam.mcs t) ∧
    (∀ t : D, ∀ φ ψ : Formula Atom,
      Formula.snce φ ψ ∈ subformulaClosure root →
      (∃ s : D, s < t ∧ φ ∈ fam.mcs s ∧ ∀ r : D, s < r → r < t → ψ ∈ fam.mcs r) →
      Formula.snce φ ψ ∈ fam.mcs t)

omit [Zero D] in
theorem BFMCS.backward_implies_restricted_backward (B : BFMCS Atom D fc) (root : Formula Atom)
    (h_buc : B.backward_until_since_coherent) :
    B.restricted_backward_until_since_coherent root := by
  intro fam hfam
  obtain ⟨h_bwd_U, h_bwd_S⟩ := h_buc fam hfam
  exact ⟨fun t φ ψ _ h_wit => h_bwd_U t φ ψ h_wit,
         fun t φ ψ _ h_wit => h_bwd_S t φ ψ h_wit⟩

end DecidableAtom2

omit [Zero D] in
theorem BFMCS.split_until_since_coherent (B : BFMCS Atom D fc)
    (h_buc : B.backward_until_since_coherent) (h_fuc : B.forward_until_since_coherent) :
    B.until_since_coherent := by
  intro fam hfam
  obtain ⟨h_bwd_U, h_bwd_S⟩ := h_buc fam hfam
  obtain ⟨h_fwd_U, h_fwd_S⟩ := h_fuc fam hfam
  exact ⟨h_fwd_U, h_bwd_U, h_fwd_S, h_bwd_S⟩

omit [Zero D] in
theorem BFMCS.until_since_coherent_backward (B : BFMCS Atom D fc)
    (h_uc : B.until_since_coherent) : B.backward_until_since_coherent := by
  intro fam hfam
  obtain ⟨_, h_bwd_U, _, h_bwd_S⟩ := h_uc fam hfam
  exact ⟨h_bwd_U, h_bwd_S⟩

omit [Zero D] in
theorem BFMCS.until_since_coherent_forward (B : BFMCS Atom D fc)
    (h_uc : B.until_since_coherent) : B.forward_until_since_coherent := by
  intro fam hfam
  obtain ⟨h_fwd_U, _, h_fwd_S, _⟩ := h_uc fam hfam
  exact ⟨h_fwd_U, h_fwd_S⟩

end Cslib.Logic.Bimodal.Metalogic.Bundle
