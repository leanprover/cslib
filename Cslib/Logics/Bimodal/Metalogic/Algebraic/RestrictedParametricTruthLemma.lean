/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.Algebraic.ParametricTruthLemma
public import Cslib.Logics.Bimodal.Metalogic.Bundle.TemporalCoherence
public import Cslib.Logics.Bimodal.Syntax.SubformulaClosure.TemporalFormulas

/-!
# Restricted Parametric Truth Lemma

Restricted version of the parametric shifted truth lemma that only requires
`B.restricted_temporally_coherent root` instead of full `B.temporally_coherent`.

## References

* Ported from BimodalLogic/Theories/Bimodal/Metalogic/Algebraic/RestrictedParametricTruthLemma.lean
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.Algebraic.RestrictedParametricTruthLemma

open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Metalogic.Core
open Cslib.Logic.Bimodal.Metalogic.Bundle
open Cslib.Logic.Bimodal.Metalogic.Algebraic.ParametricCanonical
open Cslib.Logic.Bimodal.Metalogic.Algebraic.ParametricHistory
open Cslib.Logic.Bimodal.Metalogic.Algebraic.ParametricTruthLemma
open Cslib.Logic.Bimodal

variable {Atom : Type} [DecidableEq Atom] {fc : FrameClass} {D : Type*} [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]

private noncomputable def theorem_in_mcs_fc {M : Set (Formula Atom)} {phi : Formula Atom}
    (h_mcs : SetMaximalConsistent fc M)
    (h_deriv : DerivationTree fc [] phi) : phi ∈ M :=
  SetMaximalConsistent.closed_under_derivation h_mcs [] (fun _ h => by simp at h) h_deriv

private noncomputable def neg_imp_implies_antecedent (ψ χ : Formula Atom) :
    DerivationTree fc [] ((ψ.imp χ).neg.imp ψ) := by
  have h_efq : DerivationTree FrameClass.Base [] (ψ.neg.imp (ψ.imp χ)) :=
    Theorems.Propositional.efq_neg ψ χ
  have h_efq_ctx : DerivationTree FrameClass.Base [ψ.neg, (ψ.imp χ).neg] (ψ.neg.imp (ψ.imp χ)) :=
    DerivationTree.weakening [] [ψ.neg, (ψ.imp χ).neg] _ h_efq (by intro; simp)
  have h_neg_psi : DerivationTree FrameClass.Base [ψ.neg, (ψ.imp χ).neg] ψ.neg :=
    DerivationTree.assumption _ _ (by simp)
  have h_imp : DerivationTree FrameClass.Base [ψ.neg, (ψ.imp χ).neg] (ψ.imp χ) :=
    DerivationTree.modus_ponens _ _ _ h_efq_ctx h_neg_psi
  have h_neg_imp : DerivationTree FrameClass.Base [ψ.neg, (ψ.imp χ).neg] (ψ.imp χ).neg :=
    DerivationTree.assumption _ _ (by simp)
  have h_bot : DerivationTree FrameClass.Base [ψ.neg, (ψ.imp χ).neg] (Formula.bot : Formula Atom) :=
    DerivationTree.modus_ponens _ _ _ h_neg_imp h_imp
  have h_neg_neg_psi : DerivationTree FrameClass.Base [(ψ.imp χ).neg] ψ.neg.neg :=
    deduction_theorem [(ψ.imp χ).neg] ψ.neg (Formula.bot : Formula Atom) h_bot
  have h_deduct : DerivationTree FrameClass.Base [] ((ψ.imp χ).neg.imp ψ.neg.neg) :=
    deduction_theorem [] (ψ.imp χ).neg ψ.neg.neg h_neg_neg_psi
  have h_dne : DerivationTree FrameClass.Base [] (ψ.neg.neg.imp ψ) :=
    Theorems.Propositional.double_negation ψ
  have h_b : DerivationTree FrameClass.Base [] ((ψ.neg.neg.imp ψ).imp (((ψ.imp χ).neg.imp ψ.neg.neg).imp ((ψ.imp χ).neg.imp ψ))) :=
    Theorems.Combinators.b_combinator
  have h_step1 : DerivationTree FrameClass.Base [] (((ψ.imp χ).neg.imp ψ.neg.neg).imp ((ψ.imp χ).neg.imp ψ)) :=
    DerivationTree.modus_ponens _ _ _ h_b h_dne
  have h_base : DerivationTree FrameClass.Base [] ((ψ.imp χ).neg.imp ψ) :=
    DerivationTree.modus_ponens _ _ _ h_step1 h_deduct
  exact h_base.lift (FrameClass.base_le fc)

private noncomputable def neg_imp_implies_neg_consequent (ψ χ : Formula Atom) :
    DerivationTree fc [] ((ψ.imp χ).neg.imp χ.neg) := by
  have h_prop_s : DerivationTree FrameClass.Base [] (χ.imp (ψ.imp χ)) :=
    DerivationTree.axiom [] _ (Axiom.imp_s χ ψ) trivial
  have h_prop_s_ctx : DerivationTree FrameClass.Base [χ, (ψ.imp χ).neg] (χ.imp (ψ.imp χ)) :=
    DerivationTree.weakening [] [χ, (ψ.imp χ).neg] _ h_prop_s (by intro; simp)
  have h_chi : DerivationTree FrameClass.Base [χ, (ψ.imp χ).neg] χ :=
    DerivationTree.assumption _ _ (by simp)
  have h_imp : DerivationTree FrameClass.Base [χ, (ψ.imp χ).neg] (ψ.imp χ) :=
    DerivationTree.modus_ponens _ _ _ h_prop_s_ctx h_chi
  have h_neg_imp : DerivationTree FrameClass.Base [χ, (ψ.imp χ).neg] (ψ.imp χ).neg :=
    DerivationTree.assumption _ _ (by simp)
  have h_bot : DerivationTree FrameClass.Base [χ, (ψ.imp χ).neg] (Formula.bot : Formula Atom) :=
    DerivationTree.modus_ponens _ _ _ h_neg_imp h_imp
  have h_neg_chi : DerivationTree FrameClass.Base [(ψ.imp χ).neg] χ.neg :=
    deduction_theorem [(ψ.imp χ).neg] χ (Formula.bot : Formula Atom) h_bot
  have h_base : DerivationTree FrameClass.Base [] ((ψ.imp χ).neg.imp χ.neg) :=
    deduction_theorem [] (ψ.imp χ).neg χ.neg h_neg_chi
  exact h_base.lift (FrameClass.base_le fc)

/-- Restricted parametric shifted truth lemma. -/
theorem restricted_parametric_shifted_truth_lemma (B : BFMCS Atom D fc)
    (root : Formula Atom)
    (_h_rtc : B.restricted_temporally_coherent root)
    (h_buc : B.backward_until_since_coherent)
    (h_fuc : B.forward_until_since_coherent) (φ : Formula Atom)
    (h_sub : φ ∈ subformulaClosure root)
    (fam : FMCS Atom D fc) (hfam : fam ∈ B.families) (t : D) :
    φ ∈ fam.mcs t ↔
    truth_at ParametricCanonicalTaskModel (ShiftClosedParametricCanonicalOmega B)
      (parametric_to_history fam) t φ := by
  induction φ generalizing fam t with
  | atom p =>
    simp only [truth_at, ParametricCanonicalTaskModel, parametric_to_history]
    exact ⟨fun h => ⟨True.intro, h⟩, fun ⟨_, h⟩ => h⟩
  | bot =>
    simp only [truth_at]
    exact ⟨fun h => absurd h (fun h_bot => (fam.is_mcs t).1 [(Formula.bot : Formula Atom)]
      (fun psi hpsi => by simp at hpsi; rw [hpsi]; exact h_bot)
      ⟨DerivationTree.assumption [(Formula.bot : Formula Atom)] (Formula.bot : Formula Atom) (by simp)⟩),
      fun h => h.elim⟩
  | imp ψ χ ih_ψ ih_χ =>
    have h_ψ_sub := closure_imp_left root ψ χ h_sub
    have h_χ_sub := closure_imp_right root ψ χ h_sub
    simp only [truth_at]
    have h_mcs := fam.is_mcs t
    constructor
    · intro h_imp h_ψ_true
      exact (ih_χ h_χ_sub fam hfam t).mp
        (SetMaximalConsistent.implication_property h_mcs h_imp ((ih_ψ h_ψ_sub fam hfam t).mpr h_ψ_true))
    · intro h_truth_imp
      rcases SetMaximalConsistent.negation_complete h_mcs (ψ.imp χ) with h_imp | h_neg_imp
      · exact h_imp
      · exfalso
        have h_ψ_mcs : ψ ∈ fam.mcs t :=
          SetMaximalConsistent.implication_property h_mcs
            (theorem_in_mcs_fc h_mcs (neg_imp_implies_antecedent ψ χ)) h_neg_imp
        have h_neg_χ_mcs : χ.neg ∈ fam.mcs t :=
          SetMaximalConsistent.implication_property h_mcs
            (theorem_in_mcs_fc h_mcs (neg_imp_implies_neg_consequent ψ χ)) h_neg_imp
        exact set_consistent_not_both h_mcs.1 χ
          ((ih_χ h_χ_sub fam hfam t).mpr (h_truth_imp ((ih_ψ h_ψ_sub fam hfam t).mp h_ψ_mcs)))
          h_neg_χ_mcs
  | box ψ ih =>
    have h_ψ_sub := closure_box root ψ h_sub
    constructor
    · intro h_box σ h_σ_mem
      obtain ⟨fam', hfam', delta, h_σ_eq⟩ := h_σ_mem
      have h_box_shifted := parametric_box_persistent fam ψ t (t + delta) h_box
      have h_ψ_fam' := B.modal_forward fam hfam ψ (t + delta) h_box_shifted fam' hfam'
      have h_truth_canon := (ih h_ψ_sub fam' hfam' (t + delta)).mp h_ψ_fam'
      have h_preserve := TimeShift.time_shift_preserves_truth
        ParametricCanonicalTaskModel (ShiftClosedParametricCanonicalOmega B)
        (shiftClosedParametricCanonicalOmega_is_shift_closed B) (parametric_to_history fam')
        t (t + delta) ψ
      have h_delta : (t + delta) - t = delta := add_sub_cancel_left t delta
      rw [h_σ_eq]
      rw [WorldHistory.time_shift_congr (parametric_to_history fam') ((t + delta) - t) delta h_delta] at h_preserve
      exact h_preserve.mpr h_truth_canon
    · intro h_all_σ
      exact B.modal_backward fam hfam ψ t (fun fam' hfam' =>
        (ih h_ψ_sub fam' hfam' t).mpr
          (h_all_σ (parametric_to_history fam') (parametricCanonicalOmega_subset_shiftClosed B ⟨fam', hfam', rfl⟩)))
  | untl phi psi ih_phi ih_psi =>
    have h_phi_sub := closure_untl_left root phi psi h_sub
    have h_psi_sub := closure_untl_right root phi psi h_sub
    simp only [truth_at]
    obtain ⟨h_fwd_U, _⟩ := h_fuc fam hfam
    obtain ⟨h_bwd_U, _⟩ := h_buc fam hfam
    constructor
    · intro h_U
      obtain ⟨s, h_ts, h_phi_s, h_psi_guard⟩ := h_fwd_U t phi psi h_U
      exact ⟨s, h_ts, (ih_phi h_phi_sub fam hfam s).mp h_phi_s,
        fun r h_tr h_rs => (ih_psi h_psi_sub fam hfam r).mp (h_psi_guard r h_tr h_rs)⟩
    · intro ⟨s, h_ts, h_truth_phi_s, h_truth_psi_guard⟩
      exact h_bwd_U t phi psi ⟨s, h_ts,
        (ih_phi h_phi_sub fam hfam s).mpr h_truth_phi_s,
        fun r h_tr h_rs => (ih_psi h_psi_sub fam hfam r).mpr (h_truth_psi_guard r h_tr h_rs)⟩
  | snce phi psi ih_phi ih_psi =>
    have h_phi_sub := closure_snce_left root phi psi h_sub
    have h_psi_sub := closure_snce_right root phi psi h_sub
    simp only [truth_at]
    obtain ⟨_, h_fwd_S⟩ := h_fuc fam hfam
    obtain ⟨_, h_bwd_S⟩ := h_buc fam hfam
    constructor
    · intro h_S
      obtain ⟨s, h_st, h_phi_s, h_psi_guard⟩ := h_fwd_S t phi psi h_S
      exact ⟨s, h_st, (ih_phi h_phi_sub fam hfam s).mp h_phi_s,
        fun r h_sr h_rt => (ih_psi h_psi_sub fam hfam r).mp (h_psi_guard r h_sr h_rt)⟩
    · intro ⟨s, h_st, h_truth_phi_s, h_truth_psi_guard⟩
      exact h_bwd_S t phi psi ⟨s, h_st,
        (ih_phi h_phi_sub fam hfam s).mpr h_truth_phi_s,
        fun r h_sr h_rt => (ih_psi h_psi_sub fam hfam r).mpr (h_truth_psi_guard r h_sr h_rt)⟩

/-- Restricted completeness from neg membership. -/
theorem restricted_parametric_completeness_from_neg_membership
    (B : BFMCS Atom D fc) (root : Formula Atom)
    (h_rtc : B.restricted_temporally_coherent root)
    (h_buc : B.backward_until_since_coherent)
    (h_fuc : B.forward_until_since_coherent)
    (φ : Formula Atom) (h_sub : φ ∈ subformulaClosure root)
    (fam : FMCS Atom D fc) (hfam : fam ∈ B.families)
    (t : D) (h_neg_in : φ.neg ∈ fam.mcs t) :
    ¬truth_at ParametricCanonicalTaskModel (ShiftClosedParametricCanonicalOmega B)
      (parametric_to_history fam) t φ := by
  intro h_phi_true
  exact set_consistent_not_both (fam.is_mcs t).1 φ
    ((restricted_parametric_shifted_truth_lemma B root h_rtc h_buc h_fuc φ h_sub fam hfam t).mpr h_phi_true)
    h_neg_in

/-!
## Fully Restricted Truth Lemma and Completeness

These variants weaken ALL three coherence hypotheses to their restricted forms:
- `restricted_temporally_coherent root` (forward_F/backward_P for deferralClosure only)
- `restricted_backward_until_since_coherent root` (buc for subformulaClosure only)
- `restricted_forward_until_since_coherent root` (fuc for subformulaClosure only)

The truth lemma induction only uses these coherence properties for subformulas of root,
so the restricted versions suffice.
-/

/-- Fully restricted parametric shifted truth lemma: all three coherence hypotheses
are restricted to subformulaClosure/deferralClosure of root. -/
theorem fully_restricted_parametric_shifted_truth_lemma (B : BFMCS Atom D fc)
    (root : Formula Atom)
    (_h_rtc : B.restricted_temporally_coherent root)
    (h_buc : B.restricted_backward_until_since_coherent root)
    (h_fuc : B.restricted_forward_until_since_coherent root) (φ : Formula Atom)
    (h_sub : φ ∈ subformulaClosure root)
    (fam : FMCS Atom D fc) (hfam : fam ∈ B.families) (t : D) :
    φ ∈ fam.mcs t ↔
    truth_at ParametricCanonicalTaskModel (ShiftClosedParametricCanonicalOmega B)
      (parametric_to_history fam) t φ := by
  induction φ generalizing fam t with
  | atom p =>
    simp only [truth_at, ParametricCanonicalTaskModel, parametric_to_history]
    exact ⟨fun h => ⟨True.intro, h⟩, fun ⟨_, h⟩ => h⟩
  | bot =>
    simp only [truth_at]
    exact ⟨fun h => absurd h (fun h_bot => (fam.is_mcs t).1 [(Formula.bot : Formula Atom)]
      (fun psi hpsi => by simp at hpsi; rw [hpsi]; exact h_bot)
      ⟨DerivationTree.assumption [(Formula.bot : Formula Atom)] (Formula.bot : Formula Atom) (by simp)⟩),
      fun h => h.elim⟩
  | imp ψ χ ih_ψ ih_χ =>
    have h_ψ_sub := closure_imp_left root ψ χ h_sub
    have h_χ_sub := closure_imp_right root ψ χ h_sub
    simp only [truth_at]
    have h_mcs := fam.is_mcs t
    constructor
    · intro h_imp h_ψ_true
      exact (ih_χ h_χ_sub fam hfam t).mp
        (SetMaximalConsistent.implication_property h_mcs h_imp ((ih_ψ h_ψ_sub fam hfam t).mpr h_ψ_true))
    · intro h_truth_imp
      rcases SetMaximalConsistent.negation_complete h_mcs (ψ.imp χ) with h_imp | h_neg_imp
      · exact h_imp
      · exfalso
        have h_ψ_mcs : ψ ∈ fam.mcs t :=
          SetMaximalConsistent.implication_property h_mcs
            (theorem_in_mcs_fc h_mcs (neg_imp_implies_antecedent ψ χ)) h_neg_imp
        have h_neg_χ_mcs : χ.neg ∈ fam.mcs t :=
          SetMaximalConsistent.implication_property h_mcs
            (theorem_in_mcs_fc h_mcs (neg_imp_implies_neg_consequent ψ χ)) h_neg_imp
        exact set_consistent_not_both h_mcs.1 χ
          ((ih_χ h_χ_sub fam hfam t).mpr (h_truth_imp ((ih_ψ h_ψ_sub fam hfam t).mp h_ψ_mcs)))
          h_neg_χ_mcs
  | box ψ ih =>
    have h_ψ_sub := closure_box root ψ h_sub
    constructor
    · intro h_box σ h_σ_mem
      obtain ⟨fam', hfam', delta, h_σ_eq⟩ := h_σ_mem
      have h_box_shifted := parametric_box_persistent fam ψ t (t + delta) h_box
      have h_ψ_fam' := B.modal_forward fam hfam ψ (t + delta) h_box_shifted fam' hfam'
      have h_truth_canon := (ih h_ψ_sub fam' hfam' (t + delta)).mp h_ψ_fam'
      have h_preserve := TimeShift.time_shift_preserves_truth
        ParametricCanonicalTaskModel (ShiftClosedParametricCanonicalOmega B)
        (shiftClosedParametricCanonicalOmega_is_shift_closed B) (parametric_to_history fam')
        t (t + delta) ψ
      have h_delta : (t + delta) - t = delta := add_sub_cancel_left t delta
      rw [h_σ_eq]
      rw [WorldHistory.time_shift_congr (parametric_to_history fam') ((t + delta) - t) delta h_delta] at h_preserve
      exact h_preserve.mpr h_truth_canon
    · intro h_all_σ
      exact B.modal_backward fam hfam ψ t (fun fam' hfam' =>
        (ih h_ψ_sub fam' hfam' t).mpr
          (h_all_σ (parametric_to_history fam') (parametricCanonicalOmega_subset_shiftClosed B ⟨fam', hfam', rfl⟩)))
  | untl phi psi ih_phi ih_psi =>
    have h_phi_sub := closure_untl_left root phi psi h_sub
    have h_psi_sub := closure_untl_right root phi psi h_sub
    simp only [truth_at]
    obtain ⟨h_fwd_U, _⟩ := h_fuc fam hfam
    obtain ⟨h_bwd_U, _⟩ := h_buc fam hfam
    constructor
    · intro h_U
      obtain ⟨s, h_ts, h_phi_s, h_psi_guard⟩ := h_fwd_U t phi psi h_sub h_U
      exact ⟨s, h_ts, (ih_phi h_phi_sub fam hfam s).mp h_phi_s,
        fun r h_tr h_rs => (ih_psi h_psi_sub fam hfam r).mp (h_psi_guard r h_tr h_rs)⟩
    · intro ⟨s, h_ts, h_truth_phi_s, h_truth_psi_guard⟩
      exact h_bwd_U t phi psi h_sub ⟨s, h_ts,
        (ih_phi h_phi_sub fam hfam s).mpr h_truth_phi_s,
        fun r h_tr h_rs => (ih_psi h_psi_sub fam hfam r).mpr (h_truth_psi_guard r h_tr h_rs)⟩
  | snce phi psi ih_phi ih_psi =>
    have h_phi_sub := closure_snce_left root phi psi h_sub
    have h_psi_sub := closure_snce_right root phi psi h_sub
    simp only [truth_at]
    obtain ⟨_, h_fwd_S⟩ := h_fuc fam hfam
    obtain ⟨_, h_bwd_S⟩ := h_buc fam hfam
    constructor
    · intro h_S
      obtain ⟨s, h_st, h_phi_s, h_psi_guard⟩ := h_fwd_S t phi psi h_sub h_S
      exact ⟨s, h_st, (ih_phi h_phi_sub fam hfam s).mp h_phi_s,
        fun r h_sr h_rt => (ih_psi h_psi_sub fam hfam r).mp (h_psi_guard r h_sr h_rt)⟩
    · intro ⟨s, h_st, h_truth_phi_s, h_truth_psi_guard⟩
      exact h_bwd_S t phi psi h_sub ⟨s, h_st,
        (ih_phi h_phi_sub fam hfam s).mpr h_truth_phi_s,
        fun r h_sr h_rt => (ih_psi h_psi_sub fam hfam r).mpr (h_truth_psi_guard r h_sr h_rt)⟩

/-- Fully restricted completeness from neg membership. -/
theorem fully_restricted_parametric_completeness_from_neg_membership
    (B : BFMCS Atom D fc) (root : Formula Atom)
    (h_rtc : B.restricted_temporally_coherent root)
    (h_buc : B.restricted_backward_until_since_coherent root)
    (h_fuc : B.restricted_forward_until_since_coherent root)
    (φ : Formula Atom) (h_sub : φ ∈ subformulaClosure root)
    (fam : FMCS Atom D fc) (hfam : fam ∈ B.families)
    (t : D) (h_neg_in : φ.neg ∈ fam.mcs t) :
    ¬truth_at ParametricCanonicalTaskModel (ShiftClosedParametricCanonicalOmega B)
      (parametric_to_history fam) t φ := by
  intro h_phi_true
  exact set_consistent_not_both (fam.is_mcs t).1 φ
    ((fully_restricted_parametric_shifted_truth_lemma B root h_rtc h_buc h_fuc φ h_sub fam hfam t).mpr h_phi_true)
    h_neg_in

end Cslib.Logic.Bimodal.Metalogic.Algebraic.RestrictedParametricTruthLemma
