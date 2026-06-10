/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import Cslib.Logics.Bimodal.Metalogic.Algebraic.ParametricHistory
import Cslib.Logics.Bimodal.Metalogic.Bundle.TemporalCoherence
import Cslib.Logics.Bimodal.Semantics.TaskModel
import Cslib.Logics.Bimodal.Theorems.Propositional.Core

/-!
# D-Parametric Truth Lemma

Proves the truth lemma for the D-parametric canonical model construction.

## References

* Ported from BimodalLogic/Theories/Bimodal/Metalogic/Algebraic/ParametricTruthLemma.lean
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Cslib.Logic.Bimodal.Metalogic.Algebraic.ParametricTruthLemma

open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Metalogic.Core
open Cslib.Logic.Bimodal.Metalogic.Bundle
open Cslib.Logic.Bimodal.Metalogic.Algebraic.ParametricCanonical
open Cslib.Logic.Bimodal.Metalogic.Algebraic.ParametricHistory

variable {Atom : Type} {fc : FrameClass} {D : Type*} [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]

private noncomputable def theorem_in_mcs_fc {M : Set (Formula Atom)} {phi : Formula Atom}
    (h_mcs : SetMaximalConsistent fc M)
    (h_deriv : DerivationTree fc [] phi) : phi ∈ M :=
  SetMaximalConsistent.closed_under_derivation h_mcs [] (fun _ h => by simp at h) h_deriv

/-- The D-parametric canonical task model: valuation is MCS membership. -/
def ParametricCanonicalTaskModel : TaskModel Atom (ParametricCanonicalTaskFrame (Atom := Atom) (fc := fc) (D := D)) where
  valuation := fun M p => Formula.atom p ∈ M.val

/-- Classical tautology: neg(psi -> chi) -> psi. -/
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

/-- Classical tautology: neg(psi -> chi) -> neg(chi) -/
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

/-- Past analog of TF axiom: Box phi -> H(Box phi). -/
private noncomputable def past_tf_deriv (φ : Formula Atom) :
    DerivationTree fc [] ((Formula.box φ).imp (Formula.box φ).all_past) := by
  have h_tf_swap : DerivationTree fc [] _ := Theorems.Combinators.temp_future_derived (Formula.swap_temporal φ)
  have h_dual := DerivationTree.temporal_duality _ h_tf_swap
  have h_eq : Formula.swap_temporal ((Formula.box (Formula.swap_temporal φ)).imp
      (Formula.box (Formula.swap_temporal φ)).all_future) =
    (Formula.box φ).imp (Formula.box φ).all_past := by
    simp [Formula.swap_temporal, Formula.swap_temporal_involution]
  rw [h_eq] at h_dual
  exact h_dual

omit [AddCommGroup D] [IsOrderedAddMonoid D] in
/-- Box phi at time t implies Box phi at all times s. -/
theorem parametric_box_persistent
    (fam : FMCS Atom D fc)
    (φ : Formula Atom) (t s : D)
    (h_box : Formula.box φ ∈ fam.mcs t) :
    Formula.box φ ∈ fam.mcs s := by
  have h_tf : (Formula.box φ).imp (Formula.box φ).all_future ∈ fam.mcs t :=
    theorem_in_mcs_fc (fam.is_mcs t) (Theorems.Combinators.temp_future_derived φ)
  have h_G_box : (Formula.box φ).all_future ∈ fam.mcs t :=
    SetMaximalConsistent.implication_property (fam.is_mcs t) h_tf h_box
  have h_past_tf : (Formula.box φ).imp (Formula.box φ).all_past ∈ fam.mcs t :=
    theorem_in_mcs_fc (fam.is_mcs t) (past_tf_deriv φ)
  have h_H_box : (Formula.box φ).all_past ∈ fam.mcs t :=
    SetMaximalConsistent.implication_property (fam.is_mcs t) h_past_tf h_box
  rcases lt_trichotomy t s with h_lt | h_eq | h_gt
  · exact fam.forward_G t s (Formula.box φ) h_lt h_G_box
  · exact h_eq ▸ h_box
  · exact fam.backward_H t s (Formula.box φ) h_gt h_H_box

/-- The parametric canonical truth lemma. -/
theorem parametric_canonical_truth_lemma
    (B : BFMCS Atom D fc) (_h_tc : B.temporally_coherent)
    (h_buc : B.backward_until_since_coherent)
    (h_fuc : B.forward_until_since_coherent)
    (fam : FMCS Atom D fc) (hfam : fam ∈ B.families)
    (t : D) (phi : Formula Atom) :
    phi ∈ fam.mcs t ↔
      truth_at ParametricCanonicalTaskModel (ParametricCanonicalOmega B)
        (parametric_to_history fam) t phi := by
  induction phi generalizing fam t with
  | atom p =>
    simp only [truth_at, ParametricCanonicalTaskModel, parametric_to_history]
    constructor
    · intro h_atom; exact ⟨True.intro, h_atom⟩
    · intro ⟨_, h_val⟩; exact h_val
  | bot =>
    simp only [truth_at]
    constructor
    · intro h_bot
      have h_cons := (fam.is_mcs t).1
      exact h_cons [(Formula.bot : Formula Atom)]
        (fun psi hpsi => by simp at hpsi; rw [hpsi]; exact h_bot)
        ⟨DerivationTree.assumption [(Formula.bot : Formula Atom)] (Formula.bot : Formula Atom) (by simp)⟩
    · intro h_false; exact False.elim h_false
  | imp psi chi ih_psi ih_chi =>
    simp only [truth_at]
    have h_mcs := fam.is_mcs t
    constructor
    · intro h_imp h_psi_true
      have h_psi_mcs : psi ∈ fam.mcs t := (ih_psi fam hfam t).mpr h_psi_true
      have h_chi_mcs : chi ∈ fam.mcs t := SetMaximalConsistent.implication_property h_mcs h_imp h_psi_mcs
      exact (ih_chi fam hfam t).mp h_chi_mcs
    · intro h_truth_imp
      rcases SetMaximalConsistent.negation_complete h_mcs (psi.imp chi) with h_imp | h_neg_imp
      · exact h_imp
      · exfalso
        have h_psi_mcs : psi ∈ fam.mcs t :=
          SetMaximalConsistent.implication_property h_mcs
            (theorem_in_mcs_fc h_mcs (neg_imp_implies_antecedent psi chi)) h_neg_imp
        have h_neg_chi_mcs : chi.neg ∈ fam.mcs t :=
          SetMaximalConsistent.implication_property h_mcs
            (theorem_in_mcs_fc h_mcs (neg_imp_implies_neg_consequent psi chi)) h_neg_imp
        have h_psi_true := (ih_psi fam hfam t).mp h_psi_mcs
        have h_chi_true := h_truth_imp h_psi_true
        have h_chi_mcs : chi ∈ fam.mcs t := (ih_chi fam hfam t).mpr h_chi_true
        exact set_consistent_not_both (fam.is_mcs t).1 chi h_chi_mcs h_neg_chi_mcs
  | box psi ih =>
    simp only [truth_at]
    constructor
    · intro h_box sigma h_sigma_mem
      obtain ⟨fam', hfam', h_eq⟩ := h_sigma_mem
      subst h_eq
      have h_psi_mcs : psi ∈ fam'.mcs t := B.modal_forward fam hfam psi t h_box fam' hfam'
      exact (ih fam' hfam' t).mp h_psi_mcs
    · intro h_all
      have h_psi_all_mcs : ∀ fam' ∈ B.families, psi ∈ fam'.mcs t := by
        intro fam' hfam'
        have h_in_omega : parametric_to_history fam' ∈ ParametricCanonicalOmega B := ⟨fam', hfam', rfl⟩
        exact (ih fam' hfam' t).mpr (h_all (parametric_to_history fam') h_in_omega)
      exact B.modal_backward fam hfam psi t h_psi_all_mcs
  | untl phi psi ih_phi ih_psi =>
    simp only [truth_at]
    obtain ⟨h_fwd_U, _⟩ := h_fuc fam hfam
    obtain ⟨h_bwd_U, _⟩ := h_buc fam hfam
    constructor
    · intro h_U
      obtain ⟨s, h_ts, h_event_s, h_guard⟩ := h_fwd_U t phi psi h_U
      exact ⟨s, h_ts,
        (ih_phi fam hfam s).mp h_event_s,
        fun r h_tr h_rs => (ih_psi fam hfam r).mp (h_guard r h_tr h_rs)⟩
    · intro ⟨s, h_ts, h_truth_event_s, h_truth_guard⟩
      exact h_bwd_U t phi psi ⟨s, h_ts,
        (ih_phi fam hfam s).mpr h_truth_event_s,
        fun r h_tr h_rs => (ih_psi fam hfam r).mpr (h_truth_guard r h_tr h_rs)⟩
  | snce phi psi ih_phi ih_psi =>
    simp only [truth_at]
    obtain ⟨_, h_fwd_S⟩ := h_fuc fam hfam
    obtain ⟨_, h_bwd_S⟩ := h_buc fam hfam
    constructor
    · intro h_S
      obtain ⟨s, h_st, h_event_s, h_guard⟩ := h_fwd_S t phi psi h_S
      exact ⟨s, h_st,
        (ih_phi fam hfam s).mp h_event_s,
        fun r h_sr h_rt => (ih_psi fam hfam r).mp (h_guard r h_sr h_rt)⟩
    · intro ⟨s, h_st, h_truth_event_s, h_truth_guard⟩
      exact h_bwd_S t phi psi ⟨s, h_st,
        (ih_phi fam hfam s).mpr h_truth_event_s,
        fun r h_sr h_rt => (ih_psi fam hfam r).mpr (h_truth_guard r h_sr h_rt)⟩

/-- Shifted truth lemma for ShiftClosedParametricCanonicalOmega. -/
theorem parametric_shifted_truth_lemma (B : BFMCS Atom D fc)
    (_h_tc : B.temporally_coherent)
    (h_buc : B.backward_until_since_coherent)
    (h_fuc : B.forward_until_since_coherent) (φ : Formula Atom)
    (fam : FMCS Atom D fc) (hfam : fam ∈ B.families) (t : D) :
    φ ∈ fam.mcs t ↔
    truth_at ParametricCanonicalTaskModel (ShiftClosedParametricCanonicalOmega B)
      (parametric_to_history fam) t φ := by
  induction φ generalizing fam t with
  | atom p =>
    simp only [truth_at, ParametricCanonicalTaskModel, parametric_to_history]
    constructor
    · intro h_mem; exact ⟨True.intro, h_mem⟩
    · intro ⟨_, h_val⟩; exact h_val
  | bot =>
    simp only [truth_at]
    constructor
    · intro h_mem; exfalso
      exact (fam.is_mcs t).1 [(Formula.bot : Formula Atom)]
        (fun psi hpsi => by simp at hpsi; rw [hpsi]; exact h_mem)
        ⟨DerivationTree.assumption [(Formula.bot : Formula Atom)] (Formula.bot : Formula Atom) (by simp)⟩
    · intro h; exact h.elim
  | imp ψ χ ih_ψ ih_χ =>
    simp only [truth_at]
    have h_mcs := fam.is_mcs t
    constructor
    · intro h_imp h_ψ_true
      have h_ψ_mem := (ih_ψ fam hfam t).mpr h_ψ_true
      exact (ih_χ fam hfam t).mp (SetMaximalConsistent.implication_property h_mcs h_imp h_ψ_mem)
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
        have h_ψ_true := (ih_ψ fam hfam t).mp h_ψ_mcs
        have h_χ_true := h_truth_imp h_ψ_true
        have h_χ_mcs : χ ∈ fam.mcs t := (ih_χ fam hfam t).mpr h_χ_true
        exact set_consistent_not_both (fam.is_mcs t).1 χ h_χ_mcs h_neg_χ_mcs
  | box ψ ih =>
    constructor
    · intro h_box σ h_σ_mem
      obtain ⟨fam', hfam', delta, h_σ_eq⟩ := h_σ_mem
      have h_box_shifted : Formula.box ψ ∈ fam.mcs (t + delta) :=
        parametric_box_persistent fam ψ t (t + delta) h_box
      have h_ψ_fam' : ψ ∈ fam'.mcs (t + delta) :=
        B.modal_forward fam hfam ψ (t + delta) h_box_shifted fam' hfam'
      have h_truth_canon := (ih fam' hfam' (t + delta)).mp h_ψ_fam'
      have h_preserve := TimeShift.time_shift_preserves_truth
        ParametricCanonicalTaskModel (ShiftClosedParametricCanonicalOmega B)
        (shiftClosedParametricCanonicalOmega_is_shift_closed B) (parametric_to_history fam')
        t (t + delta) ψ
      have h_delta : (t + delta) - t = delta := add_sub_cancel_left t delta
      rw [h_σ_eq]
      rw [WorldHistory.time_shift_congr (parametric_to_history fam') ((t + delta) - t) delta h_delta] at h_preserve
      exact h_preserve.mpr h_truth_canon
    · intro h_all_σ
      have h_all_fam : ∀ fam' ∈ B.families, ψ ∈ fam'.mcs t := by
        intro fam' hfam'
        have h_mem := parametricCanonicalOmega_subset_shiftClosed B ⟨fam', hfam', rfl⟩
        exact (ih fam' hfam' t).mpr (h_all_σ (parametric_to_history fam') h_mem)
      exact B.modal_backward fam hfam ψ t h_all_fam
  | untl phi psi ih_phi ih_psi =>
    simp only [truth_at]
    obtain ⟨h_fwd_U, _⟩ := h_fuc fam hfam
    obtain ⟨h_bwd_U, _⟩ := h_buc fam hfam
    constructor
    · intro h_U
      obtain ⟨s, h_ts, h_event_s, h_guard⟩ := h_fwd_U t phi psi h_U
      exact ⟨s, h_ts,
        (ih_phi fam hfam s).mp h_event_s,
        fun r h_tr h_rs => (ih_psi fam hfam r).mp (h_guard r h_tr h_rs)⟩
    · intro ⟨s, h_ts, h_truth_event_s, h_truth_guard⟩
      exact h_bwd_U t phi psi ⟨s, h_ts,
        (ih_phi fam hfam s).mpr h_truth_event_s,
        fun r h_tr h_rs => (ih_psi fam hfam r).mpr (h_truth_guard r h_tr h_rs)⟩
  | snce phi psi ih_phi ih_psi =>
    simp only [truth_at]
    obtain ⟨_, h_fwd_S⟩ := h_fuc fam hfam
    obtain ⟨_, h_bwd_S⟩ := h_buc fam hfam
    constructor
    · intro h_S
      obtain ⟨s, h_st, h_event_s, h_guard⟩ := h_fwd_S t phi psi h_S
      exact ⟨s, h_st,
        (ih_phi fam hfam s).mp h_event_s,
        fun r h_sr h_rt => (ih_psi fam hfam r).mp (h_guard r h_sr h_rt)⟩
    · intro ⟨s, h_st, h_truth_event_s, h_truth_guard⟩
      exact h_bwd_S t phi psi ⟨s, h_st,
        (ih_phi fam hfam s).mpr h_truth_event_s,
        fun r h_sr h_rt => (ih_psi fam hfam r).mpr (h_truth_guard r h_sr h_rt)⟩

end Cslib.Logic.Bimodal.Metalogic.Algebraic.ParametricTruthLemma
