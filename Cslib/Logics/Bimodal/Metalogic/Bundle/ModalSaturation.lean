/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.Bundle.BFMCS
public import Cslib.Logics.Bimodal.Metalogic.Core.MaximalConsistent
public import Cslib.Logics.Bimodal.Metalogic.Core.MCSProperties
public import Cslib.Logics.Bimodal.Syntax.Formula
public import Cslib.Logics.Bimodal.Theorems.Propositional.Connectives

/-!
# Modal Saturation for BFMCS

A modally saturated BFMCS satisfies the property that every Diamond formula that
is true in some family has a witness family where the inner formula is true.

## References

* Ported from BimodalLogic/Theories/Bimodal/Metalogic/Bundle/ModalSaturation.lean
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.Bundle

open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Metalogic.Core

variable {Atom : Type*} {D : Type*} [Preorder D]

/-! ## Saturation Predicate -/

/--
A BFMCS is modally saturated if every Diamond formula that is true in some
family's MCS has a witness family in the bundle.
-/
def is_modally_saturated (B : BFMCS Atom D) : Prop :=
  ∀ fam ∈ B.families, ∀ t : D, ∀ psi : Formula Atom,
    psi.diamond ∈ fam.mcs t → ∃ fam' ∈ B.families, psi ∈ fam'.mcs t

/-! ## Diamond Formula Properties -/

lemma diamond_eq (phi : Formula Atom) :
    phi.diamond = Formula.neg (Formula.box (Formula.neg phi)) := rfl

lemma diamond_excludes_box_neg {Omega : Set (Formula Atom)} (h_mcs : SetMaximalConsistent (FrameClass.Base : FrameClass) Omega)
    (psi : Formula Atom) (h_diamond : psi.diamond ∈ Omega) :
    Formula.box (Formula.neg psi) ∉ Omega := by
  intro h_box
  have h_eq : psi.diamond = Formula.neg (Formula.box (Formula.neg psi)) := rfl
  rw [h_eq] at h_diamond
  exact set_consistent_not_both h_mcs.1 (Formula.box (Formula.neg psi)) h_box h_diamond

/-! ## MCS Existence for Consistent Formulas -/

lemma diamond_implies_psi_consistent {Omega : Set (Formula Atom)} (h_mcs : SetMaximalConsistent (FrameClass.Base : FrameClass) Omega)
    (psi : Formula Atom) (h_diamond : psi.diamond ∈ Omega) :
    SetConsistent FrameClass.Base ({psi} : Set (Formula Atom)) := by
  intro L hL ⟨d⟩
  by_cases h_psi_in_L : psi ∈ L
  · have h_weak : ∀ x ∈ L, x ∈ [psi] := by
      intro x hx
      have := hL x hx
      simp only [Set.mem_singleton_iff] at this
      simp [this]
    have d_psi : DerivationTree FrameClass.Base [psi] (Formula.bot : Formula Atom) :=
      DerivationTree.weakening L [psi] _ d h_weak
    have d_neg : DerivationTree FrameClass.Base [] (Formula.neg psi) :=
      deduction_theorem [] psi Formula.bot d_psi
    have d_box : DerivationTree FrameClass.Base [] (Formula.box (Formula.neg psi)) :=
      DerivationTree.necessitation (Formula.neg psi) d_neg
    have h_box_in : Formula.box (Formula.neg psi) ∈ Omega := theorem_in_mcs h_mcs d_box
    have h_eq : psi.diamond = Formula.neg (Formula.box (Formula.neg psi)) := rfl
    rw [h_eq] at h_diamond
    exact set_consistent_not_both h_mcs.1 _ h_box_in h_diamond
  · have h_L_empty : L = [] := by
      cases L with
      | nil => rfl
      | cons x xs =>
        exfalso
        have hx := hL x List.mem_cons_self
        simp only [Set.mem_singleton_iff] at hx
        rw [hx] at h_psi_in_L
        exact h_psi_in_L List.mem_cons_self
    rw [h_L_empty] at d
    have h_bot_in : (Formula.bot : Formula Atom) ∈ Omega := theorem_in_mcs h_mcs d
    have h_deriv : DerivationTree FrameClass.Base [(Formula.bot : Formula Atom)] (Formula.bot : Formula Atom) :=
      DerivationTree.assumption [(Formula.bot : Formula Atom)] (Formula.bot : Formula Atom) (by simp)
    have h_sub : ∀ x ∈ [(Formula.bot : Formula Atom)], x ∈ Omega := by simp [h_bot_in]
    exact h_mcs.1 [(Formula.bot : Formula Atom)] h_sub ⟨h_deriv⟩

/-! ## Helper Lemmas for Modal Backward Proof -/

noncomputable def dne_theorem (phi : Formula Atom) : DerivationTree FrameClass.Base [] (Formula.neg (Formula.neg phi) |>.imp phi) :=
  Theorems.Propositional.double_negation phi

noncomputable def box_dne_theorem (phi : Formula Atom) :
    DerivationTree FrameClass.Base [] ((Formula.box (Formula.neg (Formula.neg phi))).imp (Formula.box phi)) := by
  have h_dne : DerivationTree FrameClass.Base [] ((Formula.neg (Formula.neg phi)).imp phi) := dne_theorem phi
  have h_box_dne : DerivationTree FrameClass.Base [] (Formula.box ((Formula.neg (Formula.neg phi)).imp phi)) :=
    DerivationTree.necessitation _ h_dne
  have h_K : DerivationTree FrameClass.Base [] ((Formula.box ((Formula.neg (Formula.neg phi)).imp phi)).imp
               ((Formula.box (Formula.neg (Formula.neg phi))).imp (Formula.box phi))) :=
    DerivationTree.axiom [] _ (Axiom.modal_k_dist _ _) trivial
  exact DerivationTree.modus_ponens [] _ _ h_K h_box_dne

lemma SetMaximalConsistent.contrapositive_lemma {fc : FrameClass} {Omega : Set (Formula Atom)} (h_mcs : SetMaximalConsistent fc Omega)
    {A B : Formula Atom} (h_impl : DerivationTree fc [] (A.imp B)) (h_negB : B.neg ∈ Omega) : A.neg ∈ Omega := by
  have h1 : DerivationTree fc [A, B.neg] A :=
    DerivationTree.assumption _ A (by simp)
  have h2 : DerivationTree fc [A, B.neg] (A.imp B) :=
    DerivationTree.weakening [] _ _ h_impl (by intro x hx; exact False.elim (List.not_mem_nil hx))
  have h3 : DerivationTree fc [A, B.neg] B :=
    DerivationTree.modus_ponens _ A B h2 h1
  have h4 : DerivationTree fc [A, B.neg] B.neg :=
    DerivationTree.assumption _ B.neg (by simp)
  have h5 : DerivationTree fc [A, B.neg] (Formula.bot : Formula Atom) :=
    DerivationTree.modus_ponens _ B Formula.bot h4 h3
  have h6 : DerivationTree fc [B.neg] A.neg :=
    deduction_theorem [B.neg] A Formula.bot h5
  have h7 : DerivationTree fc [] (B.neg.imp A.neg) :=
    deduction_theorem [] B.neg A.neg h6
  have h_thm_in : B.neg.imp A.neg ∈ Omega := theorem_in_mcs_fc h_mcs h7
  exact SetMaximalConsistent.implication_property h_mcs h_thm_in h_negB

/-! ## Modal Backward from Saturation -/

theorem saturated_modal_backward (B : BFMCS Atom D) (h_sat : is_modally_saturated B)
    (fam : FMCS Atom D) (hfam : fam ∈ B.families) (phi : Formula Atom) (t : D)
    (h_all : ∀ fam' ∈ B.families, phi ∈ fam'.mcs t) :
    Formula.box phi ∈ fam.mcs t := by
  by_contra h_not_box
  have h_mcs := fam.is_mcs t
  have h_neg_box : Formula.neg (Formula.box phi) ∈ fam.mcs t := by
    rcases SetMaximalConsistent.negation_complete h_mcs (Formula.box phi) with h_box | h_neg
    · exact absurd h_box h_not_box
    · exact h_neg
  have h_box_dne := box_dne_theorem phi
  have h_diamond_neg : Formula.neg (Formula.box (Formula.neg (Formula.neg phi))) ∈ fam.mcs t :=
    SetMaximalConsistent.contrapositive_lemma h_mcs h_box_dne h_neg_box
  have h_eq_diamond : (Formula.neg phi).diamond =
                      Formula.neg (Formula.box (Formula.neg (Formula.neg phi))) := rfl
  have h_diamond_in : (Formula.neg phi).diamond ∈ fam.mcs t := by
    rw [h_eq_diamond]
    exact h_diamond_neg
  have ⟨fam', hfam', h_neg_phi_in⟩ := h_sat fam hfam t (Formula.neg phi) h_diamond_in
  have h_phi_in := h_all fam' hfam'
  exact set_consistent_not_both (fam'.is_mcs t).1 phi h_phi_in h_neg_phi_in

/-! ## Saturated BFMCS Structure -/

structure SaturatedBFMCS (Atom : Type*) (D : Type*) [Preorder D] where
  bfmcs : BFMCS Atom D
  saturated : is_modally_saturated bfmcs

theorem SaturatedBFMCS.modal_backward (S_bfmcs : SaturatedBFMCS Atom D)
    (fam : FMCS Atom D) (hfam : fam ∈ S_bfmcs.bfmcs.families) (phi : Formula Atom) (t : D)
    (h_all : ∀ fam' ∈ S_bfmcs.bfmcs.families, phi ∈ fam'.mcs t) :
    Formula.box phi ∈ fam.mcs t :=
  saturated_modal_backward S_bfmcs.bfmcs S_bfmcs.saturated fam hfam phi t h_all

/-! ## Axiom 5 (Negative Introspection) -/

noncomputable def modal_5_collapse_theorem (phi : Formula Atom) :
    DerivationTree FrameClass.Base [] (Formula.box phi |>.diamond.imp (Formula.box phi)) :=
  DerivationTree.axiom [] _ (Axiom.modal_5_collapse phi) trivial

noncomputable def axiom_5_negative_introspection (phi : Formula Atom) :
    DerivationTree FrameClass.Base [] ((Formula.box phi).neg.imp (Formula.box (Formula.box phi).neg)) := by
  have h_collapse : DerivationTree FrameClass.Base [] ((Formula.box phi).diamond.imp (Formula.box phi)) :=
    modal_5_collapse_theorem phi
  have h_contra : DerivationTree FrameClass.Base [] ((Formula.box phi).neg.imp (Formula.box phi).diamond.neg) :=
    Theorems.Propositional.contraposition h_collapse
  have h_dne : DerivationTree FrameClass.Base [] (((Formula.box phi).neg.box.neg.neg).imp ((Formula.box phi).neg.box)) :=
    Theorems.Propositional.double_negation ((Formula.box phi).neg.box)
  have h_contra_expanded :
    (Formula.box phi).diamond.neg = (Formula.box phi).neg.box.neg.neg := rfl
  rw [h_contra_expanded] at h_contra
  exact Theorems.Combinators.imp_trans h_contra h_dne

noncomputable def neg_box_to_box_neg_box (phi : Formula Atom) :
    DerivationTree FrameClass.Base [] ((Formula.box phi).neg.imp (Formula.box (Formula.box phi).neg)) :=
  axiom_5_negative_introspection phi

lemma SetMaximalConsistent.neg_box_implies_box_neg_box {fc : FrameClass} {Omega : Set (Formula Atom)} (h_mcs : SetMaximalConsistent fc Omega)
    (phi : Formula Atom) (h_neg_box : (Formula.box phi).neg ∈ Omega) :
    Formula.box (Formula.box phi).neg ∈ Omega := by
  have h_ax5 : DerivationTree fc [] ((Formula.box phi).neg.imp (Formula.box (Formula.box phi).neg)) :=
    (neg_box_to_box_neg_box phi).lift (FrameClass.base_le fc)
  have h_ax5_in := theorem_in_mcs_fc h_mcs h_ax5
  exact SetMaximalConsistent.implication_property h_mcs h_ax5_in h_neg_box

end Cslib.Logic.Bimodal.Metalogic.Bundle
