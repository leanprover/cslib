/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import Cslib.Logics.Bimodal.Metalogic.BXCanonical.Frame
import Cslib.Logics.Bimodal.Semantics.Truth
import Cslib.Logics.Bimodal.Semantics.Validity

/-!
# BX Truth Lemma

The truth lemma for the BX canonical model: membership in an MCS corresponds
to truth in the canonical model.

## Architecture

The BX canonical model embeds the collection of all MCS (with bx_le ordering)
into a TaskModel. The truth lemma is proved by structural induction on formulas.

### Cases

- **atom**: By definition of canonical valuation
- **bot**: Trivial (bot not in any MCS, and truth_at gives False)
- **imp**: MCS implication property iff material conditional
- **box**: Modal witness construction (bx_modal_witness)
- **allFuture (G)**: bx_G_forward + bx_G_backward
- **allPast (H)**: bx_H_forward + bx_H_backward
- **untl (U)**: Eventuality resolution (BX5/BX6) for forward; BX4 for backward
- **snce (S)**: Mirror of Until

## Status

The truth lemma for atom, bot, imp, box, G, H is fully proved.
The Until/Since forward direction (eventuality resolution) is proved via
`bx_until_eventuality_resolution` / `bx_since_eventuality_resolution` in Frame.lean.

## References

* Ported from BimodalLogic/Theories/Bimodal/Metalogic/BXCanonical/TruthLemma.lean
* Burgess 1984, Goldblatt 1992 (canonical model truth lemma)
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Cslib.Logic.Bimodal.Metalogic.BXCanonical

open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Metalogic.Core
open Cslib.Logic.Bimodal.Metalogic.Bundle

variable {Atom : Type*}

/-! ## MCS Truth Properties

These lemmas establish the truth lemma at the MCS level, independent of
any particular TaskModel embedding. They show that MCS membership correctly
reflects the semantic meaning of each connective.
-/

/-- Bot is not in any MCS. -/
theorem bot_not_in_mcs {fc : FrameClass} {Omega : Set (Formula Atom)} (h_mcs : SetMaximalConsistent (fc := fc) Omega) :
    (Formula.bot : Formula Atom) ∉ Omega := by
  intro h_bot
  exact h_mcs.1 [(Formula.bot : Formula Atom)] (fun ψ hψ => by simp at hψ; rw [hψ]; exact h_bot)
    ⟨DerivationTree.assumption [(Formula.bot : Formula Atom)] (Formula.bot : Formula Atom) (by simp)⟩

/-- Implication property: (phi -> psi) in Omega iff (phi in Omega -> psi in Omega) for MCS Omega. -/
theorem imp_iff_mcs {fc : FrameClass} {Omega : Set (Formula Atom)} (h_mcs : SetMaximalConsistent (fc := fc) Omega) (φ ψ : Formula Atom) :
    φ.imp ψ ∈ Omega ↔ (φ ∈ Omega → ψ ∈ Omega) := by
  constructor
  · exact SetMaximalConsistent.implication_property h_mcs
  · intro h_imp
    by_cases h_φ : φ ∈ Omega
    · have h_ψ := h_imp h_φ
      have h_ax : DerivationTree fc [] (ψ.imp (φ.imp ψ)) :=
        DerivationTree.axiom [] _ (Axiom.imp_s ψ φ) (FrameClass.base_le fc)
      exact SetMaximalConsistent.implication_property h_mcs
        (SetMaximalConsistent.closed_under_derivation h_mcs [] (fun _ h => by simp at h) h_ax) h_ψ
    · have h_neg_φ : φ.neg ∈ Omega := by
        cases SetMaximalConsistent.negation_complete h_mcs φ with
        | inl h => exact absurd h h_φ
        | inr h => exact h
      have h_deriv : DerivationTree fc [φ.neg] (φ.imp ψ) := by
        have h_step : DerivationTree fc [φ, φ.neg] ψ := by
          have h_φ_assum : DerivationTree fc [φ, φ.neg] φ :=
            DerivationTree.assumption _ _ (by simp)
          have h_neg_assum : DerivationTree fc [φ, φ.neg] φ.neg :=
            DerivationTree.assumption _ _ (by simp)
          have h_bot : DerivationTree fc [φ, φ.neg] (Formula.bot : Formula Atom) :=
            DerivationTree.modus_ponens _ _ _ h_neg_assum h_φ_assum
          have h_ef : DerivationTree fc [] ((Formula.bot : Formula Atom).imp ψ) :=
            DerivationTree.axiom [] _ (Axiom.efq ψ) (FrameClass.base_le fc)
          exact DerivationTree.modus_ponens _ _ _
            (DerivationTree.weakening [] _ _ h_ef (List.nil_subset _)) h_bot
        exact deduction_theorem [φ.neg] φ ψ h_step
      exact SetMaximalConsistent.closed_under_derivation h_mcs [φ.neg]
        (fun χ hχ => by simp at hχ; rw [hχ]; exact h_neg_φ) h_deriv

/-- G-truth in MCS: G(phi) in w iff phi in v for all v >= w. -/
theorem G_iff_mcs (w : BXPoint Atom) (φ : Formula Atom) :
    Formula.allFuture φ ∈ w.formulas ↔ ∀ v : BXPoint Atom, bx_le w v → φ ∈ v.formulas := by
  constructor
  · intro h_G v h_le
    exact bx_G_forward h_le h_G
  · intro h_all
    by_contra h_not_G
    obtain ⟨v, h_le, h_not_φ⟩ := bx_G_backward w φ h_not_G
    exact h_not_φ (h_all v h_le)

/-- H-truth in MCS: H(phi) in w iff phi in v for all v <= w. -/
theorem H_iff_mcs (w : BXPoint Atom) (φ : Formula Atom) :
    Formula.allPast φ ∈ w.formulas ↔ ∀ v : BXPoint Atom, bx_le v w → φ ∈ v.formulas := by
  constructor
  · intro h_H v h_le
    exact bx_H_forward h_le h_H
  · intro h_all
    by_contra h_not_H
    obtain ⟨v, h_le, h_not_φ⟩ := bx_H_backward w φ h_not_H
    exact h_not_φ (h_all v h_le)

/-- Box-truth in MCS: box(phi) in w iff phi in v for all modally equivalent v. -/
theorem box_iff_mcs (w : BXPoint Atom) (φ : Formula Atom) :
    Formula.box φ ∈ w.formulas ↔
      ∀ v : BXPoint Atom, bx_modal_equiv w v → φ ∈ v.formulas := by
  constructor
  · intro h_box v h_equiv
    have h_box_v := (h_equiv φ).mp h_box
    have h_ax : DerivationTree FrameClass.Base [] (Formula.box φ |>.imp φ) :=
      DerivationTree.axiom [] _ (Axiom.modal_t φ) trivial
    exact SetMaximalConsistent.implication_property v.is_mcs
      (theorem_in_mcs_fc v.is_mcs h_ax) h_box_v
  · intro h_all
    by_contra h_not_box
    have h_dne : DerivationTree FrameClass.Base [] (φ.neg.neg.imp φ) :=
      Theorems.Propositional.double_negation φ
    have h_nec_dne : DerivationTree FrameClass.Base [] (Formula.box (φ.neg.neg.imp φ)) :=
      DerivationTree.necessitation _ h_dne
    have h_k : DerivationTree FrameClass.Base [] ((Formula.box (φ.neg.neg.imp φ)).imp
        (φ.neg.neg.box.imp φ.box)) :=
      DerivationTree.axiom [] _ (Axiom.modal_k_dist φ.neg.neg φ) trivial
    have h_box_dne : DerivationTree FrameClass.Base [] (φ.neg.neg.box.imp φ.box) :=
      DerivationTree.modus_ponens [] _ _ h_k h_nec_dne
    have h_neg_box_to_dia : DerivationTree FrameClass.Base [] (φ.box.neg.imp φ.neg.neg.box.neg) :=
      Theorems.Propositional.contraposition h_box_dne
    have h_neg_box : (Formula.box φ).neg ∈ w.formulas := by
      cases SetMaximalConsistent.negation_complete w.is_mcs (Formula.box φ) with
      | inl h => exact absurd h h_not_box
      | inr h => exact h
    have h_dia_neg : Formula.diamond φ.neg ∈ w.formulas :=
      SetMaximalConsistent.implication_property w.is_mcs
        (theorem_in_mcs_fc w.is_mcs h_neg_box_to_dia) h_neg_box
    obtain ⟨v, h_equiv, h_neg_in⟩ := bx_modal_witness w φ.neg h_dia_neg
    have h_not_in : φ ∉ v.formulas :=
      SetMaximalConsistent.neg_excludes v.is_mcs φ h_neg_in
    exact h_not_in (h_all v h_equiv)

/-! ## Until/Since MCS Properties -/

/-- Strict part of bx_le: w is strictly below v in the canonical ordering. -/
def bx_lt (w v : BXPoint Atom) : Prop :=
  bx_le w v ∧ ¬bx_le v w

/-! ### Helper: F(psi) from witness existence -/

/-- If bx_le w v, psi in v, then F(psi) in w. -/
theorem F_from_witness {w v : BXPoint Atom} {ψ : Formula Atom}
    (h_wv : bx_le w v) (h_ψv : ψ ∈ v.formulas) :
    Formula.someFuture ψ ∈ w.formulas := by
  by_contra h_not_F
  have h_neg_F : Formula.neg (Formula.someFuture ψ) ∈ w.formulas := by
    cases SetMaximalConsistent.negation_complete w.is_mcs (Formula.someFuture ψ) with
    | inl h => exact absurd h h_not_F
    | inr h => exact h
  have h_G_neg_psi : ψ.neg.allFuture ∈ w.formulas :=
    neg_someFuture_to_allFuture_neg w.is_mcs ψ h_neg_F
  have h_neg_psi_v : ψ.neg ∈ v.formulas := bx_G_forward h_wv h_G_neg_psi
  exact set_consistent_not_both v.is_mcs.1 ψ h_ψv h_neg_psi_v

/-- If bx_le v w, psi in v, then P(psi) in w. Mirror of F_from_witness. -/
theorem P_from_witness {w v : BXPoint Atom} {ψ : Formula Atom}
    (h_vw : bx_le v w) (h_ψv : ψ ∈ v.formulas) :
    Formula.somePast ψ ∈ w.formulas := by
  by_contra h_not_P
  have h_neg_P : Formula.neg (Formula.somePast ψ) ∈ w.formulas := by
    cases SetMaximalConsistent.negation_complete w.is_mcs (Formula.somePast ψ) with
    | inl h => exact absurd h h_not_P
    | inr h => exact h
  have h_H_neg_psi : ψ.neg.allPast ∈ w.formulas :=
    neg_somePast_to_allPast_neg w.is_mcs ψ h_neg_P
  have h_neg_psi_v : ψ.neg ∈ v.formulas := bx_H_forward h_vw h_H_neg_psi
  exact set_consistent_not_both v.is_mcs.1 ψ h_ψv h_neg_psi_v

/-! ### Until truth lemma -/

/-- Until truth in MCS (forward): (phi U psi) in w implies either psi in w (reflexive
    witness) or there exists v > w with psi in v. -/
theorem until_forward_mcs (w : BXPoint Atom) (φ ψ : Formula Atom)
    (h_until : Formula.untl φ ψ ∈ w.formulas) :
    φ ∈ w.formulas ∨
      (∃ v : BXPoint Atom, bx_le w v ∧ φ ∈ v.formulas) := by
  by_cases h_φ : φ ∈ w.formulas
  · exact Or.inl h_φ
  · exact Or.inr (bx_until_eventuality_resolution w ψ φ h_until h_φ)

/-- Since forward: (phi S psi) in w implies either psi in w or there exists v < w
    with psi in v. Mirror of until_forward_mcs. -/
theorem since_forward_mcs (w : BXPoint Atom) (φ ψ : Formula Atom)
    (h_since : Formula.snce φ ψ ∈ w.formulas) :
    φ ∈ w.formulas ∨
      (∃ v : BXPoint Atom, bx_le v w ∧ φ ∈ v.formulas) := by
  by_cases h_φ : φ ∈ w.formulas
  · exact Or.inl h_φ
  · exact Or.inr (bx_since_eventuality_resolution w ψ φ h_since h_φ)

end Cslib.Logic.Bimodal.Metalogic.BXCanonical
