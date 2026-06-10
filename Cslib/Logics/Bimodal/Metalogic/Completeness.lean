/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.Core
public import Cslib.Logics.Bimodal.Theorems.Perpetuity.Helpers

/-!
# MCS Completeness Properties for Bimodal Logic

This module provides modal and propositional MCS properties needed for the
completeness theorem of TM (Tense and Modality) bimodal logic.

## Main Results

Propositional MCS properties:
- `SetMaximalConsistent.disjunction_intro`: phi or psi in MCS
- `SetMaximalConsistent.disjunction_elim`: MCS disjunction elimination
- `SetMaximalConsistent.disjunction_iff`: Iff wrapper
- `SetMaximalConsistent.conjunction_intro`: phi and psi in MCS
- `SetMaximalConsistent.conjunction_elim`: MCS conjunction elimination
- `SetMaximalConsistent.conjunction_iff`: Iff wrapper

Modal MCS properties:
- `SetMaximalConsistent.box_closure`: Modal T for MCS
- `SetMaximalConsistent.box_box`: Modal 4 for MCS

Diamond-box duality:
- `SetMaximalConsistent.neg_box_implies_diamond_neg`
- `SetMaximalConsistent.diamond_neg_implies_neg_box`
- `SetMaximalConsistent.diamond_box_duality`: Iff wrapper

## References

* Modal Logic, Blackburn et al., Chapter 4 (Canonical Models)
* Ported from BimodalLogic/Theories/Bimodal/Metalogic/Completeness.lean
-/

set_option linter.style.emptyLine false
set_option linter.flexible false

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic

open Cslib.Logic.Bimodal
open Cslib.Logic

open Cslib.Logic.Bimodal.Metalogic.Core

variable {Atom : Type*}

attribute [local instance] Classical.propDecidable

/-!
### Propositional MCS Properties

These lemmas establish propositional closure properties for set-based maximal
consistent sets: disjunction intro/elim/iff and conjunction intro/elim/iff.
-/

/--
Set-based MCS: disjunction property (forward direction).

If phi in Omega or psi in Omega, then (phi or psi) in Omega.
Note: `phi.or psi = phi.neg.imp psi`
-/
theorem SetMaximalConsistent.disjunction_intro {fc : FrameClass}
    {Omega : Set (Formula Atom)} {φ ψ : Formula Atom}
    (h_mcs : SetMaximalConsistent fc Omega)
    (h : φ ∈ Omega ∨ ψ ∈ Omega) : (φ.or ψ) ∈ Omega := by
  cases h with
  | inl h_phi =>
    have h_deriv : DerivationTree fc [φ] (φ.or ψ) := by
      have h_inner : DerivationTree fc (φ.neg :: [φ]) ψ := by
        have h_phi_assume : DerivationTree fc (φ.neg :: [φ]) φ :=
          DerivationTree.assumption _ _ (by simp)
        have h_neg_assume : DerivationTree fc (φ.neg :: [φ]) φ.neg :=
          DerivationTree.assumption _ _ (by simp)
        have h_bot : DerivationTree fc (φ.neg :: [φ]) Formula.bot :=
          derivesBotFromPhiNegPhi h_phi_assume h_neg_assume
        have h_efq_thm : DerivationTree fc [] (Formula.bot.imp ψ) :=
          DerivationTree.axiom [] _ (Axiom.efq ψ) (FrameClass.base_le fc)
        have h_efq : DerivationTree fc (φ.neg :: [φ]) (Formula.bot.imp ψ) :=
          DerivationTree.weakening [] _ _ h_efq_thm (by intro; simp)
        exact DerivationTree.modus_ponens _ _ _ h_efq h_bot
      exact deductionTheorem [φ] φ.neg ψ h_inner
    have h_sub : ∀ χ ∈ [φ], χ ∈ Omega := by simp [h_phi]
    exact SetMaximalConsistent.closed_under_derivation h_mcs [φ] h_sub h_deriv
  | inr h_psi =>
    have h_deriv : DerivationTree fc [ψ] (φ.or ψ) := by
      have h_imp_s_thm : DerivationTree fc [] (ψ.imp (φ.neg.imp ψ)) :=
        DerivationTree.axiom [] _ (Axiom.imp_s ψ φ.neg) (FrameClass.base_le fc)
      have h_imp_s : DerivationTree fc [ψ] (ψ.imp (φ.neg.imp ψ)) :=
        DerivationTree.weakening [] _ _ h_imp_s_thm (by intro; simp)
      have h_psi_assume : DerivationTree fc [ψ] ψ :=
        DerivationTree.assumption _ _ (by simp)
      exact DerivationTree.modus_ponens _ _ _ h_imp_s h_psi_assume
    have h_sub : ∀ χ ∈ [ψ], χ ∈ Omega := by simp [h_psi]
    exact SetMaximalConsistent.closed_under_derivation h_mcs [ψ] h_sub h_deriv

/--
Set-based MCS: disjunction property (backward direction).

If (phi or psi) in Omega, then phi in Omega or psi in Omega.
-/
theorem SetMaximalConsistent.disjunction_elim {fc : FrameClass}
    {Omega : Set (Formula Atom)} {φ ψ : Formula Atom}
    (h_mcs : SetMaximalConsistent fc Omega)
    (h : (φ.or ψ) ∈ Omega) : φ ∈ Omega ∨ ψ ∈ Omega := by
  cases SetMaximalConsistent.negation_complete h_mcs φ with
  | inl h_phi => exact Or.inl h_phi
  | inr h_neg_phi =>
    right
    exact SetMaximalConsistent.implication_property h_mcs h h_neg_phi

/--
Set-based MCS: disjunction iff property.

(phi or psi) in Omega iff (phi in Omega or psi in Omega).
-/
theorem SetMaximalConsistent.disjunction_iff {fc : FrameClass}
    {Omega : Set (Formula Atom)} {φ ψ : Formula Atom}
    (h_mcs : SetMaximalConsistent fc Omega) :
    (φ.or ψ) ∈ Omega ↔ (φ ∈ Omega ∨ ψ ∈ Omega) :=
  ⟨SetMaximalConsistent.disjunction_elim h_mcs, SetMaximalConsistent.disjunction_intro h_mcs⟩

/--
Set-based MCS: conjunction property (forward direction).

If phi in Omega and psi in Omega, then (phi and psi) in Omega.
Note: `phi.and psi = (phi.imp psi.neg).neg`
-/
theorem SetMaximalConsistent.conjunction_intro {fc : FrameClass}
    {Omega : Set (Formula Atom)} {φ ψ : Formula Atom}
    (h_mcs : SetMaximalConsistent fc Omega)
    (h_phi : φ ∈ Omega) (h_psi : ψ ∈ Omega) : (φ.and ψ) ∈ Omega := by
  cases SetMaximalConsistent.negation_complete h_mcs (φ.imp ψ.neg) with
  | inr h_neg => exact h_neg
  | inl h_imp =>
    have h_neg_psi : ψ.neg ∈ Omega :=
      SetMaximalConsistent.implication_property h_mcs h_imp h_phi
    exfalso
    have h_deriv : DerivationTree fc [ψ, ψ.neg] Formula.bot := by
      have h_psi_assume : DerivationTree fc [ψ, ψ.neg] ψ :=
        DerivationTree.assumption _ _ (by simp)
      have h_neg_assume : DerivationTree fc [ψ, ψ.neg] ψ.neg :=
        DerivationTree.assumption _ _ (by simp)
      exact derivesBotFromPhiNegPhi h_psi_assume h_neg_assume
    have h_sub : ∀ χ ∈ [ψ, ψ.neg], χ ∈ Omega := by
      intro χ h_mem
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at h_mem
      cases h_mem with
      | inl h_eq => exact h_eq ▸ h_psi
      | inr h_eq => exact h_eq ▸ h_neg_psi
    have h_bot_in : (Formula.bot : Formula Atom) ∈ Omega :=
      SetMaximalConsistent.closed_under_derivation h_mcs [ψ, ψ.neg] h_sub h_deriv
    have h_cons := h_mcs.1
    unfold SetConsistent at h_cons
    have h_bot_deriv : DerivationTree fc
        [(Formula.bot : Formula Atom)] Formula.bot :=
      DerivationTree.assumption _ _ (by simp)
    have h_bot_sub : ∀ χ ∈ [(Formula.bot : Formula Atom)], χ ∈ Omega :=
      by simp [h_bot_in]
    exact h_cons [(Formula.bot : Formula Atom)]
      h_bot_sub ⟨h_bot_deriv⟩

/--
Set-based MCS: conjunction property (backward direction).

If (phi and psi) in Omega, then phi in Omega and psi in Omega.
-/
theorem SetMaximalConsistent.conjunction_elim {fc : FrameClass}
    {Omega : Set (Formula Atom)} {φ ψ : Formula Atom}
    (h_mcs : SetMaximalConsistent fc Omega)
    (h : (φ.and ψ) ∈ Omega) : φ ∈ Omega ∧ ψ ∈ Omega := by
  constructor
  · -- Show phi in Omega
    by_contra h_phi_not
    have h_neg_phi : φ.neg ∈ Omega := by
      cases SetMaximalConsistent.negation_complete h_mcs φ with
      | inl h => exact absurd h h_phi_not
      | inr h => exact h
    have h_deriv : DerivationTree fc [φ.neg] (φ.imp ψ.neg) := by
      have h_inner : DerivationTree fc (φ :: [φ.neg]) ψ.neg := by
        have h_phi_assume : DerivationTree fc (φ :: [φ.neg]) φ :=
          DerivationTree.assumption _ _ (by simp)
        have h_neg_assume : DerivationTree fc (φ :: [φ.neg]) φ.neg :=
          DerivationTree.assumption _ _ (by simp)
        have h_bot : DerivationTree fc (φ :: [φ.neg]) Formula.bot :=
          derivesBotFromPhiNegPhi h_phi_assume h_neg_assume
        have h_bot_weak : DerivationTree fc (ψ :: φ :: [φ.neg]) Formula.bot :=
          DerivationTree.weakening (φ :: [φ.neg]) (ψ :: φ :: [φ.neg]) _ h_bot
            (fun x hx => List.mem_cons_of_mem ψ hx)
        exact deductionTheorem (φ :: [φ.neg]) ψ Formula.bot h_bot_weak
      exact deductionTheorem [φ.neg] φ ψ.neg h_inner
    have h_sub : ∀ χ ∈ [φ.neg], χ ∈ Omega := by simp [h_neg_phi]
    have h_imp_in : (φ.imp ψ.neg) ∈ Omega :=
      SetMaximalConsistent.closed_under_derivation h_mcs [φ.neg] h_sub h_deriv
    have h_deriv_bot : DerivationTree fc [(φ.imp ψ.neg), (φ.imp ψ.neg).neg] Formula.bot := by
      have h1 : DerivationTree fc [(φ.imp ψ.neg), (φ.imp ψ.neg).neg] (φ.imp ψ.neg) :=
        DerivationTree.assumption _ _ (by simp)
      have h2 : DerivationTree fc [(φ.imp ψ.neg), (φ.imp ψ.neg).neg] (φ.imp ψ.neg).neg :=
        DerivationTree.assumption _ _ (by simp)
      exact derivesBotFromPhiNegPhi h1 h2
    have h_sub2 : ∀ χ ∈ [(φ.imp ψ.neg), (φ.imp ψ.neg).neg], χ ∈ Omega := by
      intro χ hχ
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hχ
      cases hχ with
      | inl h_eq => exact h_eq ▸ h_imp_in
      | inr h_eq => exact h_eq ▸ h
    have h_bot_in : (Formula.bot : Formula Atom) ∈ Omega :=
      SetMaximalConsistent.closed_under_derivation h_mcs _ h_sub2 h_deriv_bot
    have h_bot_deriv : DerivationTree fc
        [(Formula.bot : Formula Atom)] Formula.bot :=
      DerivationTree.assumption _ _ (by simp)
    exact h_mcs.1 [(Formula.bot : Formula Atom)]
      (by simp [h_bot_in]) ⟨h_bot_deriv⟩
  · -- Show psi in Omega (similar argument)
    by_contra h_psi_not
    have h_neg_psi : ψ.neg ∈ Omega := by
      cases SetMaximalConsistent.negation_complete h_mcs ψ with
      | inl h => exact absurd h h_psi_not
      | inr h => exact h
    have h_deriv : DerivationTree fc [ψ.neg] (φ.imp ψ.neg) := by
      have h_imp_s_thm : DerivationTree fc [] (ψ.neg.imp (φ.imp ψ.neg)) :=
        DerivationTree.axiom [] _ (Axiom.imp_s ψ.neg φ) (FrameClass.base_le fc)
      have h_imp_s : DerivationTree fc [ψ.neg] (ψ.neg.imp (φ.imp ψ.neg)) :=
        DerivationTree.weakening [] _ _ h_imp_s_thm (by intro; simp)
      have h_assume : DerivationTree fc [ψ.neg] ψ.neg :=
        DerivationTree.assumption _ _ (by simp)
      exact DerivationTree.modus_ponens _ _ _ h_imp_s h_assume
    have h_sub : ∀ χ ∈ [ψ.neg], χ ∈ Omega := by simp [h_neg_psi]
    have h_imp_in : (φ.imp ψ.neg) ∈ Omega :=
      SetMaximalConsistent.closed_under_derivation h_mcs [ψ.neg] h_sub h_deriv
    have h_deriv_bot : DerivationTree fc [(φ.imp ψ.neg), (φ.imp ψ.neg).neg] Formula.bot := by
      have h1 : DerivationTree fc [(φ.imp ψ.neg), (φ.imp ψ.neg).neg] (φ.imp ψ.neg) :=
        DerivationTree.assumption _ _ (by simp)
      have h2 : DerivationTree fc [(φ.imp ψ.neg), (φ.imp ψ.neg).neg] (φ.imp ψ.neg).neg :=
        DerivationTree.assumption _ _ (by simp)
      exact derivesBotFromPhiNegPhi h1 h2
    have h_sub2 : ∀ χ ∈ [(φ.imp ψ.neg), (φ.imp ψ.neg).neg], χ ∈ Omega := by
      intro χ hχ
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hχ
      cases hχ with
      | inl h_eq => exact h_eq ▸ h_imp_in
      | inr h_eq => exact h_eq ▸ h
    have h_bot_in : (Formula.bot : Formula Atom) ∈ Omega :=
      SetMaximalConsistent.closed_under_derivation h_mcs _ h_sub2 h_deriv_bot
    have h_bot_deriv : DerivationTree fc
        [(Formula.bot : Formula Atom)] Formula.bot :=
      DerivationTree.assumption _ _ (by simp)
    exact h_mcs.1 [(Formula.bot : Formula Atom)]
      (by simp [h_bot_in]) ⟨h_bot_deriv⟩

/--
Set-based MCS: conjunction iff property.

(phi and psi) in Omega iff (phi in Omega and psi in Omega).
-/
theorem SetMaximalConsistent.conjunction_iff {fc : FrameClass}
    {Omega : Set (Formula Atom)} {φ ψ : Formula Atom}
    (h_mcs : SetMaximalConsistent fc Omega) :
    (φ.and ψ) ∈ Omega ↔ (φ ∈ Omega ∧ ψ ∈ Omega) :=
  ⟨SetMaximalConsistent.conjunction_elim h_mcs,
   fun ⟨h1, h2⟩ => SetMaximalConsistent.conjunction_intro h_mcs h1 h2⟩

/-!
### Modal Closure Properties

These lemmas establish modal closure properties for SetMaximalConsistent sets,
using the Modal T axiom (box phi -> phi) to derive that necessity implies truth.
-/

/--
Set-based MCS: box closure property.

If box phi in Omega for a SetMaximalConsistent Omega, then phi in Omega.

**Proof Strategy**:
1. Modal T axiom: box phi -> phi
2. With box phi in Omega, derive phi via modus ponens
3. By closure: phi in Omega
-/
theorem SetMaximalConsistent.box_closure {fc : FrameClass}
    {Omega : Set (Formula Atom)} {φ : Formula Atom}
    (h_mcs : SetMaximalConsistent fc Omega)
    (h_box : Formula.box φ ∈ Omega) : φ ∈ Omega := by
  have h_modal_t_thm : DerivationTree fc [] ((Formula.box φ).imp φ) :=
    DerivationTree.axiom [] _ (Axiom.modal_t φ) (FrameClass.base_le fc)
  have h_modal_t : DerivationTree fc [Formula.box φ] ((Formula.box φ).imp φ) :=
    DerivationTree.weakening [] _ _ h_modal_t_thm (by intro; simp)
  have h_box_assume : DerivationTree fc [Formula.box φ] (Formula.box φ) :=
    DerivationTree.assumption _ _ (by simp)
  have h_deriv : DerivationTree fc [Formula.box φ] φ :=
    DerivationTree.modus_ponens _ _ _ h_modal_t h_box_assume
  have h_sub : ∀ χ ∈ [Formula.box φ], χ ∈ Omega := by simp [h_box]
  exact SetMaximalConsistent.closed_under_derivation h_mcs [Formula.box φ] h_sub h_deriv

/--
Set-based MCS: modal 4 axiom property.

If box phi in Omega for a SetMaximalConsistent Omega, then box(box phi) in Omega.

**Proof Strategy**:
1. Modal 4 axiom: box phi -> box(box phi)
2. With box phi in Omega, derive box(box phi) via modus ponens
3. By closure: box(box phi) in Omega
-/
theorem SetMaximalConsistent.box_box {fc : FrameClass}
    {Omega : Set (Formula Atom)} {φ : Formula Atom}
    (h_mcs : SetMaximalConsistent fc Omega)
    (h_box : Formula.box φ ∈ Omega) : (Formula.box φ).box ∈ Omega := by
  have h_modal_4_thm : DerivationTree fc []
      ((Formula.box φ).imp (Formula.box (Formula.box φ))) :=
    DerivationTree.axiom [] _ (Axiom.modal_4 φ) (FrameClass.base_le fc)
  have h_modal_4 : DerivationTree fc [Formula.box φ]
      ((Formula.box φ).imp (Formula.box (Formula.box φ))) :=
    DerivationTree.weakening [] _ _ h_modal_4_thm (by intro; simp)
  have h_box_assume : DerivationTree fc [Formula.box φ] (Formula.box φ) :=
    DerivationTree.assumption _ _ (by simp)
  have h_deriv : DerivationTree fc [Formula.box φ] (Formula.box φ).box :=
    DerivationTree.modus_ponens _ _ _ h_modal_4 h_box_assume
  have h_sub : ∀ χ ∈ [Formula.box φ], χ ∈ Omega := by simp [h_box]
  exact SetMaximalConsistent.closed_under_derivation h_mcs [Formula.box φ] h_sub h_deriv

/-!
### Diamond-Box Duality

These lemmas establish the classical duality between box and diamond modalities
for MCS membership: neg(box phi) iff diamond(neg phi).
-/

noncomputable section

open Cslib.Logic.Bimodal.Theorems.Perpetuity (doubleNegation dni)

/--
Set-based MCS: diamond-box duality (forward direction).

If neg(box phi) in Omega, then diamond(neg phi) in Omega.

Note: diamond psi = neg(box(neg psi)), so diamond(neg phi) = neg(box(neg(neg phi))).
-/
theorem SetMaximalConsistent.neg_box_implies_diamond_neg {fc : FrameClass}
    {Omega : Set (Formula Atom)} {φ : Formula Atom}
    (h_mcs : SetMaximalConsistent fc Omega)
    (h : (Formula.box φ).neg ∈ Omega) : φ.neg.diamond ∈ Omega := by
  unfold Formula.diamond
  cases SetMaximalConsistent.negation_complete h_mcs (φ.neg.neg.box) with
  | inr h_neg => exact h_neg
  | inl h_dne_box =>
    exfalso
    have h_dne : DerivationTree FrameClass.Base ([] : List (Formula Atom))
        (φ.neg.neg.imp φ) := doubleNegation φ
    have h_nec_dne : DerivationTree FrameClass.Base ([] : List (Formula Atom))
        (φ.neg.neg.imp φ).box :=
      DerivationTree.necessitation _ h_dne
    have h_modal_k : DerivationTree FrameClass.Base ([] : List (Formula Atom))
        ((φ.neg.neg.imp φ).box.imp ((φ.neg.neg.box).imp (φ.box))) :=
      DerivationTree.axiom [] _ (Axiom.modal_k_dist φ.neg.neg φ) trivial
    have h_impl : DerivationTree FrameClass.Base ([] : List (Formula Atom))
        ((φ.neg.neg.box).imp (φ.box)) :=
      DerivationTree.modus_ponens [] _ _ h_modal_k h_nec_dne
    -- Lift to generic fc
    have h_impl_fc : DerivationTree fc ([] : List (Formula Atom))
        ((φ.neg.neg.box).imp (φ.box)) :=
      DerivationTree.lift (FrameClass.base_le fc) h_impl
    have h_sub : ∀ χ ∈ [φ.neg.neg.box], χ ∈ Omega := by simp [h_dne_box]
    have h_impl_ctx : DerivationTree fc [φ.neg.neg.box]
        ((φ.neg.neg.box).imp (φ.box)) :=
      DerivationTree.weakening [] _ _ h_impl_fc (by intro; simp)
    have h_assume : DerivationTree fc [φ.neg.neg.box] φ.neg.neg.box :=
      DerivationTree.assumption _ _ (by simp)
    have h_deriv : DerivationTree fc [φ.neg.neg.box] φ.box :=
      DerivationTree.modus_ponens _ _ _ h_impl_ctx h_assume
    have h_box_in : φ.box ∈ Omega :=
      SetMaximalConsistent.closed_under_derivation h_mcs [φ.neg.neg.box] h_sub h_deriv
    have h_deriv_bot : DerivationTree fc [φ.box, (φ.box).neg] Formula.bot := by
      have h1 : DerivationTree fc [φ.box, (φ.box).neg] φ.box :=
        DerivationTree.assumption _ _ (by simp)
      have h2 : DerivationTree fc [φ.box, (φ.box).neg] (φ.box).neg :=
        DerivationTree.assumption _ _ (by simp)
      exact derivesBotFromPhiNegPhi h1 h2
    have h_sub2 : ∀ χ ∈ [φ.box, (φ.box).neg], χ ∈ Omega := by
      intro χ hχ
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hχ
      cases hχ with
      | inl h_eq => exact h_eq ▸ h_box_in
      | inr h_eq => exact h_eq ▸ h
    have h_bot_in : (Formula.bot : Formula Atom) ∈ Omega :=
      SetMaximalConsistent.closed_under_derivation h_mcs _ h_sub2 h_deriv_bot
    have h_bot_deriv : DerivationTree fc
        [(Formula.bot : Formula Atom)] Formula.bot :=
      DerivationTree.assumption _ _ (by simp)
    exact h_mcs.1 [(Formula.bot : Formula Atom)]
      (by simp [h_bot_in]) ⟨h_bot_deriv⟩

/--
Set-based MCS: diamond-box duality (backward direction).

If diamond(neg phi) in Omega, then neg(box phi) in Omega.
-/
theorem SetMaximalConsistent.diamond_neg_implies_neg_box {fc : FrameClass}
    {Omega : Set (Formula Atom)} {φ : Formula Atom}
    (h_mcs : SetMaximalConsistent fc Omega)
    (h : φ.neg.diamond ∈ Omega) : (Formula.box φ).neg ∈ Omega := by
  unfold Formula.diamond at h
  cases SetMaximalConsistent.negation_complete h_mcs (Formula.box φ) with
  | inr h_neg => exact h_neg
  | inl h_box =>
    exfalso
    have h_dni : DerivationTree FrameClass.Base ([] : List (Formula Atom))
        (φ.imp φ.neg.neg) := dni φ
    have h_nec_dni : DerivationTree FrameClass.Base ([] : List (Formula Atom))
        (φ.imp φ.neg.neg).box :=
      DerivationTree.necessitation _ h_dni
    have h_modal_k : DerivationTree FrameClass.Base ([] : List (Formula Atom))
        ((φ.imp φ.neg.neg).box.imp ((φ.box).imp (φ.neg.neg.box))) :=
      DerivationTree.axiom [] _ (Axiom.modal_k_dist φ φ.neg.neg) trivial
    have h_impl : DerivationTree FrameClass.Base ([] : List (Formula Atom))
        ((φ.box).imp (φ.neg.neg.box)) :=
      DerivationTree.modus_ponens [] _ _ h_modal_k h_nec_dni
    -- Lift to generic fc
    have h_impl_fc : DerivationTree fc ([] : List (Formula Atom))
        ((φ.box).imp (φ.neg.neg.box)) :=
      DerivationTree.lift (FrameClass.base_le fc) h_impl
    have h_sub : ∀ χ ∈ [φ.box], χ ∈ Omega := by simp [h_box]
    have h_impl_ctx : DerivationTree fc [φ.box]
        ((φ.box).imp (φ.neg.neg.box)) :=
      DerivationTree.weakening [] _ _ h_impl_fc (by intro; simp)
    have h_assume : DerivationTree fc [φ.box] φ.box :=
      DerivationTree.assumption _ _ (by simp)
    have h_deriv : DerivationTree fc [φ.box] φ.neg.neg.box :=
      DerivationTree.modus_ponens _ _ _ h_impl_ctx h_assume
    have h_dne_box_in : φ.neg.neg.box ∈ Omega :=
      SetMaximalConsistent.closed_under_derivation h_mcs [φ.box] h_sub h_deriv
    have h_deriv_bot : DerivationTree fc
        [φ.neg.neg.box, (φ.neg.neg.box).neg] Formula.bot := by
      have h1 : DerivationTree fc [φ.neg.neg.box, (φ.neg.neg.box).neg]
          φ.neg.neg.box :=
        DerivationTree.assumption _ _ (by simp)
      have h2 : DerivationTree fc [φ.neg.neg.box, (φ.neg.neg.box).neg]
          (φ.neg.neg.box).neg :=
        DerivationTree.assumption _ _ (by simp)
      exact derivesBotFromPhiNegPhi h1 h2
    have h_sub2 : ∀ χ ∈ [φ.neg.neg.box, (φ.neg.neg.box).neg], χ ∈ Omega := by
      intro χ hχ
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hχ
      cases hχ with
      | inl h_eq => exact h_eq ▸ h_dne_box_in
      | inr h_eq => exact h_eq ▸ h
    have h_bot_in : (Formula.bot : Formula Atom) ∈ Omega :=
      SetMaximalConsistent.closed_under_derivation h_mcs _ h_sub2 h_deriv_bot
    have h_bot_deriv : DerivationTree fc
        [(Formula.bot : Formula Atom)] Formula.bot :=
      DerivationTree.assumption _ _ (by simp)
    exact h_mcs.1 [(Formula.bot : Formula Atom)]
      (by simp [h_bot_in]) ⟨h_bot_deriv⟩

/--
Set-based MCS: diamond-box duality iff property.

neg(box phi) in Omega iff diamond(neg phi) in Omega.

This establishes the classical duality between box and diamond:
neg(box phi) iff diamond(neg phi) (equivalently, box phi iff neg(diamond(neg phi))).
-/
theorem SetMaximalConsistent.diamond_box_duality {fc : FrameClass}
    {Omega : Set (Formula Atom)} {φ : Formula Atom}
    (h_mcs : SetMaximalConsistent fc Omega) :
    (Formula.box φ).neg ∈ Omega ↔ φ.neg.diamond ∈ Omega :=
  ⟨SetMaximalConsistent.neg_box_implies_diamond_neg h_mcs,
   SetMaximalConsistent.diamond_neg_implies_neg_box h_mcs⟩

end -- noncomputable section

end Cslib.Logic.Bimodal.Metalogic
