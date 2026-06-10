/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.Decidability.FMP.FiniteModel
public import Cslib.Logics.Bimodal.Semantics.Truth
public import Cslib.Logics.Bimodal.Semantics.Validity

/-!
# Truth Preservation (Filtration Lemma) - Infrastructure

This module provides the infrastructure for proving truth preservation
under filtration. The main Filtration Lemma establishes that MCS membership
is preserved through the quotient construction.

## Overview

The Filtration Lemma states: for any formula ψ in the subformula closure of φ,
ψ is true at a world w iff ψ is "true" at the equivalence class [w].

For our MCS-based approach:
- "Worlds" are closure MCS
- "Truth" at a closure MCS Omega is membership: ψ ∈ Omega
- The filtration lemma becomes: truth preservation through the quotient

## Main Results

- `mcsTruth`: Truth in a closure MCS (membership)
- `filteredMcsTruth`: Truth lifted to filtered worlds
- `filtration_lemma_membership`: Main filtration lemma
- Lemmas for bot, negation, implication, box, temporal operators

## References

- Blackburn, de Rijke, Venema: Modal Logic (Ch 2.3)
- Ported from BimodalLogic/Theories/Bimodal/Metalogic/Decidability/FMP/TruthPreservation.lean
-/

set_option linter.style.emptyLine false

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.Decidability.FMP

open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Metalogic.Core

variable {Atom : Type} [DecidableEq Atom]

/-!
## MCS Truth Definition

For the MCS-based approach, "truth" at a closure MCS Omega is just membership.
This is well-defined for closure formulas since they're in the closure.
-/

/--
A formula is "MCS-true" at a closure MCS if it's a member of the MCS.
-/
def mcsTruth (phi : Formula Atom) (Omega : ClosureMCSBundle phi)
    (ψ : Formula Atom) : Prop :=
  ψ ∈ Omega.carrier

/--
MCS truth respects filtration equivalence for closure formulas.
-/
theorem mcsTruth_respects_equiv (phi ψ : Formula Atom)
    (hψ : ψ ∈ subformulaClosure phi)
    {Omega Theta : ClosureMCSBundle phi}
    (h : ClosureMCSEquiv phi Omega Theta) :
    mcsTruth phi Omega ψ ↔ mcsTruth phi Theta ψ := by
  simp only [mcsTruth]
  exact h ψ hψ

/--
Lift MCS truth to filtered worlds.
-/
def filteredMcsTruth (phi ψ : Formula Atom) (hψ : ψ ∈ subformulaClosure phi)
    (w : FilteredWorld phi) : Prop :=
  Quotient.lift (s := ClosureMCSSetoid phi)
    (fun (Omega : ClosureMCSBundle phi) => mcsTruth phi Omega ψ)
    (fun (Omega Theta : ClosureMCSBundle phi)
      (h : ClosureMCSEquiv phi Omega Theta) =>
      propext (mcsTruth_respects_equiv phi ψ hψ h)) w

/-!
## Basic MCS Properties for Truth Preservation

These properties establish that MCS membership behaves like truth.
-/

/--
Bot is never in a consistent MCS.
-/
theorem bot_not_in_mcs {phi : Formula Atom} (Omega : ClosureMCSBundle phi) :
    Formula.bot ∉ Omega.carrier := by
  intro h_bot
  have h_deriv : DerivationTree FrameClass.Base
      ([(Formula.bot : Formula Atom)]) Formula.bot :=
    DerivationTree.assumption [(Formula.bot : Formula Atom)] Formula.bot
      List.mem_cons_self
  have h_cons := closure_mcs_consistent Omega.is_mcs
  apply h_cons [(Formula.bot : Formula Atom)]
  · intro ψ hψ
    simp only [List.mem_singleton] at hψ
    exact hψ ▸ h_bot
  · exact ⟨h_deriv⟩

/--
Filtration lemma for Bot: bot is never "true" in the filtered model.
-/
theorem filtration_lemma_bot (phi : Formula Atom) (w : FilteredWorld phi)
    (h_clos : Formula.bot ∈ subformulaClosure phi) :
    ¬filteredMcsTruth phi Formula.bot h_clos w := by
  obtain ⟨Omega, hOmega⟩ := Quotient.exists_rep w
  simp only [← hOmega, filteredMcsTruth, mcsTruth]
  exact bot_not_in_mcs Omega

/--
An MCS cannot contain both a formula and its negation.
-/
theorem mcs_not_both_and_neg {phi : Formula Atom}
    {Omega : ClosureMCSBundle phi}
    {ψ : Formula Atom}
    (h_psi : ψ ∈ Omega.carrier)
    (h_neg : ψ.neg ∈ Omega.carrier) :
    False := by
  have h_deriv : DerivationTree FrameClass.Base [ψ, ψ.neg] Formula.bot := by
    have h1 : DerivationTree FrameClass.Base [ψ, ψ.neg] ψ.neg :=
      DerivationTree.assumption [ψ, ψ.neg] ψ.neg
        (List.mem_cons_of_mem _ List.mem_cons_self)
    have h2 : DerivationTree FrameClass.Base [ψ, ψ.neg] ψ :=
      DerivationTree.assumption [ψ, ψ.neg] ψ List.mem_cons_self
    exact DerivationTree.modus_ponens [ψ, ψ.neg] ψ Formula.bot h1 h2
  have h_sub : ∀ x ∈ [ψ, ψ.neg], x ∈ Omega.carrier := by
    intro x hx
    simp only [List.mem_cons, List.mem_nil_iff] at hx
    rcases hx with rfl | rfl | hf
    · exact h_psi
    · exact h_neg
    · exact hf.elim
  exact closure_mcs_consistent Omega.is_mcs [ψ, ψ.neg] h_sub ⟨h_deriv⟩

/--
MCS implication property: if φ → ψ ∈ Omega and φ ∈ Omega, then ψ ∈ Omega
(assuming ψ is in the closure).
-/
theorem mcs_imp_elim {phi : Formula Atom} {Omega : ClosureMCSBundle phi}
    {ψ χ : Formula Atom}
    (h_imp : (ψ.imp χ) ∈ Omega.carrier)
    (h_psi : ψ ∈ Omega.carrier)
    (h_chi_clos : χ ∈ closureWithNeg phi) :
    χ ∈ Omega.carrier := by
  have h_deriv : DerivationTree FrameClass.Base [ψ.imp χ, ψ] χ := by
    have h1 : DerivationTree FrameClass.Base [ψ.imp χ, ψ] (ψ.imp χ) :=
      DerivationTree.assumption [ψ.imp χ, ψ] (ψ.imp χ) List.mem_cons_self
    have h2 : DerivationTree FrameClass.Base [ψ.imp χ, ψ] ψ :=
      DerivationTree.assumption [ψ.imp χ, ψ] ψ
        (List.mem_cons_of_mem _ List.mem_cons_self)
    exact DerivationTree.modus_ponens [ψ.imp χ, ψ] ψ χ h1 h2
  have h_sub : ∀ x ∈ [ψ.imp χ, ψ], x ∈ Omega.carrier := by
    intro x hx
    simp only [List.mem_cons, List.mem_nil_iff] at hx
    rcases hx with rfl | rfl | hf
    · exact h_imp
    · exact h_psi
    · exact hf.elim
  exact closure_mcs_deductively_closed Omega.is_mcs h_sub h_deriv h_chi_clos

/--
Filtration lemma for implication (forward direction).
If ψ → χ ∈ Omega and ψ ∈ Omega, then χ ∈ Omega.
-/
theorem filtration_imp_forward {phi : Formula Atom}
    {Omega : ClosureMCSBundle phi}
    {ψ χ : Formula Atom}
    (h_imp_clos : (ψ.imp χ) ∈ subformulaClosure phi)
    (h_imp : (ψ.imp χ) ∈ Omega.carrier)
    (h_psi : ψ ∈ Omega.carrier) :
    χ ∈ Omega.carrier := by
  have h_chi_subclos : χ ∈ subformulaClosure phi :=
    closure_imp_right phi ψ χ h_imp_clos
  have h_chi_clos : χ ∈ closureWithNeg phi :=
    subformulaClosure_subset_closureWithNeg phi h_chi_subclos
  exact mcs_imp_elim h_imp h_psi h_chi_clos

/-!
## MCS Properties for Modal Operators

These properties establish how modal operators behave in closure MCS.
-/

/--
Box closure property for closure MCS: □ψ ∈ Omega implies ψ ∈ Omega.

This uses the Modal T axiom (□φ → φ).
-/
theorem mcs_box_closure {phi : Formula Atom}
    {Omega : ClosureMCSBundle phi}
    {ψ : Formula Atom}
    (h_box : ψ.box ∈ Omega.carrier)
    (h_psi_clos : ψ ∈ closureWithNeg phi) :
    ψ ∈ Omega.carrier := by
  have h_modal_t_thm : DerivationTree FrameClass.Base
      ([] : List (Formula Atom)) ((ψ.box).imp ψ) :=
    DerivationTree.axiom [] _ (Axiom.modal_t ψ) trivial
  have h_deriv : DerivationTree FrameClass.Base [ψ.box] ψ := by
    have h_axiom : DerivationTree FrameClass.Base [ψ.box] ((ψ.box).imp ψ) :=
      DerivationTree.weakening [] _ _ h_modal_t_thm (by intro; simp)
    have h_assume : DerivationTree FrameClass.Base [ψ.box] ψ.box :=
      DerivationTree.assumption _ _ (by simp)
    exact DerivationTree.modus_ponens _ _ _ h_axiom h_assume
  have h_sub : ∀ x ∈ [ψ.box], x ∈ Omega.carrier := by simp [h_box]
  exact closure_mcs_deductively_closed Omega.is_mcs h_sub h_deriv h_psi_clos

/--
Box transitivity for closure MCS: □ψ ∈ Omega implies □□ψ ∈ Omega.

This uses the Modal 4 axiom (□φ → □□φ).
-/
theorem mcs_box_box {phi : Formula Atom}
    {Omega : ClosureMCSBundle phi}
    {ψ : Formula Atom}
    (h_box : ψ.box ∈ Omega.carrier)
    (h_boxbox_clos : ψ.box.box ∈ closureWithNeg phi) :
    ψ.box.box ∈ Omega.carrier := by
  have h_modal_4_thm : DerivationTree FrameClass.Base
      ([] : List (Formula Atom)) ((ψ.box).imp (ψ.box.box)) :=
    DerivationTree.axiom [] _ (Axiom.modal_4 ψ) trivial
  have h_deriv : DerivationTree FrameClass.Base [ψ.box] ψ.box.box := by
    have h_axiom : DerivationTree FrameClass.Base [ψ.box] ((ψ.box).imp (ψ.box.box)) :=
      DerivationTree.weakening [] _ _ h_modal_4_thm (by intro; simp)
    have h_assume : DerivationTree FrameClass.Base [ψ.box] ψ.box :=
      DerivationTree.assumption _ _ (by simp)
    exact DerivationTree.modus_ponens _ _ _ h_axiom h_assume
  have h_sub : ∀ x ∈ [ψ.box], x ∈ Omega.carrier := by simp [h_box]
  exact closure_mcs_deductively_closed Omega.is_mcs h_sub h_deriv h_boxbox_clos

/--
Filtration lemma for Box (forward direction).
If □ψ ∈ closure(φ) and □ψ ∈ Omega, then ψ ∈ Omega.
-/
theorem filtration_box_forward {phi : Formula Atom}
    {Omega : ClosureMCSBundle phi}
    {ψ : Formula Atom}
    (h_box_clos : ψ.box ∈ subformulaClosure phi)
    (h_box : ψ.box ∈ Omega.carrier) :
    ψ ∈ Omega.carrier := by
  have h_psi_clos : ψ ∈ subformulaClosure phi := closure_box phi ψ h_box_clos
  have h_psi_clneg : ψ ∈ closureWithNeg phi :=
    subformulaClosure_subset_closureWithNeg phi h_psi_clos
  exact mcs_box_closure h_box h_psi_clneg

/-!
## MCS Properties for Temporal Operators
-/

/--
All-future transitivity for closure MCS: Gψ ∈ Omega implies GGψ ∈ Omega.

This uses the temporal 4 axiom (Gφ → GGφ).
-/
theorem mcs_allFuture_allFuture {phi : Formula Atom}
    {Omega : ClosureMCSBundle phi}
    {ψ : Formula Atom}
    (h_future : ψ.allFuture ∈ Omega.carrier)
    (h_future_future_clos : ψ.allFuture.allFuture ∈ closureWithNeg phi) :
    ψ.allFuture.allFuture ∈ Omega.carrier := by
  have h_temp_4_thm : DerivationTree FrameClass.Base
      ([] : List (Formula Atom))
      ((ψ.allFuture).imp (ψ.allFuture.allFuture)) :=
    temp_4_derived ψ
  have h_deriv : DerivationTree FrameClass.Base
      [ψ.allFuture] ψ.allFuture.allFuture := by
    have h_axiom : DerivationTree FrameClass.Base
        [ψ.allFuture] ((ψ.allFuture).imp (ψ.allFuture.allFuture)) :=
      DerivationTree.weakening [] _ _ h_temp_4_thm (by intro; simp)
    have h_assume : DerivationTree FrameClass.Base [ψ.allFuture] ψ.allFuture :=
      DerivationTree.assumption _ _ (by simp)
    exact DerivationTree.modus_ponens _ _ _ h_axiom h_assume
  have h_sub : ∀ x ∈ [ψ.allFuture], x ∈ Omega.carrier := by simp [h_future]
  exact closure_mcs_deductively_closed Omega.is_mcs h_sub h_deriv h_future_future_clos

/--
All-past transitivity for closure MCS: Hψ ∈ Omega implies HHψ ∈ Omega.

This uses the derived temporal 4 axiom for past (Hφ → HHφ).
-/
theorem mcs_allPast_allPast {phi : Formula Atom}
    {Omega : ClosureMCSBundle phi}
    {ψ : Formula Atom}
    (h_past : ψ.allPast ∈ Omega.carrier)
    (h_past_past_clos : ψ.allPast.allPast ∈ closureWithNeg phi) :
    ψ.allPast.allPast ∈ Omega.carrier := by
  have h_temp_4_past_thm : DerivationTree FrameClass.Base
      ([] : List (Formula Atom))
      ((ψ.allPast).imp (ψ.allPast.allPast)) :=
    temp_4_past ψ
  have h_deriv : DerivationTree FrameClass.Base
      [ψ.allPast] ψ.allPast.allPast := by
    have h_axiom : DerivationTree FrameClass.Base
        [ψ.allPast] ((ψ.allPast).imp (ψ.allPast.allPast)) :=
      DerivationTree.weakening [] _ _ h_temp_4_past_thm (by intro; simp)
    have h_assume : DerivationTree FrameClass.Base [ψ.allPast] ψ.allPast :=
      DerivationTree.assumption _ _ (by simp)
    exact DerivationTree.modus_ponens _ _ _ h_axiom h_assume
  have h_sub : ∀ x ∈ [ψ.allPast], x ∈ Omega.carrier := by simp [h_past]
  exact closure_mcs_deductively_closed Omega.is_mcs h_sub h_deriv h_past_past_clos

/-!
## Main Filtration Lemma
-/

/--
The main filtration lemma for MCS-based FMP.

For any formula ψ in the subformula closure of φ:
ψ ∈ Omega iff ψ is "true" in the filtered model at [Omega].
-/
theorem filtration_lemma_membership {phi : Formula Atom}
    {Omega : ClosureMCSBundle phi}
    {ψ : Formula Atom} (h_clos : ψ ∈ subformulaClosure phi) :
    (ψ ∈ Omega.carrier) ↔
    filteredMcsTruth phi ψ h_clos (toFilteredWorld phi Omega) := by
  simp only [filteredMcsTruth, toFilteredWorld, mcsTruth]
  rfl

/--
Negation completeness for closure MCS: for ψ ∈ closure(φ),
either ψ ∈ Omega or ψ.neg ∈ Omega.
-/
theorem mcs_closure_negation_complete {phi : Formula Atom}
    {Omega : ClosureMCSBundle phi}
    {ψ : Formula Atom} (h_clos : ψ ∈ subformulaClosure phi) :
    ψ ∈ Omega.carrier ∨ ψ.neg ∈ Omega.carrier :=
  closure_mcs_negation_complete Omega.is_mcs ψ h_clos

/--
Implication introduction for closure MCS:
if (ψ ∈ Omega implies χ ∈ Omega), then (ψ → χ) ∈ Omega.
-/
theorem mcs_imp_intro {phi : Formula Atom}
    {Omega : ClosureMCSBundle phi}
    {ψ χ : Formula Atom}
    (h_imp_clos : (ψ.imp χ) ∈ closureWithNeg phi)
    (h_psi_clos : ψ ∈ subformulaClosure phi)
    (h : ψ ∈ Omega.carrier → χ ∈ Omega.carrier) :
    (ψ.imp χ) ∈ Omega.carrier := by
  cases mcs_closure_negation_complete h_psi_clos with
  | inl h_psi =>
    have h_chi : χ ∈ Omega.carrier := h h_psi
    have h_imp_s_thm : DerivationTree FrameClass.Base
        ([] : List (Formula Atom)) (χ.imp (ψ.imp χ)) :=
      DerivationTree.axiom [] _ (Axiom.imp_s χ ψ) trivial
    have h_deriv : DerivationTree FrameClass.Base [χ] (ψ.imp χ) := by
      have h_axiom : DerivationTree FrameClass.Base [χ] (χ.imp (ψ.imp χ)) :=
        DerivationTree.weakening [] _ _ h_imp_s_thm (by intro; simp)
      have h_assume : DerivationTree FrameClass.Base [χ] χ :=
        DerivationTree.assumption _ _ (by simp)
      exact DerivationTree.modus_ponens _ _ _ h_axiom h_assume
    have h_sub : ∀ x ∈ [χ], x ∈ Omega.carrier := by simp [h_chi]
    exact closure_mcs_deductively_closed Omega.is_mcs h_sub h_deriv h_imp_clos
  | inr h_neg_psi =>
    have h_deriv : DerivationTree FrameClass.Base [ψ.neg] (ψ.imp χ) := by
      have h_inner : DerivationTree FrameClass.Base (ψ :: [ψ.neg]) χ := by
        have h_psi_assume : DerivationTree FrameClass.Base (ψ :: [ψ.neg]) ψ :=
          DerivationTree.assumption _ _ (by simp)
        have h_neg_assume : DerivationTree FrameClass.Base (ψ :: [ψ.neg]) ψ.neg :=
          DerivationTree.assumption _ _ (by simp)
        have h_bot : DerivationTree FrameClass.Base (ψ :: [ψ.neg]) Formula.bot :=
          derivesBotFromPhiNegPhi h_psi_assume h_neg_assume
        have h_efq_thm : DerivationTree FrameClass.Base
            ([] : List (Formula Atom)) (Formula.bot.imp χ) :=
          DerivationTree.axiom [] _ (Axiom.efq χ) trivial
        have h_efq : DerivationTree FrameClass.Base (ψ :: [ψ.neg]) (Formula.bot.imp χ) :=
          DerivationTree.weakening [] _ _ h_efq_thm (by intro; simp)
        exact DerivationTree.modus_ponens _ _ _ h_efq h_bot
      exact deductionTheorem [ψ.neg] ψ χ h_inner
    have h_sub : ∀ x ∈ [ψ.neg], x ∈ Omega.carrier := by simp [h_neg_psi]
    exact closure_mcs_deductively_closed Omega.is_mcs h_sub h_deriv h_imp_clos

end Cslib.Logic.Bimodal.Metalogic.Decidability.FMP
