/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.Bundle.TemporalContent
public import Cslib.Logics.Bimodal.Metalogic.Bundle.CanonicalFrame
public import Cslib.Logics.Bimodal.Metalogic.Bundle.WitnessSeed
public import Cslib.Logics.Bimodal.Metalogic.Core.MCSProperties

/-!
# Succ Relation for Discrete Temporal Frames

Defines the Succ (immediate successor) relation for discrete temporal frames.

## References

* Ported from BimodalLogic/Theories/Bimodal/Metalogic/Bundle/SuccRelation.lean
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.Bundle

open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Metalogic.Core

attribute [local instance] Classical.propDecidable

variable {Atom : Type*}

/-! ## Succ Definition -/

/--
Immediate successor relation: u sees v as its next state.

**Condition (1)**: G-persistence - `g_content u ⊆ v`.
**Condition (2)**: F-step - `f_content u ⊆ v ∪ f_content v`.
-/
def Succ (u v : Set (Formula Atom)) : Prop :=
  g_content u ⊆ v ∧ f_content u ⊆ v ∪ f_content v

/-! ## Accessor Theorems -/

theorem Succ.g_persistence {u v : Set (Formula Atom)} (h : Succ u v) : g_content u ⊆ v := h.1

theorem Succ.f_step {u v : Set (Formula Atom)} (h : Succ u v) : f_content u ⊆ v ∪ f_content v := h.2

/-! ## Relationship to ExistsTask -/

theorem Succ_implies_CanonicalR (u v : Set (Formula Atom)) (h : Succ u v) :
    ExistsTask u v := h.1

/-! ## g/h Duality for Succ -/

theorem Succ_implies_h_content_reverse
    (u v : Set (Formula Atom)) (h_mcs_u : SetMaximalConsistent (FrameClass.Base : FrameClass) u) (h_mcs_v : SetMaximalConsistent (FrameClass.Base : FrameClass) v)
    (h_succ : Succ u v) :
    h_content v ⊆ u :=
  g_content_subset_implies_h_content_reverse u v h_mcs_u h_mcs_v h_succ.1

/-! ## Auxiliary Lemmas for Single-Step Forcing -/

lemma G_neg_implies_not_F (M : Set (Formula Atom)) (h_mcs : SetMaximalConsistent (FrameClass.Base : FrameClass) M) (phi : Formula Atom)
    (h_G_neg : Formula.allFuture phi.neg ∈ M) :
    Formula.someFuture phi ∉ M := by
  intro h_F
  exact someFuture_allFuture_neg_absurd h_mcs phi h_F h_G_neg

lemma neg_FF_implies_GG_neg_in_mcs (M : Set (Formula Atom)) (h_mcs : SetMaximalConsistent (FrameClass.Base : FrameClass) M) (phi : Formula Atom)
    (h_neg_FF : (Formula.someFuture (Formula.someFuture phi)).neg ∈ M) :
    Formula.allFuture (Formula.allFuture phi.neg) ∈ M := by
  rcases SetMaximalConsistent.negation_complete h_mcs (Formula.allFuture (Formula.allFuture phi.neg)) with
    h_goal | h_neg_goal
  · exact h_goal
  · exfalso
    have h_dne1 : DerivationTree FrameClass.Base [] ((Formula.allFuture (Formula.allFuture phi.neg)).neg.imp
        (Formula.someFuture (Formula.allFuture phi.neg).neg)) :=
      Theorems.Propositional.double_negation _
    have h_F_neg_G : Formula.someFuture (Formula.allFuture phi.neg).neg ∈ M :=
      SetMaximalConsistent.implication_property h_mcs (theorem_in_mcs h_mcs h_dne1) h_neg_goal
    have h_dne2_base : DerivationTree FrameClass.Base [] ((Formula.someFuture phi.neg.neg).neg.neg.imp
        (Formula.someFuture phi.neg.neg)) :=
      Theorems.Propositional.double_negation _
    have h_dne2_nec : DerivationTree FrameClass.Base [] (((Formula.someFuture phi.neg.neg).neg.neg.imp
        (Formula.someFuture phi.neg.neg)).allFuture) :=
      DerivationTree.temporal_necessitation _ h_dne2_base
    have h_dne2_bx3 : DerivationTree FrameClass.Base [] (((Formula.someFuture phi.neg.neg).neg.neg.imp
        (Formula.someFuture phi.neg.neg)).allFuture.imp
        ((Formula.untl (Formula.someFuture phi.neg.neg).neg.neg Formula.top).imp
         (Formula.untl (Formula.someFuture phi.neg.neg) Formula.top))) :=
      DerivationTree.axiom [] _
        (Axiom.right_mono_until
          (Formula.someFuture phi.neg.neg).neg.neg
          (Formula.someFuture phi.neg.neg) Formula.top) trivial
    have h_F_dne2 : DerivationTree FrameClass.Base [] ((Formula.someFuture (Formula.someFuture phi.neg.neg).neg.neg).imp
        (Formula.someFuture (Formula.someFuture phi.neg.neg))) :=
      DerivationTree.modus_ponens [] _ _ h_dne2_bx3 h_dne2_nec
    have h_FF_negneg : Formula.someFuture (Formula.someFuture phi.neg.neg) ∈ M :=
      SetMaximalConsistent.implication_property h_mcs (theorem_in_mcs h_mcs h_F_dne2) h_F_neg_G
    have h_dne3_base : DerivationTree FrameClass.Base [] (phi.neg.neg.imp phi) :=
      Theorems.Propositional.double_negation _
    have h_dne3_nec : DerivationTree FrameClass.Base [] ((phi.neg.neg.imp phi).allFuture) :=
      DerivationTree.temporal_necessitation _ h_dne3_base
    have h_dne3_bx3 : DerivationTree FrameClass.Base [] ((phi.neg.neg.imp phi).allFuture.imp
        ((Formula.untl phi.neg.neg Formula.top).imp (Formula.untl phi Formula.top))) :=
      DerivationTree.axiom [] _
        (Axiom.right_mono_until phi.neg.neg phi Formula.top) trivial
    have h_F_dne3 : DerivationTree FrameClass.Base [] ((Formula.someFuture phi.neg.neg).imp (Formula.someFuture phi)) :=
      DerivationTree.modus_ponens [] _ _ h_dne3_bx3 h_dne3_nec
    have h_lift_nec : DerivationTree FrameClass.Base [] (((Formula.someFuture phi.neg.neg).imp (Formula.someFuture phi)).allFuture) :=
      DerivationTree.temporal_necessitation _ h_F_dne3
    have h_lift_bx3 : DerivationTree FrameClass.Base [] (((Formula.someFuture phi.neg.neg).imp (Formula.someFuture phi)).allFuture.imp
        ((Formula.untl (Formula.someFuture phi.neg.neg) Formula.top).imp
         (Formula.untl (Formula.someFuture phi) Formula.top))) :=
      DerivationTree.axiom [] _
        (Axiom.right_mono_until
          (Formula.someFuture phi.neg.neg) (Formula.someFuture phi) Formula.top) trivial
    have h_FF_lift : DerivationTree FrameClass.Base [] ((Formula.someFuture (Formula.someFuture phi.neg.neg)).imp
        (Formula.someFuture (Formula.someFuture phi))) :=
      DerivationTree.modus_ponens [] _ _ h_lift_bx3 h_lift_nec
    have h_FF_phi : Formula.someFuture (Formula.someFuture phi) ∈ M :=
      SetMaximalConsistent.implication_property h_mcs (theorem_in_mcs h_mcs h_FF_lift) h_FF_negneg
    exact set_consistent_not_both h_mcs.1 (Formula.someFuture (Formula.someFuture phi))
      h_FF_phi h_neg_FF

/-! ## Single-Step Forcing Theorem -/

theorem single_step_forcing
    (u v : Set (Formula Atom)) (h_mcs_u : SetMaximalConsistent (FrameClass.Base : FrameClass) u) (h_mcs_v : SetMaximalConsistent (FrameClass.Base : FrameClass) v)
    (phi : Formula Atom)
    (h_F : Formula.someFuture phi ∈ u)
    (h_FF_not : Formula.someFuture (Formula.someFuture phi) ∉ u)
    (h_succ : Succ u v) :
    phi ∈ v := by
  have h_neg_FF : (Formula.someFuture (Formula.someFuture phi)).neg ∈ u := by
    cases SetMaximalConsistent.negation_complete h_mcs_u (Formula.someFuture (Formula.someFuture phi)) with
    | inl h_in => exact absurd h_in h_FF_not
    | inr h_neg => exact h_neg
  have h_GG_neg : Formula.allFuture (Formula.allFuture phi.neg) ∈ u :=
    neg_FF_implies_GG_neg_in_mcs u h_mcs_u phi h_neg_FF
  have h_G_neg_in_g : Formula.allFuture phi.neg ∈ g_content u := h_GG_neg
  have h_G_neg_in_v : Formula.allFuture phi.neg ∈ v := h_succ.1 h_G_neg_in_g
  have h_F_not_v : Formula.someFuture phi ∉ v :=
    G_neg_implies_not_F v h_mcs_v phi h_G_neg_in_v
  have h_phi_in_f_content_u : phi ∈ f_content u := h_F
  have h_union : phi ∈ v ∪ f_content v := h_succ.2 h_phi_in_f_content_u
  rcases Set.mem_or_mem_of_mem_union h_union with h_in_v | h_in_f_v
  · exact h_in_v
  · exact absurd h_in_f_v h_F_not_v

/-! ## Past Direction Lemmas -/

lemma H_neg_implies_not_P (M : Set (Formula Atom)) (h_mcs : SetMaximalConsistent (FrameClass.Base : FrameClass) M) (phi : Formula Atom)
    (h_H_neg : Formula.allPast phi.neg ∈ M) :
    Formula.somePast phi ∉ M := by
  intro h_P
  exact somePast_allPast_neg_absurd h_mcs phi h_P h_H_neg

lemma neg_PP_implies_HH_neg_in_mcs (M : Set (Formula Atom)) (h_mcs : SetMaximalConsistent (FrameClass.Base : FrameClass) M) (phi : Formula Atom)
    (h_neg_PP : (Formula.somePast (Formula.somePast phi)).neg ∈ M) :
    Formula.allPast (Formula.allPast phi.neg) ∈ M := by
  rcases SetMaximalConsistent.negation_complete h_mcs (Formula.allPast (Formula.allPast phi.neg)) with
    h_goal | h_neg_goal
  · exact h_goal
  · exfalso
    have h_dne1 : DerivationTree FrameClass.Base [] ((Formula.allPast (Formula.allPast phi.neg)).neg.imp
        (Formula.somePast (Formula.allPast phi.neg).neg)) :=
      Theorems.Propositional.double_negation _
    have h_P_neg_H : Formula.somePast (Formula.allPast phi.neg).neg ∈ M :=
      SetMaximalConsistent.implication_property h_mcs (theorem_in_mcs h_mcs h_dne1) h_neg_goal
    have h_dne2_base : DerivationTree FrameClass.Base [] ((Formula.somePast phi.neg.neg).neg.neg.imp
        (Formula.somePast phi.neg.neg)) :=
      Theorems.Propositional.double_negation _
    have h_dne2_nec : DerivationTree FrameClass.Base [] (((Formula.somePast phi.neg.neg).neg.neg.imp
        (Formula.somePast phi.neg.neg)).allPast) :=
      Theorems.past_necessitation _ h_dne2_base
    have h_dne2_bx3 : DerivationTree FrameClass.Base [] (((Formula.somePast phi.neg.neg).neg.neg.imp
        (Formula.somePast phi.neg.neg)).allPast.imp
        ((Formula.snce (Formula.somePast phi.neg.neg).neg.neg Formula.top).imp
         (Formula.snce (Formula.somePast phi.neg.neg) Formula.top))) :=
      DerivationTree.axiom [] _
        (Axiom.right_mono_since
          (Formula.somePast phi.neg.neg).neg.neg
          (Formula.somePast phi.neg.neg) Formula.top) trivial
    have h_P_dne2 : DerivationTree FrameClass.Base [] ((Formula.somePast (Formula.somePast phi.neg.neg).neg.neg).imp
        (Formula.somePast (Formula.somePast phi.neg.neg))) :=
      DerivationTree.modus_ponens [] _ _ h_dne2_bx3 h_dne2_nec
    have h_PP_negneg : Formula.somePast (Formula.somePast phi.neg.neg) ∈ M :=
      SetMaximalConsistent.implication_property h_mcs (theorem_in_mcs h_mcs h_P_dne2) h_P_neg_H
    have h_dne3_base : DerivationTree FrameClass.Base [] (phi.neg.neg.imp phi) :=
      Theorems.Propositional.double_negation _
    have h_dne3_nec : DerivationTree FrameClass.Base [] ((phi.neg.neg.imp phi).allPast) :=
      Theorems.past_necessitation _ h_dne3_base
    have h_dne3_bx3 : DerivationTree FrameClass.Base [] ((phi.neg.neg.imp phi).allPast.imp
        ((Formula.snce phi.neg.neg Formula.top).imp (Formula.snce phi Formula.top))) :=
      DerivationTree.axiom [] _
        (Axiom.right_mono_since phi.neg.neg phi Formula.top) trivial
    have h_P_dne3 : DerivationTree FrameClass.Base [] ((Formula.somePast phi.neg.neg).imp (Formula.somePast phi)) :=
      DerivationTree.modus_ponens [] _ _ h_dne3_bx3 h_dne3_nec
    have h_lift_nec : DerivationTree FrameClass.Base [] (((Formula.somePast phi.neg.neg).imp (Formula.somePast phi)).allPast) :=
      Theorems.past_necessitation _ h_P_dne3
    have h_lift_bx3 : DerivationTree FrameClass.Base [] (((Formula.somePast phi.neg.neg).imp (Formula.somePast phi)).allPast.imp
        ((Formula.snce (Formula.somePast phi.neg.neg) Formula.top).imp
         (Formula.snce (Formula.somePast phi) Formula.top))) :=
      DerivationTree.axiom [] _
        (Axiom.right_mono_since
          (Formula.somePast phi.neg.neg) (Formula.somePast phi) Formula.top) trivial
    have h_PP_lift : DerivationTree FrameClass.Base [] ((Formula.somePast (Formula.somePast phi.neg.neg)).imp
        (Formula.somePast (Formula.somePast phi))) :=
      DerivationTree.modus_ponens [] _ _ h_lift_bx3 h_lift_nec
    have h_PP_phi : Formula.somePast (Formula.somePast phi) ∈ M :=
      SetMaximalConsistent.implication_property h_mcs (theorem_in_mcs h_mcs h_PP_lift) h_PP_negneg
    exact set_consistent_not_both h_mcs.1 (Formula.somePast (Formula.somePast phi))
      h_PP_phi h_neg_PP

theorem single_step_forcing_past
    (u v : Set (Formula Atom)) (h_mcs_u : SetMaximalConsistent (FrameClass.Base : FrameClass) u) (h_mcs_v : SetMaximalConsistent (FrameClass.Base : FrameClass) v)
    (phi : Formula Atom)
    (h_P : Formula.somePast phi ∈ v)
    (h_PP_not : Formula.somePast (Formula.somePast phi) ∉ v)
    (h_succ : Succ u v)
    (h_p_step : p_content v ⊆ u ∪ p_content u) :
    phi ∈ u := by
  have h_neg_PP : (Formula.somePast (Formula.somePast phi)).neg ∈ v := by
    cases SetMaximalConsistent.negation_complete h_mcs_v (Formula.somePast (Formula.somePast phi)) with
    | inl h_in => exact absurd h_in h_PP_not
    | inr h_neg => exact h_neg
  have h_HH_neg : Formula.allPast (Formula.allPast phi.neg) ∈ v :=
    neg_PP_implies_HH_neg_in_mcs v h_mcs_v phi h_neg_PP
  have h_H_neg_in_h : Formula.allPast phi.neg ∈ h_content v := h_HH_neg
  have h_H_neg_in_u : Formula.allPast phi.neg ∈ u :=
    Succ_implies_h_content_reverse u v h_mcs_u h_mcs_v h_succ h_H_neg_in_h
  have h_P_not_u : Formula.somePast phi ∉ u :=
    H_neg_implies_not_P u h_mcs_u phi h_H_neg_in_u
  have h_phi_in_p_content_v : phi ∈ p_content v := h_P
  have h_in_union := h_p_step h_phi_in_p_content_v
  cases h_in_union with
  | inl h_in_u => exact h_in_u
  | inr h_in_p_content_u =>
    exact absurd h_in_p_content_u h_P_not_u

/-! ## Until/Since Step Properties -/

-- Sorries from source (TOMBSTONE task 173)

theorem until_unfold_in_mcs (M : Set (Formula Atom)) (h_mcs : SetMaximalConsistent (FrameClass.Base : FrameClass) M)
    (φ ψ : Formula Atom) (h_U : Formula.untl ψ φ ∈ M) :
    Formula.untl (Formula.or ψ (Formula.and φ (Formula.untl ψ φ))) (Formula.bot : Formula Atom) ∈ M := by
  sorry

theorem since_unfold_in_mcs (M : Set (Formula Atom)) (h_mcs : SetMaximalConsistent (FrameClass.Base : FrameClass) M)
    (φ ψ : Formula Atom) (h_S : Formula.snce ψ φ ∈ M) :
    Formula.snce (Formula.or ψ (Formula.and φ (Formula.snce ψ φ))) (Formula.bot : Formula Atom) ∈ M := by
  sorry

theorem until_persists_through_succ (u v : Set (Formula Atom))
    (h_mcs_u : SetMaximalConsistent (FrameClass.Base : FrameClass) u) (h_mcs_v : SetMaximalConsistent (FrameClass.Base : FrameClass) v) (h_succ : Succ u v)
    (φ ψ : Formula Atom) (h_U : Formula.untl ψ φ ∈ u) (h_neg_psi : Formula.neg ψ ∈ u) :
    Formula.untl ψ φ ∈ v := by
  sorry

theorem or_until_in_mcs (M : Set (Formula Atom)) (h_mcs : SetMaximalConsistent (FrameClass.Base : FrameClass) M)
    (φ ψ : Formula Atom)
    (h : Formula.or ψ (Formula.and φ (Formula.untl ψ φ)) ∈ M) :
    Formula.untl ψ φ ∈ M := by
  sorry

theorem or_since_in_mcs (M : Set (Formula Atom)) (h_mcs : SetMaximalConsistent (FrameClass.Base : FrameClass) M)
    (φ ψ : Formula Atom)
    (h : Formula.or ψ (Formula.and φ (Formula.snce ψ φ)) ∈ M) :
    Formula.snce ψ φ ∈ M := by
  sorry

theorem g_content_subset_mcs (u : Set (Formula Atom)) (h_mcs : SetMaximalConsistent (FrameClass.Base : FrameClass) u) :
    g_content u ⊆ u := by
  sorry

theorem h_content_subset_mcs (u : Set (Formula Atom)) (h_mcs : SetMaximalConsistent (FrameClass.Base : FrameClass) u) :
    h_content u ⊆ u := by
  sorry

end Cslib.Logic.Bimodal.Metalogic.Bundle
