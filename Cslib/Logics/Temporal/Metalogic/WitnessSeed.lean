/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/

import Cslib.Logics.Temporal.Metalogic.TemporalContent
import Cslib.Logics.Temporal.Metalogic.GeneralizedNecessitation
import Cslib.Logics.Temporal.Metalogic.PropositionalHelpers

/-!
# Witness Seed Definitions and Consistency

Temporal witness seed definitions and their consistency proofs.
Also contains the g_content/h_content duality theorems.

## References

* Ported from Cslib/Logics/Bimodal/Metalogic/Bundle/WitnessSeed.lean
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option maxHeartbeats 800000

namespace Cslib.Logic.Temporal.Metalogic

open Cslib.Logic.Temporal

attribute [local instance] Classical.propDecidable

variable {Atom : Type*}

private noncomputable def theorem_in_mcs {M : Set (Formula Atom)} {phi : Formula Atom}
    (h_mcs : Temporal.SetMaximalConsistent M)
    (h_deriv : DerivationTree FrameClass.Base [] phi) : phi ∈ M :=
  temporal_closed_under_derivation h_mcs (L := []) (fun _ h => by simp at h) ⟨h_deriv⟩

/-! ## Duality Helpers -/

lemma some_future_all_future_neg_absurd {M : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent M) (psi : Formula Atom)
    (h_F : Formula.some_future psi ∈ M)
    (h_G_neg : Formula.all_future (Formula.neg psi) ∈ M) : False := by
  have h_bx3 : DerivationTree FrameClass.Base [] ((psi.imp psi.neg.neg).all_future.imp
      ((Formula.untl psi Formula.top).imp (Formula.untl psi.neg.neg Formula.top))) :=
    DerivationTree.axiom [] _ (Axiom.right_mono_until psi psi.neg.neg Formula.top) trivial
  have h_impl := DerivationTree.modus_ponens [] _ _ h_bx3
    (DerivationTree.temporal_necessitation _ (dni psi))
  have h_sf_nn := temporal_implication_property h_mcs (theorem_in_mcs h_mcs h_impl) h_F
  exact mcs_not_mem_of_neg h_mcs h_G_neg h_sf_nn

lemma some_past_all_past_neg_absurd {M : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent M) (psi : Formula Atom)
    (h_P : Formula.some_past psi ∈ M)
    (h_H_neg : Formula.all_past (Formula.neg psi) ∈ M) : False := by
  have h_bx3 : DerivationTree FrameClass.Base [] ((psi.imp psi.neg.neg).all_past.imp
      ((Formula.snce psi Formula.top).imp (Formula.snce psi.neg.neg Formula.top))) :=
    DerivationTree.axiom [] _ (Axiom.right_mono_since psi psi.neg.neg Formula.top) trivial
  have h_impl := DerivationTree.modus_ponens [] _ _ h_bx3
    (past_necessitation _ (dni psi))
  have h_sp_nn := temporal_implication_property h_mcs (theorem_in_mcs h_mcs h_impl) h_P
  exact mcs_not_mem_of_neg h_mcs h_H_neg h_sp_nn

/-! ## Shared helper for G(¬X) extraction from seed inconsistency -/

/-- From L ⊢ ⊥ where L ⊆ {X} ∪ g_content(M), extract G(¬X) ∈ M. -/
private theorem extract_g_neg_from_seed {M : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent M)
    (X : Formula Atom)
    {L : List (Formula Atom)}
    (hL_sub : ∀ chi ∈ L, chi ∈ ({X} ∪ g_content M : Set (Formula Atom)))
    (d : DerivationTree FrameClass.Base L Formula.bot) :
    Formula.all_future (Formula.neg X) ∈ M := by
  by_cases h_X_in : X ∈ L
  · -- Separate X from the rest
    have h_sub_reord : ∀ x, x ∈ L → x ∈ X :: L.filter (fun y => decide (y ≠ X)) := by
      intro x hx
      by_cases hxX : x = X
      · exact List.mem_cons.mpr (Or.inl hxX)
      · exact List.mem_cons.mpr (Or.inr (by simp [List.mem_filter, decide_eq_true_eq]; exact ⟨hx, hxX⟩))
    have d_reord := DerivationTree.weakening L _ Formula.bot d h_sub_reord
    have d_neg := deduction_theorem _ X Formula.bot d_reord
    have h_G_filt : ∀ chi ∈ L.filter (fun y => decide (y ≠ X)), Formula.all_future chi ∈ M := by
      intro chi h_mem
      have h_and := List.mem_filter.mp h_mem
      have h_ne : chi ≠ X := by simp only [decide_eq_true_eq] at h_and; exact h_and.2
      have h_in := hL_sub chi h_and.1
      simp only [Set.mem_union, Set.mem_singleton_iff] at h_in
      rcases h_in with rfl | h_gc
      · exact absurd rfl h_ne
      · exact h_gc
    have d_G_neg := generalized_temporal_k _ (Formula.neg X) d_neg
    have h_ctx : ∀ f ∈ Context.map Formula.all_future (L.filter (fun y => decide (y ≠ X))), f ∈ M := by
      intro f hf; rw [Context.mem_map_iff] at hf
      obtain ⟨chi, hc, he⟩ := hf; rw [← he]; exact h_G_filt chi hc
    exact temporal_closed_under_derivation h_mcs h_ctx ⟨d_G_neg⟩
  · -- X ∉ L, all of L ⊆ g_content M
    have h_G_all : ∀ chi ∈ L, Formula.all_future chi ∈ M := by
      intro chi h_mem
      have h_in := hL_sub chi h_mem
      simp only [Set.mem_union, Set.mem_singleton_iff] at h_in
      rcases h_in with rfl | h_gc
      · exact absurd h_mem h_X_in
      · exact h_gc
    have d_G_bot := generalized_temporal_k L Formula.bot d
    have h_G_L : ∀ f ∈ Context.map Formula.all_future L, f ∈ M := by
      intro f hf; rw [Context.mem_map_iff] at hf
      obtain ⟨chi, hc, he⟩ := hf; rw [← he]; exact h_G_all chi hc
    have h_G_bot := temporal_closed_under_derivation h_mcs h_G_L ⟨d_G_bot⟩
    have h_ef := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.imp_s (Formula.bot : Formula Atom) X) trivial
    have h_G_ef := DerivationTree.temporal_necessitation _ h_ef
    have h_K := temp_k_dist_derived (Formula.bot : Formula Atom) (Formula.neg X)
    have h_G_imp := DerivationTree.modus_ponens [] _ _ h_K h_G_ef
    exact temporal_implication_property h_mcs (theorem_in_mcs h_mcs h_G_imp) h_G_bot

/-- From L ⊢ ⊥ where L ⊆ {X} ∪ h_content(M), extract H(¬X) ∈ M. -/
private theorem extract_h_neg_from_seed {M : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent M)
    (X : Formula Atom)
    {L : List (Formula Atom)}
    (hL_sub : ∀ chi ∈ L, chi ∈ ({X} ∪ h_content M : Set (Formula Atom)))
    (d : DerivationTree FrameClass.Base L Formula.bot) :
    Formula.all_past (Formula.neg X) ∈ M := by
  by_cases h_X_in : X ∈ L
  · have h_sub_reord : ∀ x, x ∈ L → x ∈ X :: L.filter (fun y => decide (y ≠ X)) := by
      intro x hx
      by_cases hxX : x = X
      · exact List.mem_cons.mpr (Or.inl hxX)
      · exact List.mem_cons.mpr (Or.inr (by simp [List.mem_filter, decide_eq_true_eq]; exact ⟨hx, hxX⟩))
    have d_reord := DerivationTree.weakening L _ Formula.bot d h_sub_reord
    have d_neg := deduction_theorem _ X Formula.bot d_reord
    have h_H_filt : ∀ chi ∈ L.filter (fun y => decide (y ≠ X)), Formula.all_past chi ∈ M := by
      intro chi h_mem
      have h_and := List.mem_filter.mp h_mem
      have h_ne : chi ≠ X := by simp only [decide_eq_true_eq] at h_and; exact h_and.2
      have h_in := hL_sub chi h_and.1
      simp only [Set.mem_union, Set.mem_singleton_iff] at h_in
      rcases h_in with rfl | h_hc
      · exact absurd rfl h_ne
      · exact h_hc
    have d_H_neg := generalized_past_k _ (Formula.neg X) d_neg
    have h_ctx : ∀ f ∈ Context.map Formula.all_past (L.filter (fun y => decide (y ≠ X))), f ∈ M := by
      intro f hf; rw [Context.mem_map_iff] at hf
      obtain ⟨chi, hc, he⟩ := hf; rw [← he]; exact h_H_filt chi hc
    exact temporal_closed_under_derivation h_mcs h_ctx ⟨d_H_neg⟩
  · have h_H_all : ∀ chi ∈ L, Formula.all_past chi ∈ M := by
      intro chi h_mem
      have h_in := hL_sub chi h_mem
      simp only [Set.mem_union, Set.mem_singleton_iff] at h_in
      rcases h_in with rfl | h_hc
      · exact absurd h_mem h_X_in
      · exact h_hc
    have d_H_bot := generalized_past_k L Formula.bot d
    have h_H_L : ∀ f ∈ Context.map Formula.all_past L, f ∈ M := by
      intro f hf; rw [Context.mem_map_iff] at hf
      obtain ⟨chi, hc, he⟩ := hf; rw [← he]; exact h_H_all chi hc
    have h_H_bot := temporal_closed_under_derivation h_mcs h_H_L ⟨d_H_bot⟩
    have h_ef := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.imp_s (Formula.bot : Formula Atom) X) trivial
    have h_H_ef := past_necessitation _ h_ef
    have h_K := past_k_dist (Formula.bot : Formula Atom) (Formula.neg X)
    have h_H_imp := DerivationTree.modus_ponens [] _ _ h_K h_H_ef
    exact temporal_implication_property h_mcs (theorem_in_mcs h_mcs h_H_imp) h_H_bot

/-! ## Forward Temporal Witness Seed -/

def forward_temporal_witness_seed (M : Set (Formula Atom)) (psi : Formula Atom) : Set (Formula Atom) :=
  {psi} ∪ g_content M

theorem forward_temporal_witness_seed_consistent (M : Set (Formula Atom))
    (h_mcs : Temporal.SetMaximalConsistent M)
    (psi : Formula Atom) (h_F : Formula.some_future psi ∈ M) :
    Temporal.SetConsistent (forward_temporal_witness_seed M psi) := by
  intro L hL_sub ⟨d⟩
  exact some_future_all_future_neg_absurd h_mcs psi h_F
    (extract_g_neg_from_seed h_mcs psi hL_sub d)

/-! ## Past Temporal Witness Seed -/

def past_temporal_witness_seed (M : Set (Formula Atom)) (psi : Formula Atom) : Set (Formula Atom) :=
  {psi} ∪ h_content M

theorem past_temporal_witness_seed_consistent (M : Set (Formula Atom))
    (h_mcs : Temporal.SetMaximalConsistent M)
    (psi : Formula Atom) (h_P : Formula.some_past psi ∈ M) :
    Temporal.SetConsistent (past_temporal_witness_seed M psi) := by
  intro L hL_sub ⟨d⟩
  exact some_past_all_past_neg_absurd h_mcs psi h_P
    (extract_h_neg_from_seed h_mcs psi hL_sub d)

/-! ## Until/Since Witness Seeds -/

theorem until_witness_seed_consistent (M : Set (Formula Atom))
    (h_mcs : Temporal.SetMaximalConsistent M)
    (φ ψ : Formula Atom) (h_U : Formula.untl ψ φ ∈ M) :
    Temporal.SetConsistent (forward_temporal_witness_seed M ψ) := by
  intro L hL_sub ⟨d⟩
  have h_G_neg := extract_g_neg_from_seed h_mcs ψ hL_sub d
  have h_ax : DerivationTree FrameClass.Base [] ((Formula.untl ψ φ).imp (Formula.some_future ψ)) :=
    DerivationTree.axiom [] _ (Axiom.until_F φ ψ) trivial
  have h_F := temporal_implication_property h_mcs (theorem_in_mcs h_mcs h_ax) h_U
  exact some_future_all_future_neg_absurd h_mcs ψ h_F h_G_neg

theorem since_witness_seed_consistent (M : Set (Formula Atom))
    (h_mcs : Temporal.SetMaximalConsistent M)
    (φ ψ : Formula Atom) (h_S : Formula.snce ψ φ ∈ M) :
    Temporal.SetConsistent (past_temporal_witness_seed M ψ) := by
  intro L hL_sub ⟨d⟩
  have h_H_neg := extract_h_neg_from_seed h_mcs ψ hL_sub d
  have h_ax : DerivationTree FrameClass.Base [] ((Formula.snce ψ φ).imp (Formula.some_past ψ)) :=
    DerivationTree.axiom [] _ (Axiom.since_P φ ψ) trivial
  have h_P := temporal_implication_property h_mcs (theorem_in_mcs h_mcs h_ax) h_S
  exact some_past_all_past_neg_absurd h_mcs ψ h_P h_H_neg

/-! ## g_content/h_content Duality -/

theorem g_content_subset_implies_h_content_reverse
    (M M' : Set (Formula Atom))
    (h_mcs : Temporal.SetMaximalConsistent M) (h_mcs' : Temporal.SetMaximalConsistent M')
    (h_GC : g_content M ⊆ M') :
    h_content M' ⊆ M := by
  intro phi h_H_phi_in_M'
  by_contra h_not_phi
  have h_neg_phi := mcs_neg_of_not_mem h_mcs h_not_phi
  have h_ta : DerivationTree FrameClass.Base [] ((Formula.neg phi).imp (Formula.all_future (Formula.neg phi).some_past)) :=
    DerivationTree.axiom [] _ (Axiom.connect_future (Formula.neg phi)) trivial
  have h_G_P_neg := temporal_implication_property h_mcs (theorem_in_mcs h_mcs h_ta) h_neg_phi
  have h_P_neg_M' : (Formula.neg phi).some_past ∈ M' := h_GC h_G_P_neg
  have h_H_dni := past_necessitation _ (dni phi)
  have h_pk := past_k_dist phi phi.neg.neg
  have h_H_imp := DerivationTree.modus_ponens [] _ _ h_pk h_H_dni
  have h_H_nn := temporal_implication_property h_mcs' (theorem_in_mcs h_mcs' h_H_imp) h_H_phi_in_M'
  exact some_past_all_past_neg_absurd h_mcs' (Formula.neg phi) h_P_neg_M' h_H_nn

theorem h_content_subset_implies_g_content_reverse
    (M M' : Set (Formula Atom))
    (h_mcs : Temporal.SetMaximalConsistent M) (h_mcs' : Temporal.SetMaximalConsistent M')
    (h_HC : h_content M ⊆ M') :
    g_content M' ⊆ M := by
  intro phi h_G_phi_in_M'
  by_contra h_not_phi
  have h_neg_phi := mcs_neg_of_not_mem h_mcs h_not_phi
  have h_pta : DerivationTree FrameClass.Base [] ((Formula.neg phi).imp (Formula.neg phi).some_future.all_past) :=
    DerivationTree.axiom [] _ (Axiom.connect_past (Formula.neg phi)) trivial
  have h_H_F_neg := temporal_implication_property h_mcs (theorem_in_mcs h_mcs h_pta) h_neg_phi
  have h_F_neg_M' : (Formula.neg phi).some_future ∈ M' := h_HC h_H_F_neg
  have h_G_dni := DerivationTree.temporal_necessitation _ (dni phi)
  have h_fk := temp_k_dist_derived phi phi.neg.neg
  have h_G_imp := DerivationTree.modus_ponens [] _ _ h_fk h_G_dni
  have h_G_nn := temporal_implication_property h_mcs' (theorem_in_mcs h_mcs' h_G_imp) h_G_phi_in_M'
  exact some_future_all_future_neg_absurd h_mcs' (Formula.neg phi) h_F_neg_M' h_G_nn

end Cslib.Logic.Temporal.Metalogic
