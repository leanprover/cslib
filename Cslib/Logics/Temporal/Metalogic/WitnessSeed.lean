/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Temporal.Metalogic.TemporalContent
public import Cslib.Logics.Temporal.Metalogic.GeneralizedNecessitation
public import Cslib.Logics.Temporal.Metalogic.PropositionalHelpers

/-!
# Witness Seed Definitions and Consistency

Temporal witness seed definitions and their consistency proofs.
Also contains the gContent/hContent duality theorems.

## References

* Ported from Cslib/Logics/Bimodal/Metalogic/Bundle/WitnessSeed.lean
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option maxHeartbeats 800000

@[expose] public section

namespace Cslib.Logic.Temporal.Metalogic

open Cslib.Logic.Temporal

attribute [local instance] Classical.propDecidable

variable {Atom : Type*}

/-! ## Duality Helpers -/

lemma someFuture_allFuture_neg_absurd {M : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent M) (psi : Formula Atom)
    (h_F : (𝐅psi) ∈ M)
    (h_G_neg : Formula.allFuture (Formula.neg psi) ∈ M) : False := by
  have h_bx3 : DerivationTree FrameClass.Base [] ((psi.imp psi.neg.neg).allFuture.imp
      ((Formula.untl psi Formula.top).imp (Formula.untl psi.neg.neg Formula.top))) :=
    DerivationTree.axiom [] _ (Axiom.right_mono_until psi psi.neg.neg Formula.top) trivial
  have h_impl := DerivationTree.modus_ponens [] _ _ h_bx3
    (DerivationTree.temporal_necessitation _ (dni psi))
  have h_sf_nn := temporal_implication_property h_mcs (theoremInMcs h_mcs h_impl) h_F
  exact mcs_not_mem_of_neg h_mcs h_G_neg h_sf_nn

lemma somePast_allPast_neg_absurd {M : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent M) (psi : Formula Atom)
    (h_P : (𝐏psi) ∈ M)
    (h_H_neg : Formula.allPast (Formula.neg psi) ∈ M) : False := by
  have h_bx3 : DerivationTree FrameClass.Base [] ((psi.imp psi.neg.neg).allPast.imp
      ((Formula.snce psi Formula.top).imp (Formula.snce psi.neg.neg Formula.top))) :=
    DerivationTree.axiom [] _ (Axiom.right_mono_since psi psi.neg.neg Formula.top) trivial
  have h_impl := DerivationTree.modus_ponens [] _ _ h_bx3
    (pastNecessitation _ (dni psi))
  have h_sp_nn := temporal_implication_property h_mcs (theoremInMcs h_mcs h_impl) h_P
  exact mcs_not_mem_of_neg h_mcs h_H_neg h_sp_nn

/-! ## Shared helper for G(¬X) extraction from seed inconsistency -/

/-- From L ⊢ ⊥ where L ⊆ {X} ∪ gContent(M), extract G(¬X) ∈ M. -/
theorem extract_g_neg_from_seed {M : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent M)
    (X : Formula Atom)
    {L : List (Formula Atom)}
    (hL_sub : ∀ chi ∈ L, chi ∈ ({X} ∪ gContent M : Set (Formula Atom)))
    (d : DerivationTree FrameClass.Base L Formula.bot) :
    Formula.allFuture (Formula.neg X) ∈ M := by
  by_cases h_X_in : X ∈ L
  · -- Separate X from the rest
    have h_sub_reord : ∀ x, x ∈ L → x ∈ X :: L.filter (fun y => decide (y ≠ X)) := by
      intro x hx
      by_cases hxX : x = X
      · exact List.mem_cons.mpr (Or.inl hxX)
      · exact List.mem_cons.mpr (Or.inr (by simp [List.mem_filter, decide_eq_true_eq]; exact ⟨hx, hxX⟩))
    have d_reord := DerivationTree.weakening L _ Formula.bot d h_sub_reord
    have d_neg := deductionTheorem _ X Formula.bot d_reord
    have h_G_filt : ∀ chi ∈ L.filter (fun y => decide (y ≠ X)), (𝐆chi) ∈ M := by
      intro chi h_mem
      have h_and := List.mem_filter.mp h_mem
      have h_ne : chi ≠ X := by simp only [decide_eq_true_eq] at h_and; exact h_and.2
      have h_in := hL_sub chi h_and.1
      simp only [Set.mem_union, Set.mem_singleton_iff] at h_in
      rcases h_in with rfl | h_gc
      · exact absurd rfl h_ne
      · exact h_gc
    have d_G_neg := generalizedTemporalK _ (Formula.neg X) d_neg
    have h_ctx : ∀ f ∈ Context.map Formula.allFuture (L.filter (fun y => decide (y ≠ X))), f ∈ M := by
      intro f hf; rw [Context.mem_map_iff] at hf
      obtain ⟨chi, hc, he⟩ := hf; rw [← he]; exact h_G_filt chi hc
    exact temporal_closed_under_derivation h_mcs h_ctx ⟨d_G_neg⟩
  · -- X ∉ L, all of L ⊆ gContent M
    have h_G_all : ∀ chi ∈ L, (𝐆chi) ∈ M := by
      intro chi h_mem
      have h_in := hL_sub chi h_mem
      simp only [Set.mem_union, Set.mem_singleton_iff] at h_in
      rcases h_in with rfl | h_gc
      · exact absurd h_mem h_X_in
      · exact h_gc
    have d_G_bot := generalizedTemporalK L Formula.bot d
    have h_G_L : ∀ f ∈ Context.map Formula.allFuture L, f ∈ M := by
      intro f hf; rw [Context.mem_map_iff] at hf
      obtain ⟨chi, hc, he⟩ := hf; rw [← he]; exact h_G_all chi hc
    have h_G_bot := temporal_closed_under_derivation h_mcs h_G_L ⟨d_G_bot⟩
    have h_ef := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.imp_s (Formula.bot : Formula Atom) X) trivial
    have h_G_ef := DerivationTree.temporal_necessitation _ h_ef
    have h_K := tempKDistDerived (Formula.bot : Formula Atom) (Formula.neg X)
    have h_G_imp := DerivationTree.modus_ponens [] _ _ h_K h_G_ef
    exact temporal_implication_property h_mcs (theoremInMcs h_mcs h_G_imp) h_G_bot

/-- From L ⊢ ⊥ where L ⊆ {X} ∪ hContent(M), extract H(¬X) ∈ M. -/
theorem extract_h_neg_from_seed {M : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent M)
    (X : Formula Atom)
    {L : List (Formula Atom)}
    (hL_sub : ∀ chi ∈ L, chi ∈ ({X} ∪ hContent M : Set (Formula Atom)))
    (d : DerivationTree FrameClass.Base L Formula.bot) :
    Formula.allPast (Formula.neg X) ∈ M := by
  by_cases h_X_in : X ∈ L
  · have h_sub_reord : ∀ x, x ∈ L → x ∈ X :: L.filter (fun y => decide (y ≠ X)) := by
      intro x hx
      by_cases hxX : x = X
      · exact List.mem_cons.mpr (Or.inl hxX)
      · exact List.mem_cons.mpr (Or.inr (by simp [List.mem_filter, decide_eq_true_eq]; exact ⟨hx, hxX⟩))
    have d_reord := DerivationTree.weakening L _ Formula.bot d h_sub_reord
    have d_neg := deductionTheorem _ X Formula.bot d_reord
    have h_H_filt : ∀ chi ∈ L.filter (fun y => decide (y ≠ X)), (𝐇chi) ∈ M := by
      intro chi h_mem
      have h_and := List.mem_filter.mp h_mem
      have h_ne : chi ≠ X := by simp only [decide_eq_true_eq] at h_and; exact h_and.2
      have h_in := hL_sub chi h_and.1
      simp only [Set.mem_union, Set.mem_singleton_iff] at h_in
      rcases h_in with rfl | h_hc
      · exact absurd rfl h_ne
      · exact h_hc
    have d_H_neg := generalizedPastK _ (Formula.neg X) d_neg
    have h_ctx : ∀ f ∈ Context.map Formula.allPast (L.filter (fun y => decide (y ≠ X))), f ∈ M := by
      intro f hf; rw [Context.mem_map_iff] at hf
      obtain ⟨chi, hc, he⟩ := hf; rw [← he]; exact h_H_filt chi hc
    exact temporal_closed_under_derivation h_mcs h_ctx ⟨d_H_neg⟩
  · have h_H_all : ∀ chi ∈ L, (𝐇chi) ∈ M := by
      intro chi h_mem
      have h_in := hL_sub chi h_mem
      simp only [Set.mem_union, Set.mem_singleton_iff] at h_in
      rcases h_in with rfl | h_hc
      · exact absurd h_mem h_X_in
      · exact h_hc
    have d_H_bot := generalizedPastK L Formula.bot d
    have h_H_L : ∀ f ∈ Context.map Formula.allPast L, f ∈ M := by
      intro f hf; rw [Context.mem_map_iff] at hf
      obtain ⟨chi, hc, he⟩ := hf; rw [← he]; exact h_H_all chi hc
    have h_H_bot := temporal_closed_under_derivation h_mcs h_H_L ⟨d_H_bot⟩
    have h_ef := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.imp_s (Formula.bot : Formula Atom) X) trivial
    have h_H_ef := pastNecessitation _ h_ef
    have h_K := pastKDist (Formula.bot : Formula Atom) (Formula.neg X)
    have h_H_imp := DerivationTree.modus_ponens [] _ _ h_K h_H_ef
    exact temporal_implication_property h_mcs (theoremInMcs h_mcs h_H_imp) h_H_bot

/-! ## Forward Temporal Witness Seed -/

def forwardTemporalWitnessSeed (M : Set (Formula Atom)) (psi : Formula Atom) : Set (Formula Atom) :=
  {psi} ∪ gContent M

theorem forward_temporal_witness_seed_consistent (M : Set (Formula Atom))
    (h_mcs : Temporal.SetMaximalConsistent M)
    (psi : Formula Atom) (h_F : (𝐅psi) ∈ M) :
    Temporal.SetConsistent (forwardTemporalWitnessSeed M psi) := by
  intro L hL_sub ⟨d⟩
  exact someFuture_allFuture_neg_absurd h_mcs psi h_F
    (extract_g_neg_from_seed h_mcs psi hL_sub d)

/-! ## Past Temporal Witness Seed -/

def pastTemporalWitnessSeed (M : Set (Formula Atom)) (psi : Formula Atom) : Set (Formula Atom) :=
  {psi} ∪ hContent M

theorem past_temporal_witness_seed_consistent (M : Set (Formula Atom))
    (h_mcs : Temporal.SetMaximalConsistent M)
    (psi : Formula Atom) (h_P : (𝐏psi) ∈ M) :
    Temporal.SetConsistent (pastTemporalWitnessSeed M psi) := by
  intro L hL_sub ⟨d⟩
  exact somePast_allPast_neg_absurd h_mcs psi h_P
    (extract_h_neg_from_seed h_mcs psi hL_sub d)

/-! ## Until/Since Witness Seeds -/

theorem until_witness_seed_consistent (M : Set (Formula Atom))
    (h_mcs : Temporal.SetMaximalConsistent M)
    (φ ψ : Formula Atom) (h_U : (ψ U φ) ∈ M) :
    Temporal.SetConsistent (forwardTemporalWitnessSeed M ψ) := by
  intro L hL_sub ⟨d⟩
  have h_G_neg := extract_g_neg_from_seed h_mcs ψ hL_sub d
  have h_ax : DerivationTree FrameClass.Base [] ((Formula.untl ψ φ).imp (Formula.someFuture ψ)) :=
    DerivationTree.axiom [] _ (Axiom.until_F φ ψ) trivial
  have h_F := temporal_implication_property h_mcs (theoremInMcs h_mcs h_ax) h_U
  exact someFuture_allFuture_neg_absurd h_mcs ψ h_F h_G_neg

theorem since_witness_seed_consistent (M : Set (Formula Atom))
    (h_mcs : Temporal.SetMaximalConsistent M)
    (φ ψ : Formula Atom) (h_S : (ψ S φ) ∈ M) :
    Temporal.SetConsistent (pastTemporalWitnessSeed M ψ) := by
  intro L hL_sub ⟨d⟩
  have h_H_neg := extract_h_neg_from_seed h_mcs ψ hL_sub d
  have h_ax : DerivationTree FrameClass.Base [] ((Formula.snce ψ φ).imp (Formula.somePast ψ)) :=
    DerivationTree.axiom [] _ (Axiom.since_P φ ψ) trivial
  have h_P := temporal_implication_property h_mcs (theoremInMcs h_mcs h_ax) h_S
  exact somePast_allPast_neg_absurd h_mcs ψ h_P h_H_neg

/-! ## gContent/hContent Duality -/

theorem g_content_subset_implies_h_content_reverse
    (M M' : Set (Formula Atom))
    (h_mcs : Temporal.SetMaximalConsistent M) (h_mcs' : Temporal.SetMaximalConsistent M')
    (h_GC : gContent M ⊆ M') :
    hContent M' ⊆ M := by
  intro phi h_H_phi_in_M'
  by_contra h_not_phi
  have h_neg_phi := mcs_neg_of_not_mem h_mcs h_not_phi
  have h_ta : DerivationTree FrameClass.Base [] ((Formula.neg phi).imp (Formula.allFuture (Formula.neg phi).somePast)) :=
    DerivationTree.axiom [] _ (Axiom.connect_future (Formula.neg phi)) trivial
  have h_G_P_neg := temporal_implication_property h_mcs (theoremInMcs h_mcs h_ta) h_neg_phi
  have h_P_neg_M' : (𝐏(¬phi)) ∈ M' := h_GC h_G_P_neg
  have h_H_dni := pastNecessitation _ (dni phi)
  have h_pk := pastKDist phi phi.neg.neg
  have h_H_imp := DerivationTree.modus_ponens [] _ _ h_pk h_H_dni
  have h_H_nn := temporal_implication_property h_mcs' (theoremInMcs h_mcs' h_H_imp) h_H_phi_in_M'
  exact somePast_allPast_neg_absurd h_mcs' (Formula.neg phi) h_P_neg_M' h_H_nn

theorem h_content_subset_implies_g_content_reverse
    (M M' : Set (Formula Atom))
    (h_mcs : Temporal.SetMaximalConsistent M) (h_mcs' : Temporal.SetMaximalConsistent M')
    (h_HC : hContent M ⊆ M') :
    gContent M' ⊆ M := by
  intro phi h_G_phi_in_M'
  by_contra h_not_phi
  have h_neg_phi := mcs_neg_of_not_mem h_mcs h_not_phi
  have h_pta : DerivationTree FrameClass.Base [] ((Formula.neg phi).imp (Formula.neg phi).someFuture.allPast) :=
    DerivationTree.axiom [] _ (Axiom.connect_past (Formula.neg phi)) trivial
  have h_H_F_neg := temporal_implication_property h_mcs (theoremInMcs h_mcs h_pta) h_neg_phi
  have h_F_neg_M' : (𝐅(¬phi)) ∈ M' := h_HC h_H_F_neg
  have h_G_dni := DerivationTree.temporal_necessitation _ (dni phi)
  have h_fk := tempKDistDerived phi phi.neg.neg
  have h_G_imp := DerivationTree.modus_ponens [] _ _ h_fk h_G_dni
  have h_G_nn := temporal_implication_property h_mcs' (theoremInMcs h_mcs' h_G_imp) h_G_phi_in_M'
  exact someFuture_allFuture_neg_absurd h_mcs' (Formula.neg phi) h_F_neg_M' h_G_nn

end Cslib.Logic.Temporal.Metalogic
