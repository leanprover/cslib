/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/

import Cslib.Logics.Bimodal.Metalogic.Bundle.TemporalContent
import Cslib.Logics.Bimodal.Metalogic.Core.MaximalConsistent
import Cslib.Logics.Bimodal.Metalogic.Core.MCSProperties
import Cslib.Logics.Bimodal.Syntax.Formula
import Cslib.Logics.Bimodal.Theorems.GeneralizedNecessitation
import Cslib.Logics.Bimodal.Theorems.Combinators
import Cslib.Logics.Bimodal.Theorems.Perpetuity.Principles
import Cslib.Logics.Bimodal.Theorems.TemporalDerived

/-!
# Witness Seed Definitions and Consistency

This module contains the temporal witness seed definitions and their consistency
proofs, used by CanonicalFrame.lean for temporal witness construction.

Also contains the g_content/h_content duality theorems (g_content ⊆ implies h_content
reverse, and vice versa).

## Key Definitions

- `forward_temporal_witness_seed M psi`: `{psi} ∪ g_content(M)`
- `past_temporal_witness_seed M psi`: `{psi} ∪ h_content(M)`

## Key Theorems

- `forward_temporal_witness_seed_consistent`: If F(psi) ∈ MCS M, then the forward seed is consistent
- `past_temporal_witness_seed_consistent`: If P(psi) ∈ MCS M, then the past seed is consistent
- `g_content_subset_implies_h_content_reverse`: g_content(M) ⊆ M' implies h_content(M') ⊆ M
- `h_content_subset_implies_g_content_reverse`: h_content(M) ⊆ M' implies g_content(M') ⊆ M

## References

* Ported from BimodalLogic/Theories/Bimodal/Metalogic/Bundle/WitnessSeed.lean
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Cslib.Logic.Bimodal.Metalogic.Bundle

open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Metalogic.Core

attribute [local instance] Classical.propDecidable

variable {Atom : Type*}

/-- Helper: theorems are in any MCS (fc-parameterized version). -/
private noncomputable def theorem_in_mcs_fc {fc : FrameClass} {M : Set (Formula Atom)} {phi : Formula Atom}
    (h_mcs : SetMaximalConsistent fc M)
    (h_deriv : DerivationTree fc [] phi) : phi ∈ M :=
  SetMaximalConsistent.closed_under_derivation h_mcs [] (fun _ h => by simp at h) h_deriv

/-! ## Duality Helpers

Since `some_future`/`some_past` are no longer definitionally `neg(all_future/all_past(neg _))`,
we need helpers that derive contradictions between `some_future psi ∈ M` and
`all_future (neg psi) ∈ M` in an MCS. -/

/-- In an MCS, `some_future psi ∈ M` and `all_future (neg psi) ∈ M` is contradictory. -/
lemma some_future_all_future_neg_absurd {fc : FrameClass} {M : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc M) (psi : Formula Atom)
    (h_F : Formula.some_future psi ∈ M)
    (h_G_neg : Formula.all_future (Formula.neg psi) ∈ M) : False := by
  have h_dni : DerivationTree fc [] (psi.imp psi.neg.neg) := Theorems.Combinators.dni psi
  have h_G_dni : DerivationTree fc [] ((psi.imp psi.neg.neg).all_future) :=
    DerivationTree.temporal_necessitation _ h_dni
  have h_bx3 : DerivationTree fc [] ((psi.imp psi.neg.neg).all_future.imp
      ((Formula.untl psi Formula.top).imp (Formula.untl psi.neg.neg Formula.top))) :=
    DerivationTree.axiom [] _ (Axiom.right_mono_until psi psi.neg.neg Formula.top) (FrameClass.base_le fc)
  have h_impl : DerivationTree fc [] ((Formula.some_future psi).imp (Formula.some_future psi.neg.neg)) :=
    DerivationTree.modus_ponens [] _ _ h_bx3 h_G_dni
  have h_sf_nn : Formula.some_future psi.neg.neg ∈ M :=
    SetMaximalConsistent.implication_property h_mcs
      (theorem_in_mcs_fc h_mcs h_impl) h_F
  exact set_consistent_not_both h_mcs.1 (Formula.some_future psi.neg.neg) h_sf_nn h_G_neg

/-- In an MCS, `some_past psi ∈ M` and `all_past (neg psi) ∈ M` is contradictory. -/
lemma some_past_all_past_neg_absurd {fc : FrameClass} {M : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc M) (psi : Formula Atom)
    (h_P : Formula.some_past psi ∈ M)
    (h_H_neg : Formula.all_past (Formula.neg psi) ∈ M) : False := by
  have h_dni : DerivationTree fc [] (psi.imp psi.neg.neg) := Theorems.Combinators.dni psi
  have h_H_dni : DerivationTree fc [] ((psi.imp psi.neg.neg).all_past) :=
    Theorems.past_necessitation _ h_dni
  have h_bx3 : DerivationTree fc [] ((psi.imp psi.neg.neg).all_past.imp
      ((Formula.snce psi Formula.top).imp (Formula.snce psi.neg.neg Formula.top))) :=
    DerivationTree.axiom [] _ (Axiom.right_mono_since psi psi.neg.neg Formula.top) (FrameClass.base_le fc)
  have h_impl : DerivationTree fc [] ((Formula.some_past psi).imp (Formula.some_past psi.neg.neg)) :=
    DerivationTree.modus_ponens [] _ _ h_bx3 h_H_dni
  have h_sp_nn : Formula.some_past psi.neg.neg ∈ M :=
    SetMaximalConsistent.implication_property h_mcs
      (theorem_in_mcs_fc h_mcs h_impl) h_P
  exact set_consistent_not_both h_mcs.1 (Formula.some_past psi.neg.neg) h_sp_nn h_H_neg

/-! ## Duality Conversions

These lemmas convert between `¬F(φ)` and `G(¬φ)` (and their past duals) in an MCS. -/

/-- In an MCS, `¬F(φ) ∈ M` implies `G(¬φ) ∈ M`. -/
lemma neg_some_future_to_all_future_neg {fc : FrameClass} {M : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc M) (phi : Formula Atom)
    (h_neg_F : Formula.neg (Formula.some_future phi) ∈ M) :
    Formula.all_future (Formula.neg phi) ∈ M := by
  -- Build derivation chain at Base level, then lift to fc
  have h_dne : DerivationTree FrameClass.Base [] (phi.neg.neg.imp phi) := Theorems.Propositional.double_negation _
  have h_nec : DerivationTree FrameClass.Base [] ((phi.neg.neg.imp phi).all_future) :=
    DerivationTree.temporal_necessitation _ h_dne
  have h_bx3 : DerivationTree FrameClass.Base [] ((phi.neg.neg.imp phi).all_future.imp
      ((Formula.untl phi.neg.neg Formula.top).imp (Formula.untl phi Formula.top))) :=
    DerivationTree.axiom [] _ (Axiom.right_mono_until phi.neg.neg phi Formula.top) trivial
  have h_F_mono : DerivationTree FrameClass.Base [] ((Formula.some_future phi.neg.neg).imp (Formula.some_future phi)) :=
    DerivationTree.modus_ponens [] _ _ h_bx3 h_nec
  have h_contra : DerivationTree FrameClass.Base [] ((Formula.some_future phi).neg.imp (Formula.some_future phi.neg.neg).neg) :=
    Theorems.Propositional.contraposition h_F_mono
  exact SetMaximalConsistent.implication_property h_mcs
    (theorem_in_mcs_fc h_mcs (h_contra.lift (FrameClass.base_le fc))) h_neg_F

/-- In an MCS, `¬P(φ) ∈ M` implies `H(¬φ) ∈ M`. -/
lemma neg_some_past_to_all_past_neg {fc : FrameClass} {M : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc M) (phi : Formula Atom)
    (h_neg_P : Formula.neg (Formula.some_past phi) ∈ M) :
    Formula.all_past (Formula.neg phi) ∈ M := by
  -- Build derivation chain at Base level, then lift to fc
  have h_dne : DerivationTree FrameClass.Base [] (phi.neg.neg.imp phi) := Theorems.Propositional.double_negation _
  have h_nec : DerivationTree FrameClass.Base [] ((phi.neg.neg.imp phi).all_past) :=
    Theorems.past_necessitation _ h_dne
  have h_bx3 : DerivationTree FrameClass.Base [] ((phi.neg.neg.imp phi).all_past.imp
      ((Formula.snce phi.neg.neg Formula.top).imp (Formula.snce phi Formula.top))) :=
    DerivationTree.axiom [] _ (Axiom.right_mono_since phi.neg.neg phi Formula.top) trivial
  have h_P_mono : DerivationTree FrameClass.Base [] ((Formula.some_past phi.neg.neg).imp (Formula.some_past phi)) :=
    DerivationTree.modus_ponens [] _ _ h_bx3 h_nec
  have h_contra : DerivationTree FrameClass.Base [] ((Formula.some_past phi).neg.imp (Formula.some_past phi.neg.neg).neg) :=
    Theorems.Propositional.contraposition h_P_mono
  exact SetMaximalConsistent.implication_property h_mcs
    (theorem_in_mcs_fc h_mcs (h_contra.lift (FrameClass.base_le fc))) h_neg_P

/-!
## Forward Temporal Witness Seed
-/

/-- Forward witness seed: `{psi} ∪ g_content(M)`. -/
def forward_temporal_witness_seed (M : Set (Formula Atom)) (psi : Formula Atom) : Set (Formula Atom) :=
  {psi} ∪ g_content M

/-- psi is in its own forward_temporal_witness_seed. -/
lemma psi_mem_forward_temporal_witness_seed (M : Set (Formula Atom)) (psi : Formula Atom) :
    psi ∈ forward_temporal_witness_seed M psi :=
  Set.mem_union_left _ (Set.mem_singleton psi)

/-- g_content is a subset of forward_temporal_witness_seed. -/
lemma g_content_subset_forward_temporal_witness_seed (M : Set (Formula Atom)) (psi : Formula Atom) :
    g_content M ⊆ forward_temporal_witness_seed M psi :=
  Set.subset_union_right

/--
Forward temporal witness seed consistency: If F(psi) is in an MCS M, then
`{psi} ∪ g_content(M)` is consistent.
-/
theorem forward_temporal_witness_seed_consistent {fc : FrameClass} (M : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc M)
    (psi : Formula Atom) (h_F : Formula.some_future psi ∈ M) :
    SetConsistent fc (forward_temporal_witness_seed M psi) := by
  intro L hL_sub ⟨d⟩

  by_cases h_psi_in : psi ∈ L
  · -- Case: psi ∈ L
    let L_filt := L.filter (fun y => decide (y ≠ psi))
    have h_perm := cons_filter_neq_perm h_psi_in
    have d_reord : DerivationTree fc (psi :: L_filt) (Formula.bot : Formula Atom) :=
      derivation_exchange d (fun x => (h_perm x).symm)

    have d_neg : DerivationTree fc L_filt (Formula.neg psi) :=
      deduction_theorem L_filt psi Formula.bot d_reord

    -- Get G chi ∈ M for each chi ∈ L_filt from g_content
    have h_G_filt_in_M : ∀ chi ∈ L_filt, Formula.all_future chi ∈ M := by
      intro chi h_mem
      have h_and := List.mem_filter.mp h_mem
      have h_in_L := h_and.1
      have h_ne : chi ≠ psi := by simp only [decide_eq_true_eq] at h_and; exact h_and.2
      have h_in_seed := hL_sub chi h_in_L
      simp only [forward_temporal_witness_seed, Set.mem_union, Set.mem_singleton_iff] at h_in_seed
      rcases h_in_seed with h_eq | h_gcontent
      · exact absurd h_eq h_ne
      · exact h_gcontent

    -- Apply generalized temporal K (G distributes over derivation)
    have d_G_neg : DerivationTree fc (Context.map Formula.all_future L_filt) (Formula.all_future (Formula.neg psi)) :=
      Theorems.generalized_temporal_k L_filt (Formula.neg psi) d_neg

    -- All formulas in G(L_filt) are in M
    have h_G_context_in_M : ∀ phi ∈ Context.map Formula.all_future L_filt, phi ∈ M := by
      intro phi h_mem
      rw [Context.mem_map_iff] at h_mem
      rcases h_mem with ⟨chi, h_chi_in, h_eq⟩
      rw [← h_eq]
      exact h_G_filt_in_M chi h_chi_in

    -- By MCS closure under derivation, G(neg psi) ∈ M
    have h_G_neg_in_M : Formula.all_future (Formula.neg psi) ∈ M :=
      SetMaximalConsistent.closed_under_derivation h_mcs (Context.map Formula.all_future L_filt)
        h_G_context_in_M d_G_neg

    -- Contradiction: F(psi) and G(neg psi) cannot both be in MCS
    exact some_future_all_future_neg_absurd h_mcs psi h_F h_G_neg_in_M

  · -- Case: psi ∉ L, so L ⊆ g_content M
    have h_G_all_in_M : ∀ chi ∈ L, Formula.all_future chi ∈ M := by
      intro chi h_mem
      have h_in_seed := hL_sub chi h_mem
      simp only [forward_temporal_witness_seed, Set.mem_union, Set.mem_singleton_iff] at h_in_seed
      rcases h_in_seed with h_eq | h_gcontent
      · exact absurd h_eq (fun h => h_psi_in (h ▸ h_mem))
      · exact h_gcontent

    -- From L ⊢ ⊥, by generalized temporal K: G(L) ⊢ G(⊥)
    have d_G_bot : DerivationTree fc (Context.map Formula.all_future L) (Formula.all_future (Formula.bot : Formula Atom)) :=
      Theorems.generalized_temporal_k L Formula.bot d

    -- All formulas in G(L) are in M
    have h_G_L_in_M : ∀ phi ∈ Context.map Formula.all_future L, phi ∈ M := by
      intro phi h_mem
      rw [Context.mem_map_iff] at h_mem
      rcases h_mem with ⟨chi, h_chi_in, h_eq⟩
      rw [← h_eq]
      exact h_G_all_in_M chi h_chi_in

    -- So G(⊥) ∈ M
    have h_G_bot_in_M : Formula.all_future (Formula.bot : Formula Atom) ∈ M :=
      SetMaximalConsistent.closed_under_derivation h_mcs (Context.map Formula.all_future L)
        h_G_L_in_M d_G_bot

    -- ⊢ ⊥ → ¬psi by imp_s (weakening)
    have h_bot_imp_neg : DerivationTree fc [] ((Formula.bot : Formula Atom).imp (Formula.neg psi)) :=
      DerivationTree.axiom [] _ (Axiom.imp_s (Formula.bot : Formula Atom) psi) (FrameClass.base_le fc)

    -- By temporal necessitation: ⊢ G(⊥ → ¬psi)
    have h_G_ef : DerivationTree fc [] (Formula.all_future ((Formula.bot : Formula Atom).imp (Formula.neg psi))) :=
      DerivationTree.temporal_necessitation _ h_bot_imp_neg

    -- By temporal K distribution: ⊢ G(⊥ → ¬psi) → (G(⊥) → G(¬psi))
    have h_K : DerivationTree fc [] ((Formula.all_future ((Formula.bot : Formula Atom).imp (Formula.neg psi))).imp
                     ((Formula.all_future (Formula.bot : Formula Atom)).imp (Formula.all_future (Formula.neg psi)))) :=
      (Theorems.TemporalDerived.temp_k_dist_derived (Formula.bot : Formula Atom) (Formula.neg psi)).lift (FrameClass.base_le fc)

    -- Modus ponens twice: G(¬psi) ∈ M
    have h_G_imp : DerivationTree fc [] ((Formula.all_future (Formula.bot : Formula Atom)).imp (Formula.all_future (Formula.neg psi))) :=
      DerivationTree.modus_ponens [] _ _ h_K h_G_ef
    have h_G_neg_psi : Formula.all_future (Formula.neg psi) ∈ M :=
      SetMaximalConsistent.implication_property h_mcs (theorem_in_mcs_fc h_mcs h_G_imp) h_G_bot_in_M

    -- Contradiction: F(psi) and G(neg psi) cannot both be in MCS
    exact some_future_all_future_neg_absurd h_mcs psi h_F h_G_neg_psi

/-!
## Past Temporal Witness Seed
-/

/-- Past witness seed: `{psi} ∪ h_content(M)`. -/
def past_temporal_witness_seed (M : Set (Formula Atom)) (psi : Formula Atom) : Set (Formula Atom) :=
  {psi} ∪ h_content M

/-- psi is in its own past_temporal_witness_seed. -/
lemma psi_mem_past_temporal_witness_seed (M : Set (Formula Atom)) (psi : Formula Atom) :
    psi ∈ past_temporal_witness_seed M psi :=
  Set.mem_union_left _ (Set.mem_singleton psi)

/-- h_content is a subset of past_temporal_witness_seed. -/
lemma h_content_subset_past_temporal_witness_seed (M : Set (Formula Atom)) (psi : Formula Atom) :
    h_content M ⊆ past_temporal_witness_seed M psi :=
  Set.subset_union_right

/--
Past temporal witness seed consistency: If P(psi) is in an MCS M, then
`{psi} ∪ h_content(M)` is consistent.
-/
theorem past_temporal_witness_seed_consistent {fc : FrameClass} (M : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc M)
    (psi : Formula Atom) (h_P : Formula.some_past psi ∈ M) :
    SetConsistent fc (past_temporal_witness_seed M psi) := by
  intro L hL_sub ⟨d⟩

  by_cases h_psi_in : psi ∈ L
  · -- Case: psi ∈ L
    let L_filt := L.filter (fun y => decide (y ≠ psi))
    have h_perm := cons_filter_neq_perm h_psi_in
    have d_reord : DerivationTree fc (psi :: L_filt) (Formula.bot : Formula Atom) :=
      derivation_exchange d (fun x => (h_perm x).symm)

    have d_neg : DerivationTree fc L_filt (Formula.neg psi) :=
      deduction_theorem L_filt psi Formula.bot d_reord

    -- Get H chi ∈ M for each chi ∈ L_filt from h_content
    have h_H_filt_in_M : ∀ chi ∈ L_filt, Formula.all_past chi ∈ M := by
      intro chi h_mem
      have h_and := List.mem_filter.mp h_mem
      have h_in_L := h_and.1
      have h_ne : chi ≠ psi := by simp only [decide_eq_true_eq] at h_and; exact h_and.2
      have h_in_seed := hL_sub chi h_in_L
      simp only [past_temporal_witness_seed, Set.mem_union, Set.mem_singleton_iff] at h_in_seed
      rcases h_in_seed with h_eq | h_hcontent
      · exact absurd h_eq h_ne
      · exact h_hcontent

    -- Apply generalized past K (H distributes over derivation)
    have d_H_neg : DerivationTree fc (Context.map Formula.all_past L_filt) (Formula.all_past (Formula.neg psi)) :=
      Theorems.generalized_past_k L_filt (Formula.neg psi) d_neg

    -- All formulas in H(L_filt) are in M
    have h_H_context_in_M : ∀ phi ∈ Context.map Formula.all_past L_filt, phi ∈ M := by
      intro phi h_mem
      rw [Context.mem_map_iff] at h_mem
      rcases h_mem with ⟨chi, h_chi_in, h_eq⟩
      rw [← h_eq]
      exact h_H_filt_in_M chi h_chi_in

    -- By MCS closure under derivation, H(neg psi) ∈ M
    have h_H_neg_in_M : Formula.all_past (Formula.neg psi) ∈ M :=
      SetMaximalConsistent.closed_under_derivation h_mcs (Context.map Formula.all_past L_filt)
        h_H_context_in_M d_H_neg

    -- Contradiction: P(psi) and H(neg psi) cannot both be in MCS
    exact some_past_all_past_neg_absurd h_mcs psi h_P h_H_neg_in_M

  · -- Case: psi ∉ L, so L ⊆ h_content M
    have h_H_all_in_M : ∀ chi ∈ L, Formula.all_past chi ∈ M := by
      intro chi h_mem
      have h_in_seed := hL_sub chi h_mem
      simp only [past_temporal_witness_seed, Set.mem_union, Set.mem_singleton_iff] at h_in_seed
      rcases h_in_seed with h_eq | h_hcontent
      · exact absurd h_eq (fun h => h_psi_in (h ▸ h_mem))
      · exact h_hcontent

    -- From L ⊢ ⊥, by generalized past K: H(L) ⊢ H(⊥)
    have d_H_bot : DerivationTree fc (Context.map Formula.all_past L) (Formula.all_past (Formula.bot : Formula Atom)) :=
      Theorems.generalized_past_k L Formula.bot d

    -- All formulas in H(L) are in M
    have h_H_L_in_M : ∀ phi ∈ Context.map Formula.all_past L, phi ∈ M := by
      intro phi h_mem
      rw [Context.mem_map_iff] at h_mem
      rcases h_mem with ⟨chi, h_chi_in, h_eq⟩
      rw [← h_eq]
      exact h_H_all_in_M chi h_chi_in

    -- So H(⊥) ∈ M
    have h_H_bot_in_M : Formula.all_past (Formula.bot : Formula Atom) ∈ M :=
      SetMaximalConsistent.closed_under_derivation h_mcs (Context.map Formula.all_past L)
        h_H_L_in_M d_H_bot

    -- ⊢ ⊥ → ¬psi by imp_s
    have h_bot_imp_neg : DerivationTree fc [] ((Formula.bot : Formula Atom).imp (Formula.neg psi)) :=
      DerivationTree.axiom [] _ (Axiom.imp_s (Formula.bot : Formula Atom) psi) (FrameClass.base_le fc)

    -- By past necessitation: ⊢ H(⊥ → ¬psi)
    have h_H_ef : DerivationTree fc [] (Formula.all_past ((Formula.bot : Formula Atom).imp (Formula.neg psi))) :=
      Theorems.past_necessitation _ h_bot_imp_neg

    -- By past K distribution: ⊢ H(⊥ → ¬psi) → (H(⊥) → H(¬psi))
    have h_K : DerivationTree fc [] ((Formula.all_past ((Formula.bot : Formula Atom).imp (Formula.neg psi))).imp
                     ((Formula.all_past (Formula.bot : Formula Atom)).imp (Formula.all_past (Formula.neg psi)))) :=
      (Theorems.past_k_dist (Formula.bot : Formula Atom) (Formula.neg psi)).lift (FrameClass.base_le fc)

    -- Modus ponens twice: H(¬psi) ∈ M
    have h_H_imp : DerivationTree fc [] ((Formula.all_past (Formula.bot : Formula Atom)).imp (Formula.all_past (Formula.neg psi))) :=
      DerivationTree.modus_ponens [] _ _ h_K h_H_ef
    have h_H_neg_psi : Formula.all_past (Formula.neg psi) ∈ M :=
      SetMaximalConsistent.implication_property h_mcs (theorem_in_mcs_fc h_mcs h_H_imp) h_H_bot_in_M

    -- Contradiction: P(psi) and H(neg psi) cannot both be in MCS
    exact some_past_all_past_neg_absurd h_mcs psi h_P h_H_neg_psi

/-!
## Until Temporal Witness Seed
-/

/-- Until witness seed: `{ψ} ∪ g_content(M)`. -/
def until_witness_seed (M : Set (Formula Atom)) (ψ : Formula Atom) : Set (Formula Atom) :=
  {ψ} ∪ g_content M

/-- ψ is in its own until_witness_seed. -/
lemma psi_mem_until_witness_seed (M : Set (Formula Atom)) (ψ : Formula Atom) :
    ψ ∈ until_witness_seed M ψ :=
  Set.mem_union_left _ (Set.mem_singleton ψ)

/-- g_content is a subset of until_witness_seed. -/
lemma g_content_subset_until_witness_seed (M : Set (Formula Atom)) (ψ : Formula Atom) :
    g_content M ⊆ until_witness_seed M ψ :=
  Set.subset_union_right

/--
Until witness seed consistency: If `φ U ψ ∈ M` and M is MCS, then
`{ψ} ∪ g_content(M)` is consistent.
-/
theorem until_witness_seed_consistent (M : Set (Formula Atom)) (h_mcs : SetMaximalConsistent (FrameClass.Base : FrameClass) M)
    (φ ψ : Formula Atom) (h_U : Formula.untl ψ φ ∈ M) :
    SetConsistent FrameClass.Base (until_witness_seed M ψ) := by
  intro L hL_sub ⟨d⟩

  -- Extract G(¬ψ) ∈ M from the inconsistency of {ψ} ∪ g_content(M)
  have h_G_neg_psi : Formula.all_future (Formula.neg ψ) ∈ M := by
    by_cases h_psi_in : ψ ∈ L
    · -- Case: ψ ∈ L — derive G(¬ψ) via generalized temporal K
      let L_filt := L.filter (fun y => decide (y ≠ ψ))
      have h_perm := cons_filter_neq_perm h_psi_in
      have d_reord : DerivationTree FrameClass.Base (ψ :: L_filt) (Formula.bot : Formula Atom) :=
        derivation_exchange d (fun x => (h_perm x).symm)
      have d_neg : DerivationTree FrameClass.Base L_filt (Formula.neg ψ) :=
        deduction_theorem L_filt ψ Formula.bot d_reord
      have h_G_filt_in_M : ∀ chi ∈ L_filt, Formula.all_future chi ∈ M := by
        intro chi h_mem
        have h_and := List.mem_filter.mp h_mem
        have h_in_L := h_and.1
        have h_ne : chi ≠ ψ := by simp only [decide_eq_true_eq] at h_and; exact h_and.2
        have h_in_seed := hL_sub chi h_in_L
        simp only [until_witness_seed, Set.mem_union, Set.mem_singleton_iff] at h_in_seed
        rcases h_in_seed with h_eq | h_gcontent
        · exact absurd h_eq h_ne
        · exact h_gcontent
      have d_G_neg : DerivationTree FrameClass.Base (Context.map Formula.all_future L_filt) (Formula.all_future (Formula.neg ψ)) :=
        Theorems.generalized_temporal_k L_filt (Formula.neg ψ) d_neg
      have h_G_context_in_M : ∀ f ∈ Context.map Formula.all_future L_filt, f ∈ M := by
        intro f h_mem
        rw [Context.mem_map_iff] at h_mem
        rcases h_mem with ⟨chi, h_chi_in, h_eq⟩
        rw [← h_eq]
        exact h_G_filt_in_M chi h_chi_in
      exact SetMaximalConsistent.closed_under_derivation h_mcs
        (Context.map Formula.all_future L_filt) h_G_context_in_M d_G_neg
    · -- Case: ψ ∉ L — all of L ⊆ g_content(M), derive G(⊥) then G(¬ψ)
      have h_G_all_in_M : ∀ chi ∈ L, Formula.all_future chi ∈ M := by
        intro chi h_mem
        have h_in_seed := hL_sub chi h_mem
        simp only [until_witness_seed, Set.mem_union, Set.mem_singleton_iff] at h_in_seed
        rcases h_in_seed with h_eq | h_gcontent
        · exact absurd h_eq (fun h => h_psi_in (h ▸ h_mem))
        · exact h_gcontent
      have d_G_bot : DerivationTree FrameClass.Base (Context.map Formula.all_future L) (Formula.all_future (Formula.bot : Formula Atom)) :=
        Theorems.generalized_temporal_k L Formula.bot d
      have h_G_L_in_M : ∀ f ∈ Context.map Formula.all_future L, f ∈ M := by
        intro f h_mem
        rw [Context.mem_map_iff] at h_mem
        rcases h_mem with ⟨chi, h_chi_in, h_eq⟩
        rw [← h_eq]
        exact h_G_all_in_M chi h_chi_in
      have h_G_bot_in_M : Formula.all_future (Formula.bot : Formula Atom) ∈ M :=
        SetMaximalConsistent.closed_under_derivation h_mcs
          (Context.map Formula.all_future L) h_G_L_in_M d_G_bot
      have h_bot_imp_neg : DerivationTree FrameClass.Base [] ((Formula.bot : Formula Atom).imp (Formula.neg ψ)) :=
        DerivationTree.axiom [] _ (Axiom.imp_s (Formula.bot : Formula Atom) ψ) trivial
      have h_G_ef : DerivationTree FrameClass.Base [] (Formula.all_future ((Formula.bot : Formula Atom).imp (Formula.neg ψ))) :=
        DerivationTree.temporal_necessitation _ h_bot_imp_neg
      have h_K : DerivationTree FrameClass.Base [] ((Formula.all_future ((Formula.bot : Formula Atom).imp (Formula.neg ψ))).imp
                       ((Formula.all_future (Formula.bot : Formula Atom)).imp (Formula.all_future (Formula.neg ψ)))) :=
        Theorems.TemporalDerived.temp_k_dist_derived (Formula.bot : Formula Atom) (Formula.neg ψ)
      have h_G_imp : DerivationTree FrameClass.Base [] ((Formula.all_future (Formula.bot : Formula Atom)).imp (Formula.all_future (Formula.neg ψ))) :=
        DerivationTree.modus_ponens [] _ _ h_K h_G_ef
      exact SetMaximalConsistent.implication_property h_mcs
        (theorem_in_mcs_fc h_mcs h_G_imp) h_G_bot_in_M

  -- BX10 contradiction: (φ U ψ) → F(ψ) by BX10, and F(ψ) = ¬G(¬ψ), contradicting G(¬ψ) ∈ M
  have h_F_psi : ψ.some_future ∈ M :=
    SetMaximalConsistent.implication_property h_mcs
      (theorem_in_mcs_fc h_mcs (Theorems.TemporalDerived.until_imp_F φ ψ)) h_U
  exact some_future_all_future_neg_absurd h_mcs ψ h_F_psi h_G_neg_psi

/--
Since witness seed consistency: If `φ S ψ ∈ M` and M is MCS, then
`{ψ} ∪ h_content(M)` is consistent.
-/
theorem since_witness_seed_consistent (M : Set (Formula Atom)) (h_mcs : SetMaximalConsistent (FrameClass.Base : FrameClass) M)
    (φ ψ : Formula Atom) (h_S : Formula.snce ψ φ ∈ M) :
    SetConsistent FrameClass.Base (past_temporal_witness_seed M ψ) := by
  intro L hL_sub ⟨d⟩

  -- Extract H(¬ψ) ∈ M from the inconsistency of {ψ} ∪ h_content(M)
  have h_H_neg_psi : Formula.all_past (Formula.neg ψ) ∈ M := by
    by_cases h_psi_in : ψ ∈ L
    · let L_filt := L.filter (fun y => decide (y ≠ ψ))
      have h_perm := cons_filter_neq_perm h_psi_in
      have d_reord : DerivationTree FrameClass.Base (ψ :: L_filt) (Formula.bot : Formula Atom) :=
        derivation_exchange d (fun x => (h_perm x).symm)
      have d_neg : DerivationTree FrameClass.Base L_filt (Formula.neg ψ) :=
        deduction_theorem L_filt ψ Formula.bot d_reord
      have h_H_filt_in_M : ∀ chi ∈ L_filt, Formula.all_past chi ∈ M := by
        intro chi h_mem
        have h_and := List.mem_filter.mp h_mem
        have h_in_L := h_and.1
        have h_ne : chi ≠ ψ := by simp only [decide_eq_true_eq] at h_and; exact h_and.2
        have h_in_seed := hL_sub chi h_in_L
        simp only [past_temporal_witness_seed, Set.mem_union, Set.mem_singleton_iff] at h_in_seed
        rcases h_in_seed with h_eq | h_hcontent
        · exact absurd h_eq h_ne
        · exact h_hcontent
      have d_H_neg : DerivationTree FrameClass.Base (Context.map Formula.all_past L_filt) (Formula.all_past (Formula.neg ψ)) :=
        Theorems.generalized_past_k L_filt (Formula.neg ψ) d_neg
      have h_H_context_in_M : ∀ f ∈ Context.map Formula.all_past L_filt, f ∈ M := by
        intro f h_mem
        rw [Context.mem_map_iff] at h_mem
        rcases h_mem with ⟨chi, h_chi_in, h_eq⟩
        rw [← h_eq]
        exact h_H_filt_in_M chi h_chi_in
      exact SetMaximalConsistent.closed_under_derivation h_mcs
        (Context.map Formula.all_past L_filt) h_H_context_in_M d_H_neg
    · have h_H_all_in_M : ∀ chi ∈ L, Formula.all_past chi ∈ M := by
        intro chi h_mem
        have h_in_seed := hL_sub chi h_mem
        simp only [past_temporal_witness_seed, Set.mem_union, Set.mem_singleton_iff] at h_in_seed
        rcases h_in_seed with h_eq | h_hcontent
        · exact absurd h_eq (fun h => h_psi_in (h ▸ h_mem))
        · exact h_hcontent
      have d_H_bot : DerivationTree FrameClass.Base (Context.map Formula.all_past L) (Formula.all_past (Formula.bot : Formula Atom)) :=
        Theorems.generalized_past_k L Formula.bot d
      have h_H_L_in_M : ∀ f ∈ Context.map Formula.all_past L, f ∈ M := by
        intro f h_mem
        rw [Context.mem_map_iff] at h_mem
        rcases h_mem with ⟨chi, h_chi_in, h_eq⟩
        rw [← h_eq]
        exact h_H_all_in_M chi h_chi_in
      have h_H_bot_in_M : Formula.all_past (Formula.bot : Formula Atom) ∈ M :=
        SetMaximalConsistent.closed_under_derivation h_mcs
          (Context.map Formula.all_past L) h_H_L_in_M d_H_bot
      have h_bot_imp_neg : DerivationTree FrameClass.Base [] ((Formula.bot : Formula Atom).imp (Formula.neg ψ)) :=
        DerivationTree.axiom [] _ (Axiom.imp_s (Formula.bot : Formula Atom) ψ) trivial
      have h_H_ef : DerivationTree FrameClass.Base [] (Formula.all_past ((Formula.bot : Formula Atom).imp (Formula.neg ψ))) :=
        Theorems.past_necessitation _ h_bot_imp_neg
      have h_K : DerivationTree FrameClass.Base [] ((Formula.all_past ((Formula.bot : Formula Atom).imp (Formula.neg ψ))).imp
                       ((Formula.all_past (Formula.bot : Formula Atom)).imp (Formula.all_past (Formula.neg ψ)))) :=
        Theorems.past_k_dist (Formula.bot : Formula Atom) (Formula.neg ψ)
      have h_H_imp : DerivationTree FrameClass.Base [] ((Formula.all_past (Formula.bot : Formula Atom)).imp (Formula.all_past (Formula.neg ψ))) :=
        DerivationTree.modus_ponens [] _ _ h_K h_H_ef
      exact SetMaximalConsistent.implication_property h_mcs
        (theorem_in_mcs_fc h_mcs h_H_imp) h_H_bot_in_M

  -- BX10' contradiction: (φ S ψ) → P(ψ) by BX10', and P(ψ) = ¬H(¬ψ), contradicting H(¬ψ) ∈ M
  have h_P_psi : ψ.some_past ∈ M :=
    SetMaximalConsistent.implication_property h_mcs
      (theorem_in_mcs_fc h_mcs (Theorems.TemporalDerived.since_imp_P φ ψ)) h_S
  exact some_past_all_past_neg_absurd h_mcs ψ h_P_psi h_H_neg_psi

/-!
## g_content/h_content Duality
-/

/-- If g_content(M) ⊆ M', then h_content(M') ⊆ M.
Uses connect_future: φ → G(P(φ)). -/
theorem g_content_subset_implies_h_content_reverse
    (M M' : Set (Formula Atom)) (h_mcs : SetMaximalConsistent (FrameClass.Base : FrameClass) M) (h_mcs' : SetMaximalConsistent (FrameClass.Base : FrameClass) M')
    (h_GC : g_content M ⊆ M') :
    h_content M' ⊆ M := by
  intro phi h_H_phi_in_M'
  by_contra h_not_phi
  have h_neg_phi : Formula.neg phi ∈ M := by
    rcases SetMaximalConsistent.negation_complete h_mcs phi with h | h
    · exact absurd h h_not_phi
    · exact h
  have h_ta : DerivationTree FrameClass.Base [] ((Formula.neg phi).imp (Formula.all_future (Formula.neg phi).some_past)) :=
    DerivationTree.axiom [] _ (Axiom.connect_future (Formula.neg phi)) trivial
  have h_G_P_neg : Formula.all_future (Formula.neg phi).some_past ∈ M :=
    SetMaximalConsistent.implication_property h_mcs (theorem_in_mcs_fc h_mcs h_ta) h_neg_phi
  have h_P_neg_M' : (Formula.neg phi).some_past ∈ M' := h_GC h_G_P_neg
  have h_dni : DerivationTree FrameClass.Base [] (phi.imp phi.neg.neg) := Theorems.Combinators.dni phi
  have h_H_dni : DerivationTree FrameClass.Base [] ((phi.imp phi.neg.neg).all_past) :=
    Theorems.past_necessitation _ h_dni
  have h_pk : DerivationTree FrameClass.Base [] ((phi.imp phi.neg.neg).all_past.imp (phi.all_past.imp phi.neg.neg.all_past)) :=
    Theorems.past_k_dist phi phi.neg.neg
  have h_H_imp : DerivationTree FrameClass.Base [] (phi.all_past.imp phi.neg.neg.all_past) :=
    DerivationTree.modus_ponens [] _ _ h_pk h_H_dni
  have h_H_nn : phi.neg.neg.all_past ∈ M' :=
    SetMaximalConsistent.implication_property h_mcs' (theorem_in_mcs_fc h_mcs' h_H_imp) h_H_phi_in_M'
  exact some_past_all_past_neg_absurd h_mcs' (Formula.neg phi) h_P_neg_M' h_H_nn

/-- If h_content(M) ⊆ M', then g_content(M') ⊆ M.
Uses connect_past: φ → H(F(φ)). -/
theorem h_content_subset_implies_g_content_reverse
    (M M' : Set (Formula Atom)) (h_mcs : SetMaximalConsistent (FrameClass.Base : FrameClass) M) (h_mcs' : SetMaximalConsistent (FrameClass.Base : FrameClass) M')
    (h_HC : h_content M ⊆ M') :
    g_content M' ⊆ M := by
  intro phi h_G_phi_in_M'
  have h_G_phi : Formula.all_future phi ∈ M' := h_G_phi_in_M'
  by_contra h_not_phi
  have h_neg_phi : Formula.neg phi ∈ M := by
    rcases SetMaximalConsistent.negation_complete h_mcs phi with h | h
    · exact absurd h h_not_phi
    · exact h
  have h_pta : DerivationTree FrameClass.Base [] ((Formula.neg phi).imp (Formula.neg phi).some_future.all_past) :=
    DerivationTree.axiom [] _ (Axiom.connect_past (Formula.neg phi)) trivial
  have h_H_F_neg : (Formula.neg phi).some_future.all_past ∈ M :=
    SetMaximalConsistent.implication_property h_mcs (theorem_in_mcs_fc h_mcs h_pta) h_neg_phi
  have h_F_neg_M' : (Formula.neg phi).some_future ∈ M' := h_HC h_H_F_neg
  have h_dni : DerivationTree FrameClass.Base [] (phi.imp phi.neg.neg) := Theorems.Combinators.dni phi
  have h_G_dni : DerivationTree FrameClass.Base [] ((phi.imp phi.neg.neg).all_future) :=
    DerivationTree.temporal_necessitation _ h_dni
  have h_fk : DerivationTree FrameClass.Base [] ((phi.imp phi.neg.neg).all_future.imp (phi.all_future.imp phi.neg.neg.all_future)) :=
    Theorems.Perpetuity.future_k_dist phi phi.neg.neg
  have h_G_imp : DerivationTree FrameClass.Base [] (phi.all_future.imp phi.neg.neg.all_future) :=
    DerivationTree.modus_ponens [] _ _ h_fk h_G_dni
  have h_G_nn : phi.neg.neg.all_future ∈ M' :=
    SetMaximalConsistent.implication_property h_mcs' (theorem_in_mcs_fc h_mcs' h_G_imp) h_G_phi
  exact some_future_all_future_neg_absurd h_mcs' (Formula.neg phi) h_F_neg_M' h_G_nn

end Cslib.Logic.Bimodal.Metalogic.Bundle
