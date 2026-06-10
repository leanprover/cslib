/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.BXCanonical.CanonicalChain
public import Cslib.Logics.Bimodal.Metalogic.BXCanonical.TruthLemma
public import Cslib.Logics.Bimodal.Metalogic.Bundle.FMCSDef
public import Cslib.Logics.Bimodal.Metalogic.Bundle.BFMCS
public import Cslib.Logics.Bimodal.Metalogic.Bundle.CanonicalFrame
public import Cslib.Logics.Bimodal.Metalogic.Bundle.ModalSaturation
public import Cslib.Logics.Bimodal.Theorems.GeneralizedNecessitation
public import Mathlib.Logic.Denumerable

/-!
# BXCanonical Canonical Model Construction

Constructs a BFMCS Int from BXCanonical witnesses, bridging to the parametric
algebraic completeness theorem for the BX completeness proof.

## References

* Ported from BimodalLogic/Theories/Bimodal/Metalogic/BXCanonical/CanonicalModel.lean
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.BXCanonical.CanonicalModel

open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Metalogic.Core
open Cslib.Logic.Bimodal.Metalogic.Bundle
open Cslib.Logic.Bimodal.Theorems.Combinators

attribute [local instance] Classical.propDecidable

variable {Atom : Type*}

/-! ## Helper -/

private noncomputable def theorem_in_mcs_fc' {fc : FrameClass} {M : Set (Formula Atom)} {phi : Formula Atom}
    (h_mcs : SetMaximalConsistent fc M)
    (h_deriv : DerivationTree fc [] phi) : phi ∈ M :=
  SetMaximalConsistent.closed_under_derivation h_mcs [] (fun _ h => by simp at h) h_deriv

/-! ## FC-Parametric Utility Lemmas -/

/-- Lift a Base-level derivation to any frame class. -/
noncomputable def liftBase (fc : FrameClass) {Γ : Context Atom} {φ : Formula Atom}
    (d : DerivationTree FrameClass.Base Γ φ) : DerivationTree fc Γ φ :=
  d.lift (FrameClass.base_le fc)

/-- An MCS at any frame class is also an MCS at Base. -/
theorem mcs_to_base {fc : FrameClass} {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) :
    SetMaximalConsistent FrameClass.Base A := by
  constructor
  · intro L hL ⟨d⟩
    exact h_mcs.1 L hL ⟨liftBase fc d⟩
  · intro φ hφ
    have h_neg : φ.neg ∈ A := by
      rcases SetMaximalConsistent.negation_complete h_mcs φ with h | h
      · exact absurd h hφ
      · exact h
    intro h_cons
    exact set_consistent_not_both h_cons φ (Set.mem_insert φ A) (Set.mem_insert_of_mem φ h_neg)

/-- FC-parametric Lindenbaum: extend an fc-consistent set to an fc-MCS. -/
theorem set_lindenbaum_fc {fc : FrameClass} {Omega : Set (Formula Atom)}
    (hOmega : SetConsistent fc Omega) :
    ∃ M : Set (Formula Atom), Omega ⊆ M ∧ SetMaximalConsistent fc M := by
  obtain ⟨M, hSM, ⟨hM_mem, hM_max⟩⟩ := zorn_subset_nonempty
    { T : Set (Formula Atom) | Omega ⊆ T ∧ SetConsistent fc T }
    (fun C hC hchain hCne => by
      refine ⟨⋃₀ C, ⟨?_, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
      · intro x hx
        obtain ⟨T, hT⟩ := hCne
        exact Set.mem_sUnion.mpr ⟨T, hT, (hC hT).1 hx⟩
      · intro L hL
        have ⟨T, hTC, hLT⟩ := Metalogic.finite_list_in_chain_member hchain hCne L hL
        exact (hC hTC).2 L hLT)
    Omega ⟨Set.Subset.refl Omega, hOmega⟩
  obtain ⟨hOmega_sub, hM_cons⟩ := hM_mem
  refine ⟨M, hSM, hM_cons, ?_⟩
  intro φ hφ h_cons
  have h_ins_mem : insert φ M ∈ { T | Omega ⊆ T ∧ SetConsistent fc T } :=
    ⟨Set.Subset.trans hOmega_sub (Set.subset_insert φ M), h_cons⟩
  exact hφ (hM_max h_ins_mem (Set.subset_insert φ M) (Set.mem_insert φ M))

/-- Modal witness at arbitrary fc: given an fc-MCS A with diamond-psi in A, produce an fc-MCS v
that is box-equivalent to A and contains psi. -/
noncomputable def bx_modal_witness_fc {fc : FrameClass} {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) (psi : Formula Atom)
    (h_dia : Formula.diamond psi ∈ A) :
    ∃ (v : Set (Formula Atom)), SetMaximalConsistent fc v ∧
      (∀ chi, Formula.box chi ∈ A ↔ Formula.box chi ∈ v) ∧ psi ∈ v := by
  let bc := {chi : Formula Atom | Formula.box chi ∈ A}
  have h_seed_cons : SetConsistent fc ({psi} ∪ bc) := by
    intro L hL ⟨d⟩
    by_cases h_psi_in : psi ∈ L
    · let L_filt := L.filter (fun y => decide (y ≠ psi))
      have d_reord : DerivationTree fc (psi :: L_filt) (Formula.bot : Formula Atom) :=
        derivation_exchange d (fun x => (cons_filter_neq_perm h_psi_in x).symm)
      have d_neg : DerivationTree fc L_filt (Formula.neg psi) :=
        deduction_theorem L_filt psi (Formula.bot : Formula Atom) d_reord
      have h_filt_box : ∀ x ∈ L_filt, Formula.box x ∈ A := by
        intro x hx
        have hx_L : x ∈ L := List.mem_of_mem_filter hx
        have hx_ne : x ≠ psi := by
          have := (List.mem_filter.mp hx).2
          simp at this; exact this
        have h_mem := hL x hx_L
        simp only [Set.mem_union, Set.mem_singleton_iff] at h_mem
        rcases h_mem with rfl | h
        · exact absurd rfl hx_ne
        · exact h
      have d_box_neg : DerivationTree fc (Context.map Formula.box L_filt) (Formula.box (Formula.neg psi)) :=
        Theorems.generalized_modal_k L_filt (Formula.neg psi) d_neg
      have h_box_L_in : ∀ f ∈ Context.map Formula.box L_filt, f ∈ A := by
        intro f hf
        rw [Context.mem_map_iff] at hf
        obtain ⟨chi, hchi_in, hchi_eq⟩ := hf
        rw [← hchi_eq]
        exact h_filt_box chi hchi_in
      have h_box_neg_in := SetMaximalConsistent.closed_under_derivation h_mcs
        (Context.map Formula.box L_filt) h_box_L_in d_box_neg
      have h_eq : Formula.diamond psi = Formula.neg (Formula.box (Formula.neg psi)) := rfl
      rw [h_eq] at h_dia
      exact set_consistent_not_both h_mcs.1 _ h_box_neg_in h_dia
    · have h_L_in_bc : ∀ chi ∈ L, chi ∈ bc := by
        intro chi hchi
        have h_mem := hL chi hchi
        simp only [Set.mem_union, Set.mem_singleton_iff] at h_mem
        rcases h_mem with rfl | h
        · exact absurd hchi h_psi_in
        · exact h
      have d_box_bot : DerivationTree fc (Context.map Formula.box L) (Formula.box (Formula.bot : Formula Atom)) :=
        Theorems.generalized_modal_k L (Formula.bot : Formula Atom) d
      have h_box_L_in : ∀ f ∈ Context.map Formula.box L, f ∈ A := by
        intro f hf
        rw [Context.mem_map_iff] at hf
        obtain ⟨chi, hchi_in, hchi_eq⟩ := hf
        rw [← hchi_eq]
        exact h_L_in_bc chi hchi_in
      have h_box_bot_in := SetMaximalConsistent.closed_under_derivation h_mcs
        (Context.map Formula.box L) h_box_L_in d_box_bot
      have h_ax : DerivationTree fc [] ((Formula.box (Formula.bot : Formula Atom)).imp (Formula.bot : Formula Atom)) :=
        DerivationTree.axiom [] _ (Axiom.modal_t (Formula.bot : Formula Atom)) trivial
      have h_bot := SetMaximalConsistent.implication_property h_mcs
        (theorem_in_mcs_fc' h_mcs h_ax) h_box_bot_in
      exact h_mcs.1 [(Formula.bot : Formula Atom)] (fun chi hchi => by simp at hchi; rw [hchi]; exact h_bot)
        ⟨DerivationTree.assumption [(Formula.bot : Formula Atom)] (Formula.bot : Formula Atom) (by simp)⟩
  obtain ⟨v, h_sub, h_v_mcs⟩ := set_lindenbaum_fc h_seed_cons
  have h_psi_in : psi ∈ v := h_sub (Set.mem_union_left bc (Set.mem_singleton_iff.mpr rfl))
  have h_bc_sub : bc ⊆ v := fun chi hchi => h_sub (Set.mem_union_right {psi} hchi)
  have h_box_equiv : ∀ chi, Formula.box chi ∈ A ↔ Formula.box chi ∈ v := by
    intro chi
    constructor
    · intro h_box
      have h_m4 : DerivationTree fc [] ((Formula.box chi).imp (Formula.box (Formula.box chi))) :=
        DerivationTree.axiom [] _ (Axiom.modal_4 chi) trivial
      have h_box_box := SetMaximalConsistent.implication_property h_mcs
        (theorem_in_mcs_fc' h_mcs h_m4) h_box
      exact h_bc_sub h_box_box
    · intro h_box_v
      by_contra h_not_box
      have h_neg_box : (Formula.box chi).neg ∈ A := by
        rcases SetMaximalConsistent.negation_complete h_mcs (Formula.box chi) with h | h
        · exact absurd h h_not_box
        · exact h
      have h_m5 : DerivationTree fc [] ((Formula.box chi).neg.imp (Formula.box (Formula.box chi).neg)) :=
        liftBase fc (axiom_5_negative_introspection chi)
      have h_box_neg_box := SetMaximalConsistent.implication_property h_mcs
        (theorem_in_mcs_fc' h_mcs h_m5) h_neg_box
      have h_neg_box_v : (Formula.box chi).neg ∈ v := h_bc_sub h_box_neg_box
      exact set_consistent_not_both h_v_mcs.1 (Formula.box chi) h_box_v h_neg_box_v
  exact ⟨v, h_v_mcs, h_box_equiv, h_psi_in⟩

/-! ## Schedule -/

variable [Denumerable (Formula Atom)]

noncomputable def schedule (n : Nat) : Formula Atom :=
  Denumerable.ofNat (Formula Atom) (Nat.unpair n).2

theorem schedule_surjective_above (psi : Formula Atom) (k : Nat) :
    ∃ n : Nat, n ≥ k ∧ schedule n = psi :=
  ⟨Nat.pair k (Encodable.encode psi),
   Nat.left_le_pair k _,
   by simp [schedule, Nat.unpair_pair, Denumerable.ofNat_encode]⟩

/-! ## Forward Step -/

noncomputable def fwd_succ (M : Set (Formula Atom)) (h_mcs : SetMaximalConsistent FrameClass.Base M) (psi : Formula Atom) :
    Set (Formula Atom) := by
  by_cases h_F : Formula.someFuture psi ∈ M
  · exact (set_lindenbaum_base (forward_temporal_witness_seed_consistent M h_mcs psi h_F)).choose
  · exact (set_lindenbaum_base (g_content_set_consistent h_mcs)).choose

theorem fwd_succ_mcs (M : Set (Formula Atom)) (h_mcs : SetMaximalConsistent FrameClass.Base M) (psi : Formula Atom) :
    SetMaximalConsistent FrameClass.Base (fwd_succ M h_mcs psi) := by
  unfold fwd_succ; split
  · exact (set_lindenbaum_base (forward_temporal_witness_seed_consistent M h_mcs psi ‹_›)).choose_spec.2
  · exact (set_lindenbaum_base (g_content_set_consistent h_mcs)).choose_spec.2

theorem fwd_succ_g_content (M : Set (Formula Atom)) (h_mcs : SetMaximalConsistent FrameClass.Base M) (psi : Formula Atom) :
    g_content M ⊆ fwd_succ M h_mcs psi := by
  unfold fwd_succ; split
  · exact fun chi hchi => (set_lindenbaum_base (forward_temporal_witness_seed_consistent M h_mcs psi ‹_›)).choose_spec.1
      (Set.mem_union_right _ hchi)
  · exact fun chi hchi => (set_lindenbaum_base (g_content_set_consistent h_mcs)).choose_spec.1 hchi

theorem fwd_succ_resolves (M : Set (Formula Atom)) (h_mcs : SetMaximalConsistent FrameClass.Base M) (psi : Formula Atom)
    (h_F : Formula.someFuture psi ∈ M) : psi ∈ fwd_succ M h_mcs psi := by
  unfold fwd_succ; rw [dif_pos h_F]
  exact (set_lindenbaum_base (forward_temporal_witness_seed_consistent M h_mcs psi h_F)).choose_spec.1
    (Set.mem_union_left _ (Set.mem_singleton psi))

/-! ## Backward Step -/

noncomputable def bwd_pred (M : Set (Formula Atom)) (h_mcs : SetMaximalConsistent FrameClass.Base M) (psi : Formula Atom) :
    Set (Formula Atom) := by
  by_cases h_P : Formula.somePast psi ∈ M
  · exact (set_lindenbaum_base (past_temporal_witness_seed_consistent M h_mcs psi h_P)).choose
  · exact (set_lindenbaum_base (h_content_set_consistent h_mcs)).choose

theorem bwd_pred_mcs (M : Set (Formula Atom)) (h_mcs : SetMaximalConsistent FrameClass.Base M) (psi : Formula Atom) :
    SetMaximalConsistent FrameClass.Base (bwd_pred M h_mcs psi) := by
  unfold bwd_pred; split
  · exact (set_lindenbaum_base (past_temporal_witness_seed_consistent M h_mcs psi ‹_›)).choose_spec.2
  · exact (set_lindenbaum_base (h_content_set_consistent h_mcs)).choose_spec.2

theorem bwd_pred_h_content (M : Set (Formula Atom)) (h_mcs : SetMaximalConsistent FrameClass.Base M) (psi : Formula Atom) :
    h_content M ⊆ bwd_pred M h_mcs psi := by
  unfold bwd_pred; split
  · exact fun chi hchi => (set_lindenbaum_base (past_temporal_witness_seed_consistent M h_mcs psi ‹_›)).choose_spec.1
      (Set.mem_union_right _ hchi)
  · exact fun chi hchi => (set_lindenbaum_base (h_content_set_consistent h_mcs)).choose_spec.1 hchi

theorem bwd_pred_resolves (M : Set (Formula Atom)) (h_mcs : SetMaximalConsistent FrameClass.Base M) (psi : Formula Atom)
    (h_P : Formula.somePast psi ∈ M) : psi ∈ bwd_pred M h_mcs psi := by
  unfold bwd_pred; rw [dif_pos h_P]
  exact (set_lindenbaum_base (past_temporal_witness_seed_consistent M h_mcs psi h_P)).choose_spec.1
    (Set.mem_union_left _ (Set.mem_singleton psi))

/-! ## Forward/Backward Chains -/

noncomputable def fwd_chain (M0 : Set (Formula Atom)) (h0 : SetMaximalConsistent FrameClass.Base M0) :
    (n : Nat) → { M : Set (Formula Atom) // SetMaximalConsistent FrameClass.Base M }
  | 0 => ⟨M0, h0⟩
  | n + 1 =>
    let ⟨M, hM⟩ := fwd_chain M0 h0 n
    ⟨fwd_succ M hM (schedule n), fwd_succ_mcs M hM (schedule n)⟩

noncomputable def bwd_chain (M0 : Set (Formula Atom)) (h0 : SetMaximalConsistent FrameClass.Base M0) :
    (n : Nat) → { M : Set (Formula Atom) // SetMaximalConsistent FrameClass.Base M }
  | 0 => ⟨M0, h0⟩
  | n + 1 =>
    let ⟨M, hM⟩ := bwd_chain M0 h0 n
    ⟨bwd_pred M hM (schedule n), bwd_pred_mcs M hM (schedule n)⟩

/-! ## Int-indexed Chain -/

noncomputable def int_chain (M0 : Set (Formula Atom)) (h0 : SetMaximalConsistent FrameClass.Base M0) (t : Int) :
    Set (Formula Atom) :=
  if t ≥ 0 then (fwd_chain M0 h0 t.toNat).val
  else (bwd_chain M0 h0 ((-t).toNat)).val

theorem int_chain_zero (M0 : Set (Formula Atom)) (h0 : SetMaximalConsistent FrameClass.Base M0) :
    int_chain M0 h0 0 = M0 := by simp [int_chain, fwd_chain]

theorem int_chain_mcs (M0 : Set (Formula Atom)) (h0 : SetMaximalConsistent FrameClass.Base M0) (t : Int) :
    SetMaximalConsistent FrameClass.Base (int_chain M0 h0 t) := by
  simp only [int_chain]; split
  · exact (fwd_chain M0 h0 t.toNat).property
  · exact (bwd_chain M0 h0 ((-t).toNat)).property

/-! ### Chain ordering -/

theorem fwd_chain_g_content_step (M0 : Set (Formula Atom)) (h0 : SetMaximalConsistent FrameClass.Base M0) (n : Nat) :
    g_content (fwd_chain M0 h0 n).val ⊆ (fwd_chain M0 h0 (n + 1)).val := by
  show g_content (fwd_chain M0 h0 n).val ⊆
    (fwd_succ (fwd_chain M0 h0 n).val (fwd_chain M0 h0 n).property (schedule n))
  exact fwd_succ_g_content _ _ _

theorem fwd_chain_g_content_trans (M0 : Set (Formula Atom)) (h0 : SetMaximalConsistent FrameClass.Base M0)
    {m n : Nat} (h : m < n) :
    g_content (fwd_chain M0 h0 m).val ⊆ (fwd_chain M0 h0 n).val := by
  induction n with
  | zero => exact absurd h (Nat.not_lt_zero m)
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp h) with rfl | h_lt
    · exact fwd_chain_g_content_step M0 h0 m
    · intro phi hphi
      exact fwd_chain_g_content_step M0 h0 n (ih h_lt (SetMaximalConsistent.allFuture_allFuture (fwd_chain M0 h0 m).property hphi))

theorem bwd_chain_h_content_step (M0 : Set (Formula Atom)) (h0 : SetMaximalConsistent FrameClass.Base M0) (n : Nat) :
    h_content (bwd_chain M0 h0 n).val ⊆ (bwd_chain M0 h0 (n + 1)).val := by
  show h_content (bwd_chain M0 h0 n).val ⊆
    (bwd_pred (bwd_chain M0 h0 n).val (bwd_chain M0 h0 n).property (schedule n))
  exact bwd_pred_h_content _ _ _

theorem bwd_chain_h_content_trans (M0 : Set (Formula Atom)) (h0 : SetMaximalConsistent FrameClass.Base M0)
    {m n : Nat} (h : m < n) :
    h_content (bwd_chain M0 h0 m).val ⊆ (bwd_chain M0 h0 n).val := by
  induction n with
  | zero => exact absurd h (Nat.not_lt_zero m)
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp h) with rfl | h_lt
    · exact bwd_chain_h_content_step M0 h0 m
    · intro phi hphi
      exact bwd_chain_h_content_step M0 h0 n (ih h_lt (SetMaximalConsistent.allPast_allPast (bwd_chain M0 h0 m).property hphi))

theorem fwd_chain_reverse_h (M0 : Set (Formula Atom)) (h0 : SetMaximalConsistent FrameClass.Base M0)
    {m n : Nat} (h : m < n) :
    h_content (fwd_chain M0 h0 n).val ⊆ (fwd_chain M0 h0 m).val :=
  g_content_subset_implies_h_content_reverse _ _ (fwd_chain M0 h0 m).property (fwd_chain M0 h0 n).property
    (fwd_chain_g_content_trans M0 h0 h)

theorem bwd_chain_reverse_g (M0 : Set (Formula Atom)) (h0 : SetMaximalConsistent FrameClass.Base M0)
    {m n : Nat} (h : m < n) :
    g_content (bwd_chain M0 h0 n).val ⊆ (bwd_chain M0 h0 m).val :=
  h_content_subset_implies_g_content_reverse _ _ (bwd_chain M0 h0 m).property (bwd_chain M0 h0 n).property
    (bwd_chain_h_content_trans M0 h0 h)

theorem int_chain_g_content (M0 : Set (Formula Atom)) (h0 : SetMaximalConsistent FrameClass.Base M0)
    {t t' : Int} (h_lt : t < t') :
    g_content (int_chain M0 h0 t) ⊆ int_chain M0 h0 t' := by
  simp only [int_chain]
  split_ifs with ht ht'
  · exact fwd_chain_g_content_trans M0 h0 (by omega)
  · omega
  · intro chi hchi
    rcases Nat.eq_zero_or_pos t'.toNat with h_zero | h_pos
    · have h_in_bwd0 := bwd_chain_reverse_g M0 h0 (show 0 < ((-t).toNat) by omega) hchi
      simp only [bwd_chain] at h_in_bwd0
      simp only [h_zero, fwd_chain]; exact h_in_bwd0
    · have h_GG := SetMaximalConsistent.allFuture_allFuture (bwd_chain M0 h0 ((-t).toNat)).property hchi
      have h_in_bwd0 := bwd_chain_reverse_g M0 h0 (show 0 < ((-t).toNat) by omega) h_GG
      simp only [bwd_chain] at h_in_bwd0
      exact fwd_chain_g_content_trans M0 h0 h_pos h_in_bwd0
  · exact bwd_chain_reverse_g M0 h0 (by omega)

theorem int_chain_forward_G (M0 : Set (Formula Atom)) (h0 : SetMaximalConsistent FrameClass.Base M0)
    (t t' : Int) (phi : Formula Atom) (h_lt : t < t')
    (h_G : Formula.allFuture phi ∈ int_chain M0 h0 t) :
    phi ∈ int_chain M0 h0 t' :=
  int_chain_g_content M0 h0 h_lt h_G

theorem int_chain_h_content (M0 : Set (Formula Atom)) (h0 : SetMaximalConsistent FrameClass.Base M0)
    {t t' : Int} (h_lt : t < t') :
    h_content (int_chain M0 h0 t') ⊆ int_chain M0 h0 t :=
  g_content_subset_implies_h_content_reverse _ _ (int_chain_mcs M0 h0 t) (int_chain_mcs M0 h0 t')
    (int_chain_g_content M0 h0 h_lt)

theorem int_chain_backward_H (M0 : Set (Formula Atom)) (h0 : SetMaximalConsistent FrameClass.Base M0)
    (t t' : Int) (phi : Formula Atom) (h_lt : t' < t)
    (h_H : Formula.allPast phi ∈ int_chain M0 h0 t) :
    phi ∈ int_chain M0 h0 t' :=
  int_chain_h_content M0 h0 h_lt h_H

/-! ## FMCS -/

noncomputable def bx_fmcs (M0 : Set (Formula Atom)) (h0 : SetMaximalConsistent FrameClass.Base M0) : FMCS Atom Int where
  mcs := int_chain M0 h0
  is_mcs := int_chain_mcs M0 h0
  forward_G := int_chain_forward_G M0 h0
  backward_H := int_chain_backward_H M0 h0

theorem bx_fmcs_at_zero (M0 : Set (Formula Atom)) (h0 : SetMaximalConsistent FrameClass.Base M0) :
    (bx_fmcs M0 h0).mcs 0 = M0 := int_chain_zero M0 h0

noncomputable def shifted_bx_fmcs (M0 : Set (Formula Atom)) (h0 : SetMaximalConsistent FrameClass.Base M0)
    (s : Int) : FMCS Atom Int where
  mcs t := int_chain M0 h0 (t - s)
  is_mcs t := int_chain_mcs M0 h0 (t - s)
  forward_G t t' phi h_lt h_G := int_chain_forward_G M0 h0 (t - s) (t' - s) phi (by omega) h_G
  backward_H t t' phi h_lt h_H := int_chain_backward_H M0 h0 (t - s) (t' - s) phi (by omega) h_H

theorem shifted_bx_fmcs_at_s (M0 : Set (Formula Atom)) (h0 : SetMaximalConsistent FrameClass.Base M0) (s : Int) :
    (shifted_bx_fmcs M0 h0 s).mcs s = M0 := by
  simp [shifted_bx_fmcs, int_chain_zero]

/-! ## Box Stability Along the Chain -/

theorem box_stable_in_int_chain (M0 : Set (Formula Atom)) (h0 : SetMaximalConsistent FrameClass.Base M0)
    (phi : Formula Atom) (t : Int) :
    Formula.box phi ∈ int_chain M0 h0 t ↔ Formula.box phi ∈ M0 := by
  constructor
  · intro h_box_t
    by_contra h_not_box_M0
    have h_neg_box_M0 : (Formula.box phi).neg ∈ M0 := by
      rcases SetMaximalConsistent.negation_complete h0 (Formula.box phi) with h | h
      · exact absurd h h_not_box_M0
      · exact h
    have h_box_neg : Formula.box (Formula.box phi).neg ∈ M0 :=
      SetMaximalConsistent.implication_property h0
        (theorem_in_mcs_fc' h0 (neg_box_to_box_neg_box phi)) h_neg_box_M0
    have h_box_neg_t : Formula.box (Formula.box phi).neg ∈ int_chain M0 h0 t := by
      rcases lt_trichotomy 0 t with h_pos | rfl | h_neg
      · exact int_chain_forward_G M0 h0 0 t _ h_pos
          (SetMaximalConsistent.implication_property h0
            (theorem_in_mcs_fc' h0 (temp_future_derived (Formula.box phi).neg)) h_box_neg)
      · rw [int_chain_zero]; exact h_box_neg
      · have h_box_box_neg := SetMaximalConsistent.implication_property h0
            (theorem_in_mcs_fc' h0 (DerivationTree.axiom [] _ (Axiom.modal_4 (Formula.box phi).neg) trivial)) h_box_neg
        exact int_chain_backward_H M0 h0 0 t _ h_neg
          (SetMaximalConsistent.implication_property h0
            (theorem_in_mcs_fc' h0 (Theorems.Perpetuity.box_to_past (Formula.box (Formula.box phi).neg))) h_box_box_neg)
    have h_neg_box_t : (Formula.box phi).neg ∈ int_chain M0 h0 t :=
      SetMaximalConsistent.implication_property (int_chain_mcs M0 h0 t)
        (theorem_in_mcs_fc' (int_chain_mcs M0 h0 t)
          (DerivationTree.axiom [] _ (Axiom.modal_t (Formula.box phi).neg) trivial))
        h_box_neg_t
    exact set_consistent_not_both (int_chain_mcs M0 h0 t).1 (Formula.box phi) h_box_t h_neg_box_t
  · intro h_box_M0
    rcases lt_trichotomy 0 t with h_pos | rfl | h_neg
    · exact int_chain_forward_G M0 h0 0 t _ h_pos
        (SetMaximalConsistent.implication_property h0
          (theorem_in_mcs_fc' h0 (temp_future_derived phi)) h_box_M0)
    · rw [int_chain_zero]; exact h_box_M0
    · have h_box_box := SetMaximalConsistent.implication_property h0
          (theorem_in_mcs_fc' h0 (DerivationTree.axiom [] _ (Axiom.modal_4 phi) trivial)) h_box_M0
      exact int_chain_backward_H M0 h0 0 t _ h_neg
        (SetMaximalConsistent.implication_property h0
          (theorem_in_mcs_fc' h0 (Theorems.Perpetuity.box_to_past (Formula.box phi))) h_box_box)

theorem box_stable_in_shifted_fmcs (M0 : Set (Formula Atom)) (h0 : SetMaximalConsistent FrameClass.Base M0)
    (phi : Formula Atom) (s t : Int) :
    Formula.box phi ∈ (shifted_bx_fmcs M0 h0 s).mcs t ↔ Formula.box phi ∈ M0 :=
  box_stable_in_int_chain M0 h0 phi (t - s)

/-! ## FC-Parametric Chain Construction -/

theorem g_content_fc_consistent {fc : FrameClass} {M : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc M) :
    SetConsistent fc (g_content M) := by
  have h_top : (Formula.bot.imp (Formula.bot : Formula Atom)) ∈ M :=
    theorem_in_mcs_fc' h_mcs (identity (Formula.bot : Formula Atom))
  have h_F_top : Formula.someFuture (Formula.bot.imp (Formula.bot : Formula Atom)) ∈ M :=
    SetMaximalConsistent.implication_property h_mcs
      (theorem_in_mcs_fc' h_mcs (DerivationTree.axiom [] _ Axiom.serial_future trivial)) h_top
  have h_seed := forward_temporal_witness_seed_consistent M h_mcs _ h_F_top
  intro L hL ⟨d⟩
  exact h_seed L (fun x hx => g_content_subset_forward_temporal_witness_seed M _ (hL x hx)) ⟨d⟩

theorem h_content_fc_consistent {fc : FrameClass} {M : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc M) :
    SetConsistent fc (h_content M) := by
  have h_top : (Formula.bot.imp (Formula.bot : Formula Atom)) ∈ M :=
    theorem_in_mcs_fc' h_mcs (identity (Formula.bot : Formula Atom))
  have h_P_top : Formula.somePast (Formula.bot.imp (Formula.bot : Formula Atom)) ∈ M :=
    SetMaximalConsistent.implication_property h_mcs
      (theorem_in_mcs_fc' h_mcs (DerivationTree.axiom [] _ Axiom.serial_past trivial)) h_top
  have h_seed := past_temporal_witness_seed_consistent M h_mcs _ h_P_top
  intro L hL ⟨d⟩
  exact h_seed L (fun x hx => h_content_subset_past_temporal_witness_seed M _ (hL x hx)) ⟨d⟩

/-! ### FC-Parametric Forward/Backward Steps -/

noncomputable def fwd_succ_fc {fc : FrameClass}
    (M : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc M) (psi : Formula Atom) :
    Set (Formula Atom) := by
  by_cases h_F : Formula.someFuture psi ∈ M
  · exact (set_lindenbaum_fc (forward_temporal_witness_seed_consistent M h_mcs psi h_F)).choose
  · exact (set_lindenbaum_fc (g_content_fc_consistent h_mcs)).choose

theorem fwd_succ_fc_mcs {fc : FrameClass}
    (M : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc M) (psi : Formula Atom) :
    SetMaximalConsistent fc (fwd_succ_fc M h_mcs psi) := by
  unfold fwd_succ_fc; split
  · exact (set_lindenbaum_fc (forward_temporal_witness_seed_consistent M h_mcs psi ‹_›)).choose_spec.2
  · exact (set_lindenbaum_fc (g_content_fc_consistent h_mcs)).choose_spec.2

theorem fwd_succ_fc_g_content {fc : FrameClass}
    (M : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc M) (psi : Formula Atom) :
    g_content M ⊆ fwd_succ_fc M h_mcs psi := by
  unfold fwd_succ_fc; split
  · exact fun chi hchi => (set_lindenbaum_fc (forward_temporal_witness_seed_consistent M h_mcs psi ‹_›)).choose_spec.1
      (Set.mem_union_right _ hchi)
  · exact fun chi hchi => (set_lindenbaum_fc (g_content_fc_consistent h_mcs)).choose_spec.1 hchi

theorem fwd_succ_fc_resolves {fc : FrameClass}
    (M : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc M) (psi : Formula Atom)
    (h_F : Formula.someFuture psi ∈ M) : psi ∈ fwd_succ_fc M h_mcs psi := by
  unfold fwd_succ_fc; rw [dif_pos h_F]
  exact (set_lindenbaum_fc (forward_temporal_witness_seed_consistent M h_mcs psi h_F)).choose_spec.1
    (Set.mem_union_left _ (Set.mem_singleton psi))

noncomputable def bwd_pred_fc {fc : FrameClass}
    (M : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc M) (psi : Formula Atom) :
    Set (Formula Atom) := by
  by_cases h_P : Formula.somePast psi ∈ M
  · exact (set_lindenbaum_fc (past_temporal_witness_seed_consistent M h_mcs psi h_P)).choose
  · exact (set_lindenbaum_fc (h_content_fc_consistent h_mcs)).choose

theorem bwd_pred_fc_mcs {fc : FrameClass}
    (M : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc M) (psi : Formula Atom) :
    SetMaximalConsistent fc (bwd_pred_fc M h_mcs psi) := by
  unfold bwd_pred_fc; split
  · exact (set_lindenbaum_fc (past_temporal_witness_seed_consistent M h_mcs psi ‹_›)).choose_spec.2
  · exact (set_lindenbaum_fc (h_content_fc_consistent h_mcs)).choose_spec.2

theorem bwd_pred_fc_h_content {fc : FrameClass}
    (M : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc M) (psi : Formula Atom) :
    h_content M ⊆ bwd_pred_fc M h_mcs psi := by
  unfold bwd_pred_fc; split
  · exact fun chi hchi => (set_lindenbaum_fc (past_temporal_witness_seed_consistent M h_mcs psi ‹_›)).choose_spec.1
      (Set.mem_union_right _ hchi)
  · exact fun chi hchi => (set_lindenbaum_fc (h_content_fc_consistent h_mcs)).choose_spec.1 hchi

theorem bwd_pred_fc_resolves {fc : FrameClass}
    (M : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc M) (psi : Formula Atom)
    (h_P : Formula.somePast psi ∈ M) : psi ∈ bwd_pred_fc M h_mcs psi := by
  unfold bwd_pred_fc; rw [dif_pos h_P]
  exact (set_lindenbaum_fc (past_temporal_witness_seed_consistent M h_mcs psi h_P)).choose_spec.1
    (Set.mem_union_left _ (Set.mem_singleton psi))

/-! ### FC-Parametric Chains -/

noncomputable def fwd_chain_fc {fc : FrameClass}
    (M0 : Set (Formula Atom)) (h0 : SetMaximalConsistent fc M0) :
    (n : Nat) → { M : Set (Formula Atom) // SetMaximalConsistent fc M }
  | 0 => ⟨M0, h0⟩
  | n + 1 =>
    let ⟨M, hM⟩ := fwd_chain_fc M0 h0 n
    ⟨fwd_succ_fc M hM (schedule n), fwd_succ_fc_mcs M hM (schedule n)⟩

noncomputable def bwd_chain_fc {fc : FrameClass}
    (M0 : Set (Formula Atom)) (h0 : SetMaximalConsistent fc M0) :
    (n : Nat) → { M : Set (Formula Atom) // SetMaximalConsistent fc M }
  | 0 => ⟨M0, h0⟩
  | n + 1 =>
    let ⟨M, hM⟩ := bwd_chain_fc M0 h0 n
    ⟨bwd_pred_fc M hM (schedule n), bwd_pred_fc_mcs M hM (schedule n)⟩

noncomputable def int_chain_fc {fc : FrameClass}
    (M0 : Set (Formula Atom)) (h0 : SetMaximalConsistent fc M0) (t : Int) :
    Set (Formula Atom) :=
  if t ≥ 0 then (fwd_chain_fc M0 h0 t.toNat).val
  else (bwd_chain_fc M0 h0 ((-t).toNat)).val

theorem int_chain_fc_zero {fc : FrameClass}
    (M0 : Set (Formula Atom)) (h0 : SetMaximalConsistent fc M0) :
    int_chain_fc M0 h0 0 = M0 := by simp [int_chain_fc, fwd_chain_fc]

theorem int_chain_fc_mcs {fc : FrameClass}
    (M0 : Set (Formula Atom)) (h0 : SetMaximalConsistent fc M0) (t : Int) :
    SetMaximalConsistent fc (int_chain_fc M0 h0 t) := by
  simp only [int_chain_fc]; split
  · exact (fwd_chain_fc M0 h0 t.toNat).property
  · exact (bwd_chain_fc M0 h0 ((-t).toNat)).property

/-! ### FC-Parametric G/H Content Propagation -/

theorem fwd_chain_fc_g_content_step {fc : FrameClass}
    (M0 : Set (Formula Atom)) (h0 : SetMaximalConsistent fc M0) (n : Nat) :
    g_content (fwd_chain_fc M0 h0 n).val ⊆ (fwd_chain_fc (fc := fc) M0 h0 (n + 1)).val :=
  fwd_succ_fc_g_content (fwd_chain_fc M0 h0 n).val (fwd_chain_fc M0 h0 n).property (schedule n)

theorem fwd_chain_fc_g_content_trans {fc : FrameClass}
    (M0 : Set (Formula Atom)) (h0 : SetMaximalConsistent fc M0)
    {m n : Nat} (h : m < n) :
    g_content (fwd_chain_fc M0 h0 m).val ⊆ (fwd_chain_fc (fc := fc) M0 h0 n).val := by
  induction n with
  | zero => exact absurd h (Nat.not_lt_zero m)
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp h) with rfl | h_lt
    · exact fwd_chain_fc_g_content_step M0 h0 m
    · intro phi hphi
      exact fwd_chain_fc_g_content_step M0 h0 n
        (ih h_lt (SetMaximalConsistent.allFuture_allFuture (fwd_chain_fc (fc := fc) M0 h0 m).property hphi))

theorem bwd_chain_fc_h_content_step {fc : FrameClass}
    (M0 : Set (Formula Atom)) (h0 : SetMaximalConsistent fc M0) (n : Nat) :
    h_content (bwd_chain_fc M0 h0 n).val ⊆ (bwd_chain_fc (fc := fc) M0 h0 (n + 1)).val :=
  bwd_pred_fc_h_content (bwd_chain_fc M0 h0 n).val (bwd_chain_fc M0 h0 n).property (schedule n)

theorem bwd_chain_fc_h_content_trans {fc : FrameClass}
    (M0 : Set (Formula Atom)) (h0 : SetMaximalConsistent fc M0)
    {m n : Nat} (h : m < n) :
    h_content (bwd_chain_fc M0 h0 m).val ⊆ (bwd_chain_fc (fc := fc) M0 h0 n).val := by
  induction n with
  | zero => exact absurd h (Nat.not_lt_zero m)
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp h) with rfl | h_lt
    · exact bwd_chain_fc_h_content_step M0 h0 m
    · intro phi hphi
      exact bwd_chain_fc_h_content_step M0 h0 n
        (ih h_lt (SetMaximalConsistent.allPast_allPast (bwd_chain_fc (fc := fc) M0 h0 m).property hphi))

theorem fwd_chain_fc_reverse_h {fc : FrameClass}
    (M0 : Set (Formula Atom)) (h0 : SetMaximalConsistent fc M0)
    {m n : Nat} (h : m < n) :
    h_content (fwd_chain_fc (fc := fc) M0 h0 n).val ⊆ (fwd_chain_fc M0 h0 m).val :=
  g_content_subset_implies_h_content_reverse _ _
    (mcs_to_base (fwd_chain_fc (fc := fc) M0 h0 m).property)
    (mcs_to_base (fwd_chain_fc (fc := fc) M0 h0 n).property)
    (fwd_chain_fc_g_content_trans M0 h0 h)

theorem bwd_chain_fc_reverse_g {fc : FrameClass}
    (M0 : Set (Formula Atom)) (h0 : SetMaximalConsistent fc M0)
    {m n : Nat} (h : m < n) :
    g_content (bwd_chain_fc (fc := fc) M0 h0 n).val ⊆ (bwd_chain_fc M0 h0 m).val :=
  h_content_subset_implies_g_content_reverse _ _
    (mcs_to_base (bwd_chain_fc (fc := fc) M0 h0 m).property)
    (mcs_to_base (bwd_chain_fc (fc := fc) M0 h0 n).property)
    (bwd_chain_fc_h_content_trans M0 h0 h)

theorem int_chain_fc_g_content {fc : FrameClass}
    (M0 : Set (Formula Atom)) (h0 : SetMaximalConsistent fc M0)
    {t t' : Int} (h_lt : t < t') :
    g_content (int_chain_fc M0 h0 t) ⊆ int_chain_fc (fc := fc) M0 h0 t' := by
  simp only [int_chain_fc]
  split_ifs with ht ht'
  · exact fwd_chain_fc_g_content_trans M0 h0 (by omega)
  · omega
  · intro chi hchi
    rcases Nat.eq_zero_or_pos t'.toNat with h_zero | h_pos
    · have h_in := bwd_chain_fc_reverse_g M0 h0 (show 0 < ((-t).toNat) by omega) hchi
      simp only [bwd_chain_fc] at h_in; simp only [h_zero, fwd_chain_fc]; exact h_in
    · have h_GG := SetMaximalConsistent.allFuture_allFuture (bwd_chain_fc (fc := fc) M0 h0 ((-t).toNat)).property hchi
      have h_in := bwd_chain_fc_reverse_g M0 h0 (show 0 < ((-t).toNat) by omega) h_GG
      simp only [bwd_chain_fc] at h_in
      exact fwd_chain_fc_g_content_trans M0 h0 h_pos h_in
  · exact bwd_chain_fc_reverse_g M0 h0 (by omega)

theorem int_chain_fc_forward_G {fc : FrameClass}
    (M0 : Set (Formula Atom)) (h0 : SetMaximalConsistent fc M0)
    (t t' : Int) (phi : Formula Atom) (h_lt : t < t')
    (h_G : Formula.allFuture phi ∈ int_chain_fc (fc := fc) M0 h0 t) :
    phi ∈ int_chain_fc M0 h0 t' :=
  int_chain_fc_g_content M0 h0 h_lt h_G

theorem int_chain_fc_h_content {fc : FrameClass}
    (M0 : Set (Formula Atom)) (h0 : SetMaximalConsistent fc M0)
    {t t' : Int} (h_lt : t < t') :
    h_content (int_chain_fc (fc := fc) M0 h0 t') ⊆ int_chain_fc M0 h0 t :=
  g_content_subset_implies_h_content_reverse _ _
    (mcs_to_base (int_chain_fc_mcs M0 h0 t))
    (mcs_to_base (int_chain_fc_mcs M0 h0 t'))
    (int_chain_fc_g_content M0 h0 h_lt)

theorem int_chain_fc_backward_H {fc : FrameClass}
    (M0 : Set (Formula Atom)) (h0 : SetMaximalConsistent fc M0)
    (t t' : Int) (phi : Formula Atom) (h_lt : t' < t)
    (h_H : Formula.allPast phi ∈ int_chain_fc (fc := fc) M0 h0 t) :
    phi ∈ int_chain_fc M0 h0 t' :=
  int_chain_fc_h_content M0 h0 h_lt h_H

/-! ### FC-Parametric FMCS -/

noncomputable def bx_fmcs_fc {fc : FrameClass}
    (M0 : Set (Formula Atom)) (h0 : SetMaximalConsistent fc M0) : FMCS Atom Int fc where
  mcs := int_chain_fc M0 h0
  is_mcs := int_chain_fc_mcs M0 h0
  forward_G := int_chain_fc_forward_G M0 h0
  backward_H := int_chain_fc_backward_H M0 h0

noncomputable def shifted_bx_fmcs_fc {fc : FrameClass}
    (M0 : Set (Formula Atom)) (h0 : SetMaximalConsistent fc M0)
    (s : Int) : FMCS Atom Int fc where
  mcs t := int_chain_fc M0 h0 (t - s)
  is_mcs t := int_chain_fc_mcs M0 h0 (t - s)
  forward_G t t' phi h_lt h_G := int_chain_fc_forward_G M0 h0 (t - s) (t' - s) phi (by omega) h_G
  backward_H t t' phi h_lt h_H := int_chain_fc_backward_H M0 h0 (t - s) (t' - s) phi (by omega) h_H

theorem shifted_bx_fmcs_fc_at_s {fc : FrameClass}
    (M0 : Set (Formula Atom)) (h0 : SetMaximalConsistent fc M0) (s : Int) :
    (shifted_bx_fmcs_fc M0 h0 s).mcs s = M0 := by
  simp [shifted_bx_fmcs_fc, int_chain_fc_zero]

/-! ### FC-Parametric Box Stability -/

theorem box_stable_in_int_chain_fc {fc : FrameClass}
    (M0 : Set (Formula Atom)) (h0 : SetMaximalConsistent fc M0)
    (phi : Formula Atom) (t : Int) :
    Formula.box phi ∈ int_chain_fc (fc := fc) M0 h0 t ↔ Formula.box phi ∈ M0 := by
  constructor
  · intro h_box_t
    by_contra h_not
    have h_neg_box : (Formula.box phi).neg ∈ M0 := by
      rcases SetMaximalConsistent.negation_complete h0 (Formula.box phi) with h | h
      · exact absurd h h_not
      · exact h
    have h_box_neg := SetMaximalConsistent.implication_property h0
      (theorem_in_mcs_fc' h0 (liftBase fc (neg_box_to_box_neg_box phi))) h_neg_box
    have h_box_neg_t : Formula.box (Formula.box phi).neg ∈ int_chain_fc (fc := fc) M0 h0 t := by
      rcases lt_trichotomy 0 t with h_pos | rfl | h_neg
      · exact int_chain_fc_forward_G M0 h0 0 t _ h_pos
          (SetMaximalConsistent.implication_property h0
            (theorem_in_mcs_fc' h0 (liftBase fc (temp_future_derived (Formula.box phi).neg))) h_box_neg)
      · rw [int_chain_fc_zero]; exact h_box_neg
      · have h_bb := SetMaximalConsistent.implication_property h0
            (theorem_in_mcs_fc' h0 (DerivationTree.axiom [] _ (Axiom.modal_4 (Formula.box phi).neg) trivial)) h_box_neg
        exact int_chain_fc_backward_H M0 h0 0 t _ h_neg
          (SetMaximalConsistent.implication_property h0
            (theorem_in_mcs_fc' h0 (liftBase fc (Theorems.Perpetuity.box_to_past (Formula.box (Formula.box phi).neg)))) h_bb)
    have h_neg_box_t := SetMaximalConsistent.implication_property (int_chain_fc_mcs M0 h0 t)
      (theorem_in_mcs_fc' (int_chain_fc_mcs M0 h0 t)
        (DerivationTree.axiom [] _ (Axiom.modal_t (Formula.box phi).neg) trivial)) h_box_neg_t
    exact set_consistent_not_both (int_chain_fc_mcs (fc := fc) M0 h0 t).1 (Formula.box phi) h_box_t h_neg_box_t
  · intro h_box
    rcases lt_trichotomy 0 t with h_pos | rfl | h_neg
    · exact int_chain_fc_forward_G M0 h0 0 t _ h_pos
        (SetMaximalConsistent.implication_property h0
          (theorem_in_mcs_fc' h0 (liftBase fc (temp_future_derived phi))) h_box)
    · rw [int_chain_fc_zero]; exact h_box
    · have h_bb := SetMaximalConsistent.implication_property h0
          (theorem_in_mcs_fc' h0 (DerivationTree.axiom [] _ (Axiom.modal_4 phi) trivial)) h_box
      exact int_chain_fc_backward_H M0 h0 0 t _ h_neg
        (SetMaximalConsistent.implication_property h0
          (theorem_in_mcs_fc' h0 (liftBase fc (Theorems.Perpetuity.box_to_past (Formula.box phi)))) h_bb)

theorem box_stable_in_shifted_fmcs_fc {fc : FrameClass}
    (M0 : Set (Formula Atom)) (h0 : SetMaximalConsistent fc M0)
    (phi : Formula Atom) (s t : Int) :
    Formula.box phi ∈ (shifted_bx_fmcs_fc M0 h0 s).mcs t ↔ Formula.box phi ∈ M0 :=
  box_stable_in_int_chain_fc M0 h0 phi (t - s)

/-! ## Henkin BFMCS on Int -/

noncomputable def henkin_bfmcs (fc : FrameClass) (A : Set (Formula Atom))
    (h_mcs : SetMaximalConsistent fc A) :
    BFMCS Atom ℤ fc where
  families := { fam | ∃ (N : Set (Formula Atom)) (h_N : SetMaximalConsistent fc N)
    (s : ℤ),
    (∀ psi, Formula.box psi ∈ A ↔ Formula.box psi ∈ N) ∧
    fam = shifted_bx_fmcs_fc N h_N s }
  nonempty := ⟨shifted_bx_fmcs_fc A h_mcs 0, A, h_mcs, 0, fun _ => Iff.rfl, rfl⟩
  modal_forward := by
    intro fam hfam phi t h_box fam' hfam'
    obtain ⟨N, h_N, s, h_eqN, rfl⟩ := hfam
    obtain ⟨N', h_N', s', h_eqN', rfl⟩ := hfam'
    have h_box_N := (box_stable_in_shifted_fmcs_fc N h_N phi s t).mp h_box
    have h_box_A := (h_eqN phi).mpr h_box_N
    have h_box_N' := (h_eqN' phi).mp h_box_A
    have h_box_t' := (box_stable_in_shifted_fmcs_fc N' h_N' phi s' t).mpr h_box_N'
    exact SetMaximalConsistent.implication_property
      ((shifted_bx_fmcs_fc N' h_N' s').is_mcs t)
      (theorem_in_mcs_fc' ((shifted_bx_fmcs_fc N' h_N' s').is_mcs t)
        (DerivationTree.axiom [] _ (Axiom.modal_t phi) trivial)) h_box_t'
  modal_backward := by
    intro fam hfam phi t h_all
    obtain ⟨N, h_N, s, h_eqN, rfl⟩ := hfam
    suffices h_box_N : Formula.box phi ∈ N from
      (box_stable_in_shifted_fmcs_fc N h_N phi s t).mpr h_box_N
    suffices h_box_A : Formula.box phi ∈ A from (h_eqN phi).mp h_box_A
    by_contra h_not_box
    have h_neg_box : (Formula.box phi).neg ∈ A := by
      rcases SetMaximalConsistent.negation_complete h_mcs (Formula.box phi) with h | h
      · exact absurd h h_not_box
      · exact h
    have h_diamond_neg : (Formula.neg phi).diamond ∈ A :=
      SetMaximalConsistent.contrapositive_lemma h_mcs
        (liftBase fc (box_dne_theorem phi)) h_neg_box
    obtain ⟨v, h_v_mcs, h_equiv, h_neg_phi_v⟩ := bx_modal_witness_fc h_mcs (Formula.neg phi) h_diamond_neg
    have h_fam_v_mem : shifted_bx_fmcs_fc v h_v_mcs t ∈
        { fam | ∃ (N : Set (Formula Atom)) (h_N : SetMaximalConsistent fc N) (s : ℤ),
          (∀ psi, Formula.box psi ∈ A ↔ Formula.box psi ∈ N) ∧
          fam = shifted_bx_fmcs_fc N h_N s } :=
      ⟨v, h_v_mcs, t, fun psi => h_equiv psi, rfl⟩
    have h_phi_v := h_all (shifted_bx_fmcs_fc v h_v_mcs t) h_fam_v_mem
    rw [shifted_bx_fmcs_fc_at_s] at h_phi_v
    exact set_consistent_not_both h_v_mcs.1 phi h_phi_v h_neg_phi_v
  eval_family := shifted_bx_fmcs_fc A h_mcs 0
  eval_family_mem := ⟨A, h_mcs, 0, fun _ => Iff.rfl, rfl⟩

end Cslib.Logic.Bimodal.Metalogic.BXCanonical.CanonicalModel
