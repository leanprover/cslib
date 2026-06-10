/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import Cslib.Logics.Bimodal.Metalogic.Core.MaximalConsistent
import Cslib.Logics.Bimodal.Metalogic.Core.MCSProperties
import Cslib.Logics.Bimodal.Metalogic.Bundle.TemporalContent
import Cslib.Logics.Bimodal.Metalogic.Bundle.WitnessSeed
import Cslib.Logics.Bimodal.Metalogic.Bundle.CanonicalFrame
import Cslib.Logics.Bimodal.Syntax.Formula
import Cslib.Logics.Bimodal.Theorems.GeneralizedNecessitation
import Cslib.Logics.Bimodal.Theorems.Combinators
import Cslib.Logics.Bimodal.Theorems.Propositional.Core
import Cslib.Logics.Bimodal.Theorems.Propositional.Connectives

/-!
# BX Canonical Frame

Defines the canonical frame for BX completeness.

## References

* Ported from BimodalLogic/Theories/Bimodal/Metalogic/BXCanonical/Frame.lean
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Cslib.Logic.Bimodal.Metalogic.BXCanonical

open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Metalogic.Core
open Cslib.Logic.Bimodal.Metalogic.Bundle

attribute [local instance] Classical.propDecidable

variable {Atom : Type*}

/-! ## BX Canonical Point -/

structure BXPoint (Atom : Type*) where
  formulas : Set (Formula Atom)
  is_mcs : SetMaximalConsistent FrameClass.Base formulas

/-! ## Canonical Temporal Ordering -/

def bx_le (w v : BXPoint Atom) : Prop :=
  g_content w.formulas ⊆ v.formulas

def bx_modal_equiv (w v : BXPoint Atom) : Prop :=
  ∀ φ : Formula Atom, Formula.box φ ∈ w.formulas ↔ Formula.box φ ∈ v.formulas

/-! ## Key Helper: g_content Closed Under Derivation -/

noncomputable def g_content_closed_derivation {Omega : Set (Formula Atom)} {φ : Formula Atom}
    (h_mcs : SetMaximalConsistent FrameClass.Base Omega)
    (L : List (Formula Atom)) (h_sub : ∀ ψ ∈ L, ψ ∈ g_content Omega)
    (h_deriv : DerivationTree FrameClass.Base L φ) : Formula.allFuture φ ∈ Omega := by
  have d_G : DerivationTree FrameClass.Base (Context.map Formula.allFuture L) (Formula.allFuture φ) :=
    Theorems.generalized_temporal_k L φ h_deriv
  have h_GL_in : ∀ f ∈ Context.map Formula.allFuture L, f ∈ Omega := by
    intro f hf
    rw [Context.mem_map_iff] at hf
    obtain ⟨ψ, hψ_in, hψ_eq⟩ := hf
    rw [← hψ_eq]
    exact h_sub ψ hψ_in
  exact SetMaximalConsistent.closed_under_derivation h_mcs
    (Context.map Formula.allFuture L) h_GL_in d_G

noncomputable def h_content_closed_derivation {Omega : Set (Formula Atom)} {φ : Formula Atom}
    (h_mcs : SetMaximalConsistent FrameClass.Base Omega)
    (L : List (Formula Atom)) (h_sub : ∀ ψ ∈ L, ψ ∈ h_content Omega)
    (h_deriv : DerivationTree FrameClass.Base L φ) : Formula.allPast φ ∈ Omega := by
  have d_H : DerivationTree FrameClass.Base (Context.map Formula.allPast L) (Formula.allPast φ) :=
    Theorems.generalized_past_k L φ h_deriv
  have h_HL_in : ∀ f ∈ Context.map Formula.allPast L, f ∈ Omega := by
    intro f hf
    rw [Context.mem_map_iff] at hf
    obtain ⟨ψ, hψ_in, hψ_eq⟩ := hf
    rw [← hψ_eq]
    exact h_sub ψ hψ_in
  exact SetMaximalConsistent.closed_under_derivation h_mcs
    (Context.map Formula.allPast L) h_HL_in d_H

/-! ## g_content / h_content Set Consistent -/

private noncomputable def theorem_in_mcs_fc {M : Set (Formula Atom)} {phi : Formula Atom}
    (h_mcs : SetMaximalConsistent FrameClass.Base M)
    (h_deriv : DerivationTree FrameClass.Base [] phi) : phi ∈ M :=
  SetMaximalConsistent.closed_under_derivation h_mcs [] (fun _ h => by simp at h) h_deriv

theorem g_content_set_consistent {Omega : Set (Formula Atom)} (h_mcs : SetMaximalConsistent FrameClass.Base Omega) :
    SetConsistent FrameClass.Base (g_content Omega) := by
  intro L hL ⟨d⟩
  have h_G_bot : Formula.allFuture (Formula.bot : Formula Atom) ∈ Omega :=
    g_content_closed_derivation h_mcs L hL d
  let neg_top : Formula Atom := ((Formula.bot : Formula Atom).imp (Formula.bot : Formula Atom)).imp (Formula.bot : Formula Atom)
  have h_ef : DerivationTree FrameClass.Base [] ((Formula.bot : Formula Atom).imp neg_top) :=
    DerivationTree.axiom [] _ (Axiom.efq neg_top) trivial
  have h_G_ef : DerivationTree FrameClass.Base [] (Formula.allFuture ((Formula.bot : Formula Atom).imp neg_top)) :=
    DerivationTree.temporal_necessitation _ h_ef
  have h_kd : DerivationTree FrameClass.Base [] (((Formula.bot : Formula Atom).imp neg_top).allFuture.imp
    ((Formula.bot : Formula Atom).allFuture.imp neg_top.allFuture)) :=
    Theorems.TemporalDerived.temp_k_dist_derived (Formula.bot : Formula Atom) neg_top
  have h1 := theorem_in_mcs_fc h_mcs h_G_ef
  have h2 := theorem_in_mcs_fc h_mcs h_kd
  have h3 := SetMaximalConsistent.implication_property h_mcs h2 h1
  have h_G_neg_top : neg_top.allFuture ∈ Omega :=
    SetMaximalConsistent.implication_property h_mcs h3 h_G_bot
  have h_serial : DerivationTree FrameClass.Base [] ((Formula.top : Formula Atom).imp
    (Formula.someFuture (Formula.top : Formula Atom))) :=
    DerivationTree.axiom [] _ Axiom.serial_future trivial
  have h_serial_in := theorem_in_mcs_fc h_mcs h_serial
  have h_top : DerivationTree FrameClass.Base [] (Formula.top : Formula Atom) :=
    DerivationTree.axiom [] _ (Axiom.efq (Formula.bot : Formula Atom)) trivial
  have h_top_in := theorem_in_mcs_fc h_mcs h_top
  have h_F_top : Formula.someFuture (Formula.top : Formula Atom) ∈ Omega :=
    SetMaximalConsistent.implication_property h_mcs h_serial_in h_top_in
  exact someFuture_allFuture_neg_absurd h_mcs (Formula.top : Formula Atom) h_F_top h_G_neg_top

theorem h_content_set_consistent {Omega : Set (Formula Atom)} (h_mcs : SetMaximalConsistent FrameClass.Base Omega) :
    SetConsistent FrameClass.Base (h_content Omega) := by
  intro L hL ⟨d⟩
  have h_H_bot : Formula.allPast (Formula.bot : Formula Atom) ∈ Omega :=
    h_content_closed_derivation h_mcs L hL d
  let neg_top : Formula Atom := ((Formula.bot : Formula Atom).imp (Formula.bot : Formula Atom)).imp (Formula.bot : Formula Atom)
  have h_ef : DerivationTree FrameClass.Base [] ((Formula.bot : Formula Atom).imp neg_top) :=
    DerivationTree.axiom [] _ (Axiom.efq neg_top) trivial
  have h_H_ef : DerivationTree FrameClass.Base [] (Formula.allPast ((Formula.bot : Formula Atom).imp neg_top)) :=
    Theorems.past_necessitation _ h_ef
  have h_kd : DerivationTree FrameClass.Base [] (((Formula.bot : Formula Atom).imp neg_top).allPast.imp
    ((Formula.bot : Formula Atom).allPast.imp neg_top.allPast)) :=
    Theorems.past_k_dist (Formula.bot : Formula Atom) neg_top
  have h1 := theorem_in_mcs_fc h_mcs h_H_ef
  have h2 := theorem_in_mcs_fc h_mcs h_kd
  have h3 := SetMaximalConsistent.implication_property h_mcs h2 h1
  have h_H_neg_top : neg_top.allPast ∈ Omega :=
    SetMaximalConsistent.implication_property h_mcs h3 h_H_bot
  have h_serial : DerivationTree FrameClass.Base [] ((Formula.top : Formula Atom).imp
    (Formula.somePast (Formula.top : Formula Atom))) :=
    DerivationTree.axiom [] _ Axiom.serial_past trivial
  have h_serial_in := theorem_in_mcs_fc h_mcs h_serial
  have h_top : DerivationTree FrameClass.Base [] (Formula.top : Formula Atom) :=
    DerivationTree.axiom [] _ (Axiom.efq (Formula.bot : Formula Atom)) trivial
  have h_top_in := theorem_in_mcs_fc h_mcs h_top
  have h_P_top : Formula.somePast (Formula.top : Formula Atom) ∈ Omega :=
    SetMaximalConsistent.implication_property h_mcs h_serial_in h_top_in
  exact somePast_allPast_neg_absurd h_mcs (Formula.top : Formula Atom) h_P_top h_H_neg_top

/-! ## Reflexivity (sorry'd under irreflexive semantics) -/

theorem bx_le_refl (w : BXPoint Atom) : bx_le w w := by
  sorry

/-! ## Transitivity -/

theorem bx_le_trans {w u v : BXPoint Atom} (hwu : bx_le w u) (huv : bx_le u v) :
    bx_le w v := by
  intro φ hφ
  have h_GGφ := SetMaximalConsistent.allFuture_allFuture w.is_mcs hφ
  exact huv (hwu h_GGφ)

/-! ## Forward/Backward Temporal Witnesses -/

noncomputable def bx_forward_witness (w : BXPoint Atom) (ψ : Formula Atom)
    (h_F : Formula.someFuture ψ ∈ w.formulas) :
    ∃ v : BXPoint Atom, bx_le w v ∧ ψ ∈ v.formulas := by
  have h_seed_cons := forward_temporal_witness_seed_consistent w.formulas w.is_mcs ψ h_F
  obtain ⟨M, hM_sup, hM_mcs⟩ := set_lindenbaum_base h_seed_cons
  exact ⟨⟨M, hM_mcs⟩,
    fun χ hχ => hM_sup (Set.mem_union_right _ hχ),
    hM_sup (Set.mem_union_left _ (Set.mem_singleton ψ))⟩

noncomputable def bx_backward_witness (w : BXPoint Atom) (ψ : Formula Atom)
    (h_P : Formula.somePast ψ ∈ w.formulas) :
    ∃ v : BXPoint Atom, bx_le v w ∧ ψ ∈ v.formulas := by
  have h_seed_cons := past_temporal_witness_seed_consistent w.formulas w.is_mcs ψ h_P
  obtain ⟨M, hM_sup, hM_mcs⟩ := set_lindenbaum_base h_seed_cons
  have h_h_sub : h_content w.formulas ⊆ M :=
    fun χ hχ => hM_sup (Set.mem_union_right _ hχ)
  exact ⟨⟨M, hM_mcs⟩,
    h_content_subset_implies_g_content_reverse w.formulas M w.is_mcs hM_mcs h_h_sub,
    hM_sup (Set.mem_union_left _ (Set.mem_singleton ψ))⟩

/-! ## G-content Forward and Backward -/

theorem bx_G_forward {w v : BXPoint Atom} {φ : Formula Atom}
    (h_le : bx_le w v) (h_G : Formula.allFuture φ ∈ w.formulas) :
    φ ∈ v.formulas :=
  h_le h_G

noncomputable def bx_G_backward (w : BXPoint Atom) (φ : Formula Atom)
    (h_not_G : Formula.allFuture φ ∉ w.formulas) :
    ∃ v : BXPoint Atom, bx_le w v ∧ φ ∉ v.formulas := by
  have h_seed_cons : SetConsistent FrameClass.Base ({Formula.neg φ} ∪ g_content w.formulas : Set (Formula Atom)) := by
    intro L hL ⟨d⟩
    by_cases h_negφ_in : Formula.neg φ ∈ L
    · let L_filt := L.filter (fun y => decide (y ≠ Formula.neg φ))
      have d_reord : DerivationTree FrameClass.Base (Formula.neg φ :: L_filt) (Formula.bot : Formula Atom) :=
        derivation_exchange d (fun x => (cons_filter_neq_perm h_negφ_in x).symm)
      have d_negneg : DerivationTree FrameClass.Base L_filt (Formula.neg (Formula.neg φ)) :=
        deduction_theorem L_filt (Formula.neg φ) (Formula.bot : Formula Atom) d_reord
      have h_filt_in_g : ∀ ψ ∈ L_filt, ψ ∈ g_content w.formulas := by
        intro ψ hψ
        have h_and := List.mem_filter.mp hψ
        have h_ne : ψ ≠ Formula.neg φ := by simpa using h_and.2
        have h_mem := hL ψ h_and.1
        simp only [Set.mem_union, Set.mem_singleton_iff] at h_mem
        rcases h_mem with rfl | h
        · exact absurd rfl h_ne
        · exact h
      have h_dne : DerivationTree FrameClass.Base [] ((Formula.neg (Formula.neg φ)).imp φ) :=
        Theorems.Propositional.double_negation φ
      have d_dne_weak : DerivationTree FrameClass.Base L_filt ((Formula.neg (Formula.neg φ)).imp φ) :=
        DerivationTree.weakening [] L_filt _ h_dne (List.nil_subset _)
      have d_phi : DerivationTree FrameClass.Base L_filt φ :=
        DerivationTree.modus_ponens L_filt _ _ d_dne_weak d_negneg
      have h_Gφ := g_content_closed_derivation w.is_mcs L_filt h_filt_in_g d_phi
      exact h_not_G h_Gφ
    · have h_L_in_g : ∀ ψ ∈ L, ψ ∈ g_content w.formulas := by
        intro ψ hψ
        have h_mem := hL ψ hψ
        simp only [Set.mem_union, Set.mem_singleton_iff] at h_mem
        rcases h_mem with rfl | h
        · exact absurd hψ h_negφ_in
        · exact h
      exact g_content_set_consistent w.is_mcs L h_L_in_g ⟨d⟩
  obtain ⟨M, hM_sup, hM_mcs⟩ := set_lindenbaum_base h_seed_cons
  exact ⟨⟨M, hM_mcs⟩,
    fun χ hχ => hM_sup (Set.mem_union_right _ hχ),
    SetMaximalConsistent.neg_excludes hM_mcs φ
      (hM_sup (Set.mem_union_left _ (Set.mem_singleton _)))⟩

/-! ## H-content Forward and Backward -/

theorem bx_H_forward {w v : BXPoint Atom} {φ : Formula Atom}
    (h_le : bx_le v w) (h_H : Formula.allPast φ ∈ w.formulas) :
    φ ∈ v.formulas :=
  g_content_subset_implies_h_content_reverse v.formulas w.formulas
    v.is_mcs w.is_mcs h_le h_H

noncomputable def bx_H_backward (w : BXPoint Atom) (φ : Formula Atom)
    (h_not_H : Formula.allPast φ ∉ w.formulas) :
    ∃ v : BXPoint Atom, bx_le v w ∧ φ ∉ v.formulas := by
  have h_seed_cons : SetConsistent FrameClass.Base ({Formula.neg φ} ∪ h_content w.formulas : Set (Formula Atom)) := by
    intro L hL ⟨d⟩
    by_cases h_negφ_in : Formula.neg φ ∈ L
    · let L_filt := L.filter (fun y => decide (y ≠ Formula.neg φ))
      have d_reord : DerivationTree FrameClass.Base (Formula.neg φ :: L_filt) (Formula.bot : Formula Atom) :=
        derivation_exchange d (fun x => (cons_filter_neq_perm h_negφ_in x).symm)
      have d_negneg : DerivationTree FrameClass.Base L_filt (Formula.neg (Formula.neg φ)) :=
        deduction_theorem L_filt (Formula.neg φ) (Formula.bot : Formula Atom) d_reord
      have h_filt_in_h : ∀ ψ ∈ L_filt, ψ ∈ h_content w.formulas := by
        intro ψ hψ
        have h_and := List.mem_filter.mp hψ
        have h_ne : ψ ≠ Formula.neg φ := by simpa using h_and.2
        have h_mem := hL ψ h_and.1
        simp only [Set.mem_union, Set.mem_singleton_iff] at h_mem
        rcases h_mem with rfl | h
        · exact absurd rfl h_ne
        · exact h
      have h_dne : DerivationTree FrameClass.Base [] ((Formula.neg (Formula.neg φ)).imp φ) :=
        Theorems.Propositional.double_negation φ
      have d_dne_weak : DerivationTree FrameClass.Base L_filt ((Formula.neg (Formula.neg φ)).imp φ) :=
        DerivationTree.weakening [] L_filt _ h_dne (List.nil_subset _)
      have d_phi : DerivationTree FrameClass.Base L_filt φ :=
        DerivationTree.modus_ponens L_filt _ _ d_dne_weak d_negneg
      have h_Hφ := h_content_closed_derivation w.is_mcs L_filt h_filt_in_h d_phi
      exact h_not_H h_Hφ
    · have h_L_in_h : ∀ ψ ∈ L, ψ ∈ h_content w.formulas := by
        intro ψ hψ
        have h_mem := hL ψ hψ
        simp only [Set.mem_union, Set.mem_singleton_iff] at h_mem
        rcases h_mem with rfl | h
        · exact absurd hψ h_negφ_in
        · exact h
      exact h_content_set_consistent w.is_mcs L h_L_in_h ⟨d⟩
  obtain ⟨M, hM_sup, hM_mcs⟩ := set_lindenbaum_base h_seed_cons
  have h_h_sub : h_content w.formulas ⊆ M :=
    fun χ hχ => hM_sup (Set.mem_union_right _ hχ)
  exact ⟨⟨M, hM_mcs⟩,
    h_content_subset_implies_g_content_reverse w.formulas M w.is_mcs hM_mcs h_h_sub,
    SetMaximalConsistent.neg_excludes hM_mcs φ
      (hM_sup (Set.mem_union_left _ (Set.mem_singleton _)))⟩

/-! ## Modal Equivalence Properties -/

theorem bx_modal_equiv_refl (w : BXPoint Atom) : bx_modal_equiv w w :=
  fun _ => Iff.rfl

theorem bx_modal_equiv_symm {w v : BXPoint Atom} (h : bx_modal_equiv w v) :
    bx_modal_equiv v w :=
  fun φ => (h φ).symm

theorem bx_modal_equiv_trans {w u v : BXPoint Atom}
    (hwu : bx_modal_equiv w u) (huv : bx_modal_equiv u v) :
    bx_modal_equiv w v :=
  fun φ => (hwu φ).trans (huv φ)

/-! ## Modal Witness -/

noncomputable def bx_modal_witness (w : BXPoint Atom) (ψ : Formula Atom)
    (h_dia : Formula.diamond ψ ∈ w.formulas) :
    ∃ v : BXPoint Atom, bx_modal_equiv w v ∧ ψ ∈ v.formulas := by
  let bc := {χ : Formula Atom | Formula.box χ ∈ w.formulas}
  have h_seed_cons : SetConsistent FrameClass.Base ({ψ} ∪ bc : Set (Formula Atom)) := by
    intro L hL ⟨d⟩
    by_cases h_ψ_in : ψ ∈ L
    · let L_filt := L.filter (fun y => decide (y ≠ ψ))
      have d_reord : DerivationTree FrameClass.Base (ψ :: L_filt) (Formula.bot : Formula Atom) :=
        derivation_exchange d (fun x => (cons_filter_neq_perm h_ψ_in x).symm)
      have d_neg : DerivationTree FrameClass.Base L_filt (Formula.neg ψ) :=
        deduction_theorem L_filt ψ (Formula.bot : Formula Atom) d_reord
      have h_filt_in_bc : ∀ χ ∈ L_filt, χ ∈ bc := by
        intro χ hχ
        have h_and := List.mem_filter.mp hχ
        have h_ne : χ ≠ ψ := by simpa using h_and.2
        have h_mem := hL χ h_and.1
        simp only [Set.mem_union, Set.mem_singleton_iff] at h_mem
        rcases h_mem with rfl | h
        · exact absurd rfl h_ne
        · exact h
      have d_box_neg : DerivationTree FrameClass.Base (Context.map Formula.box L_filt) (Formula.box (Formula.neg ψ)) :=
        Theorems.generalized_modal_k L_filt (Formula.neg ψ) d_neg
      have h_box_L_in : ∀ f ∈ Context.map Formula.box L_filt, f ∈ w.formulas := by
        intro f hf
        rw [Context.mem_map_iff] at hf
        obtain ⟨χ, hχ_in, hχ_eq⟩ := hf
        rw [← hχ_eq]
        exact h_filt_in_bc χ hχ_in
      have h_box_neg_in := SetMaximalConsistent.closed_under_derivation w.is_mcs
        (Context.map Formula.box L_filt) h_box_L_in d_box_neg
      have h_eq : Formula.diamond ψ = Formula.neg (Formula.box (Formula.neg ψ)) := rfl
      rw [h_eq] at h_dia
      exact set_consistent_not_both w.is_mcs.1 _ h_box_neg_in h_dia
    · have h_L_in_bc : ∀ χ ∈ L, χ ∈ bc := by
        intro χ hχ
        have h_mem := hL χ hχ
        simp only [Set.mem_union, Set.mem_singleton_iff] at h_mem
        rcases h_mem with rfl | h
        · exact absurd hχ h_ψ_in
        · exact h
      have d_box_bot : DerivationTree FrameClass.Base (Context.map Formula.box L) (Formula.box (Formula.bot : Formula Atom)) :=
        Theorems.generalized_modal_k L (Formula.bot : Formula Atom) d
      have h_box_L_in : ∀ f ∈ Context.map Formula.box L, f ∈ w.formulas := by
        intro f hf
        rw [Context.mem_map_iff] at hf
        obtain ⟨χ, hχ_in, hχ_eq⟩ := hf
        rw [← hχ_eq]
        exact h_L_in_bc χ hχ_in
      have h_box_bot_in := SetMaximalConsistent.closed_under_derivation w.is_mcs
        (Context.map Formula.box L) h_box_L_in d_box_bot
      have h_ax : DerivationTree FrameClass.Base [] (Formula.box (Formula.bot : Formula Atom) |>.imp (Formula.bot : Formula Atom)) :=
        DerivationTree.axiom [] _ (Axiom.modal_t (Formula.bot : Formula Atom)) trivial
      have h_bot := SetMaximalConsistent.implication_property w.is_mcs
        (theorem_in_mcs_fc w.is_mcs h_ax) h_box_bot_in
      exact w.is_mcs.1 [(Formula.bot : Formula Atom)] (fun χ hχ => by simp at hχ; rw [hχ]; exact h_bot)
        ⟨DerivationTree.assumption [(Formula.bot : Formula Atom)] (Formula.bot : Formula Atom) (by simp)⟩
  obtain ⟨M, hM_sup, hM_mcs⟩ := set_lindenbaum_base h_seed_cons
  have h_ψ_in : ψ ∈ M := hM_sup (Set.mem_union_left _ (Set.mem_singleton ψ))
  have h_bc_sub : bc ⊆ M := fun χ hχ => hM_sup (Set.mem_union_right _ hχ)
  have h_equiv : bx_modal_equiv w ⟨M, hM_mcs⟩ := by
    intro χ
    constructor
    · intro h_box
      have h_m4 : DerivationTree FrameClass.Base [] ((Formula.box χ).imp (Formula.box (Formula.box χ))) :=
        DerivationTree.axiom [] _ (Axiom.modal_4 χ) trivial
      have h_box_box := SetMaximalConsistent.implication_property w.is_mcs
        (theorem_in_mcs_fc w.is_mcs h_m4) h_box
      have h_in_bc : Formula.box χ ∈ bc := h_box_box
      exact h_bc_sub h_in_bc
    · intro h_box_M
      by_contra h_not_box
      have h_neg_box : (Formula.box χ).neg ∈ w.formulas := by
        cases SetMaximalConsistent.negation_complete w.is_mcs (Formula.box χ) with
        | inl h => exact absurd h h_not_box
        | inr h => exact h
      have h_m5 : DerivationTree FrameClass.Base [] ((Formula.box χ).neg.box.neg.imp (Formula.box χ)) :=
        DerivationTree.axiom [] _ (Axiom.modal_5_collapse χ) trivial
      have h_contra : DerivationTree FrameClass.Base [] ((Formula.box χ).neg.imp (Formula.box χ).neg.box.neg.neg) :=
        Theorems.Propositional.contraposition h_m5
      have h_dne : DerivationTree FrameClass.Base [] ((Formula.box χ).neg.box.neg.neg.imp (Formula.box χ).neg.box) :=
        Theorems.Propositional.double_negation ((Formula.box χ).neg.box)
      have h_neg_intro : DerivationTree FrameClass.Base [] ((Formula.box χ).neg.imp (Formula.box χ).neg.box) :=
        Theorems.Combinators.imp_trans h_contra h_dne
      have h_box_neg_box := SetMaximalConsistent.implication_property w.is_mcs
        (theorem_in_mcs_fc w.is_mcs h_neg_intro) h_neg_box
      have h_in_bc : (Formula.box χ).neg ∈ bc := h_box_neg_box
      have h_neg_in_M := h_bc_sub h_in_bc
      exact set_consistent_not_both hM_mcs.1 (Formula.box χ) h_box_M h_neg_in_M
  exact ⟨⟨M, hM_mcs⟩, h_equiv, h_ψ_in⟩

/-! ## Box Preservation Along bx_le -/

noncomputable def neg_box_to_box_neg_box' (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] ((Formula.box φ).neg.imp (Formula.box (Formula.box φ).neg)) := by
  have h_m5 : DerivationTree FrameClass.Base [] ((Formula.box φ).neg.box.neg.imp (Formula.box φ)) :=
    DerivationTree.axiom [] _ (Axiom.modal_5_collapse φ) trivial
  have h_contra : DerivationTree FrameClass.Base [] ((Formula.box φ).neg.imp (Formula.box φ).neg.box.neg.neg) :=
    Theorems.Propositional.contraposition h_m5
  have h_dne : DerivationTree FrameClass.Base [] ((Formula.box φ).neg.box.neg.neg.imp (Formula.box φ).neg.box) :=
    Theorems.Propositional.double_negation ((Formula.box φ).neg.box)
  exact Theorems.Combinators.imp_trans h_contra h_dne

theorem box_preserved_along_bx_le {w v : BXPoint Atom} (h_le : bx_le w v) (φ : Formula Atom) :
    Formula.box φ ∈ w.formulas ↔ Formula.box φ ∈ v.formulas := by
  constructor
  · intro h_box
    have h_tf : DerivationTree FrameClass.Base [] ((Formula.box φ).imp (Formula.allFuture (Formula.box φ))) :=
      Theorems.Combinators.temp_future_derived φ
    have h_G_box := SetMaximalConsistent.implication_property w.is_mcs
      (theorem_in_mcs_fc w.is_mcs h_tf) h_box
    exact bx_G_forward h_le h_G_box
  · intro h_box_v
    by_contra h_not_box
    have h_neg_box : (Formula.box φ).neg ∈ w.formulas := by
      cases SetMaximalConsistent.negation_complete w.is_mcs (Formula.box φ) with
      | inl h => exact absurd h h_not_box
      | inr h => exact h
    have h_box_neg := SetMaximalConsistent.implication_property w.is_mcs
      (theorem_in_mcs_fc w.is_mcs (neg_box_to_box_neg_box' φ)) h_neg_box
    have h_tf2 : DerivationTree FrameClass.Base [] ((Formula.box (Formula.box φ).neg).imp
        (Formula.allFuture (Formula.box (Formula.box φ).neg))) :=
      Theorems.Combinators.temp_future_derived (Formula.box φ).neg
    have h_G_box_neg := SetMaximalConsistent.implication_property w.is_mcs
      (theorem_in_mcs_fc w.is_mcs h_tf2) h_box_neg
    have h_box_neg_v := bx_G_forward h_le h_G_box_neg
    have h_mt : DerivationTree FrameClass.Base [] ((Formula.box (Formula.box φ).neg).imp (Formula.box φ).neg) :=
      DerivationTree.axiom [] _ (Axiom.modal_t (Formula.box φ).neg) trivial
    have h_neg_v := SetMaximalConsistent.implication_property v.is_mcs
      (theorem_in_mcs_fc v.is_mcs h_mt) h_box_neg_v
    exact set_consistent_not_both v.is_mcs.1 (Formula.box φ) h_box_v h_neg_v

theorem bx_modal_equiv_of_bx_le {w v : BXPoint Atom} (h_le : bx_le w v) :
    bx_modal_equiv w v :=
  fun φ => box_preserved_along_bx_le h_le φ

/-! ## Eventuality Resolution for Until/Since -/

noncomputable def bx_until_eventuality_resolution
    (w : BXPoint Atom) (φ ψ : Formula Atom)
    (h_until : Formula.untl ψ φ ∈ w.formulas)
    (h_not_psi : ψ ∉ w.formulas) :
    ∃ v : BXPoint Atom, bx_le w v ∧ ψ ∈ v.formulas := by
  have h_F_psi : Formula.someFuture ψ ∈ w.formulas := by
    have h_ax : DerivationTree FrameClass.Base [] _ := DerivationTree.axiom [] _ (Axiom.until_F φ ψ) trivial
    exact SetMaximalConsistent.implication_property w.is_mcs
      (theorem_in_mcs_fc w.is_mcs h_ax) h_until
  exact bx_forward_witness w ψ h_F_psi

noncomputable def bx_since_eventuality_resolution
    (w : BXPoint Atom) (φ ψ : Formula Atom)
    (h_since : Formula.snce ψ φ ∈ w.formulas)
    (h_not_psi : ψ ∉ w.formulas) :
    ∃ v : BXPoint Atom, bx_le v w ∧ ψ ∈ v.formulas := by
  have h_P_psi : Formula.somePast ψ ∈ w.formulas := by
    have h_ax : DerivationTree FrameClass.Base [] _ := DerivationTree.axiom [] _ (Axiom.since_P φ ψ) trivial
    exact SetMaximalConsistent.implication_property w.is_mcs
      (theorem_in_mcs_fc w.is_mcs h_ax) h_since
  exact bx_backward_witness w ψ h_P_psi

end Cslib.Logic.Bimodal.Metalogic.BXCanonical
