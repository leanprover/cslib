/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/

import Cslib.Logics.Temporal.Metalogic.Chronicle.ChronicleTypes
import Cslib.Logics.Temporal.Metalogic.WitnessSeed
import Cslib.Logics.Temporal.Metalogic.CompletenessHelpers

/-!
# Temporal Canonical Frame

Defines TPoint, temporal ordering t_le, g/h-content closure properties,
witnesses, and eventuality resolution for the temporal chronicle construction.

## References

* Ported from Cslib/Logics/Bimodal/Metalogic/BXCanonical/Frame.lean
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option maxHeartbeats 800000

namespace Cslib.Logic.Temporal.Metalogic.Chronicle

open Cslib.Logic.Temporal
open Cslib.Logic.Temporal.Metalogic

attribute [local instance] Classical.propDecidable

variable {Atom : Type*}

/-! ## TPoint -/

/-- A temporal canonical point: an MCS of temporal formulas. -/
structure TPoint (Atom : Type*) where
  formulas : Set (Formula Atom)
  is_mcs : Temporal.SetMaximalConsistent formulas

/-! ## Canonical Temporal Ordering -/

/-- Temporal ordering: w ≤ v iff g_content(w) ⊆ v. -/
def t_le (w v : TPoint Atom) : Prop :=
  g_content w.formulas ⊆ v.formulas

/-! ## g/h-content Closed Under Derivation -/

private noncomputable def theorem_in_mcs {M : Set (Formula Atom)} {phi : Formula Atom}
    (h_mcs : Temporal.SetMaximalConsistent M)
    (h_deriv : DerivationTree FrameClass.Base [] phi) : phi ∈ M :=
  temporal_closed_under_derivation h_mcs (L := []) (fun _ h => by simp at h) ⟨h_deriv⟩

noncomputable def g_content_closed_derivation {Omega : Set (Formula Atom)} {φ : Formula Atom}
    (h_mcs : Temporal.SetMaximalConsistent Omega)
    (L : List (Formula Atom)) (h_sub : ∀ ψ ∈ L, ψ ∈ g_content Omega)
    (h_deriv : DerivationTree FrameClass.Base L φ) : Formula.all_future φ ∈ Omega := by
  have d_G := generalized_temporal_k L φ h_deriv
  have h_GL_in : ∀ f ∈ Context.map Formula.all_future L, f ∈ Omega := by
    intro f hf; rw [Context.mem_map_iff] at hf
    obtain ⟨ψ, hψ_in, hψ_eq⟩ := hf; rw [← hψ_eq]; exact h_sub ψ hψ_in
  exact temporal_closed_under_derivation h_mcs h_GL_in ⟨d_G⟩

noncomputable def h_content_closed_derivation {Omega : Set (Formula Atom)} {φ : Formula Atom}
    (h_mcs : Temporal.SetMaximalConsistent Omega)
    (L : List (Formula Atom)) (h_sub : ∀ ψ ∈ L, ψ ∈ h_content Omega)
    (h_deriv : DerivationTree FrameClass.Base L φ) : Formula.all_past φ ∈ Omega := by
  have d_H := generalized_past_k L φ h_deriv
  have h_HL_in : ∀ f ∈ Context.map Formula.all_past L, f ∈ Omega := by
    intro f hf; rw [Context.mem_map_iff] at hf
    obtain ⟨ψ, hψ_in, hψ_eq⟩ := hf; rw [← hψ_eq]; exact h_sub ψ hψ_in
  exact temporal_closed_under_derivation h_mcs h_HL_in ⟨d_H⟩

/-! ## g/h-content Set Consistent -/

theorem g_content_set_consistent {Omega : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent Omega) :
    Temporal.SetConsistent (g_content Omega) := by
  intro L hL ⟨d⟩
  have h_G_bot := g_content_closed_derivation h_mcs L hL d
  -- G(⊥) = ¬F(⊤) ∈ Omega, but F(⊤) ∈ Omega by serial_future. Contradiction.
  have h_top : Formula.top ∈ Omega := theorem_in_mcs h_mcs
    (DerivationTree.axiom [] _ (.efq Formula.bot) trivial)
  have h_f_top : Formula.some_future Formula.top ∈ Omega :=
    temporal_implication_property h_mcs
      (theorem_in_mcs h_mcs (DerivationTree.axiom [] _ .serial_future trivial)) h_top
  exact mcs_not_mem_of_neg h_mcs h_G_bot h_f_top

theorem h_content_set_consistent {Omega : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent Omega) :
    Temporal.SetConsistent (h_content Omega) := by
  intro L hL ⟨d⟩
  have h_H_bot := h_content_closed_derivation h_mcs L hL d
  have h_top : Formula.top ∈ Omega := theorem_in_mcs h_mcs
    (DerivationTree.axiom [] _ (.efq Formula.bot) trivial)
  have h_p_top : Formula.some_past Formula.top ∈ Omega :=
    temporal_implication_property h_mcs
      (theorem_in_mcs h_mcs (DerivationTree.axiom [] _ .serial_past trivial)) h_top
  exact mcs_not_mem_of_neg h_mcs h_H_bot h_p_top

/-! ## Transitivity -/

theorem t_le_trans {w u v : TPoint Atom} (hwu : t_le w u) (huv : t_le u v) :
    t_le w v := by
  intro φ hφ
  have h_GGφ := mcs_g_trans w.is_mcs hφ
  exact huv (hwu h_GGφ)

/-! ## Forward/Backward Temporal Witnesses -/

noncomputable def t_forward_witness (w : TPoint Atom) (ψ : Formula Atom)
    (h_F : Formula.some_future ψ ∈ w.formulas) :
    ∃ v : TPoint Atom, t_le w v ∧ ψ ∈ v.formulas := by
  have h_seed_cons := forward_temporal_witness_seed_consistent w.formulas w.is_mcs ψ h_F
  obtain ⟨M, hM_sup, hM_mcs⟩ := temporal_lindenbaum h_seed_cons
  exact ⟨⟨M, hM_mcs⟩,
    fun χ hχ => hM_sup (Set.mem_union_right _ hχ),
    hM_sup (Set.mem_union_left _ (Set.mem_singleton ψ))⟩

noncomputable def t_backward_witness (w : TPoint Atom) (ψ : Formula Atom)
    (h_P : Formula.some_past ψ ∈ w.formulas) :
    ∃ v : TPoint Atom, t_le v w ∧ ψ ∈ v.formulas := by
  have h_seed_cons := past_temporal_witness_seed_consistent w.formulas w.is_mcs ψ h_P
  obtain ⟨M, hM_sup, hM_mcs⟩ := temporal_lindenbaum h_seed_cons
  have h_h_sub : h_content w.formulas ⊆ M :=
    fun χ hχ => hM_sup (Set.mem_union_right _ hχ)
  exact ⟨⟨M, hM_mcs⟩,
    h_content_subset_implies_g_content_reverse w.formulas M w.is_mcs hM_mcs h_h_sub,
    hM_sup (Set.mem_union_left _ (Set.mem_singleton ψ))⟩

/-! ## G-content Forward and Backward -/

theorem t_G_forward {w v : TPoint Atom} {φ : Formula Atom}
    (h_le : t_le w v) (h_G : Formula.all_future φ ∈ w.formulas) :
    φ ∈ v.formulas :=
  h_le h_G

noncomputable def t_G_backward (w : TPoint Atom) (φ : Formula Atom)
    (h_not_G : Formula.all_future φ ∉ w.formulas) :
    ∃ v : TPoint Atom, t_le w v ∧ φ ∉ v.formulas := by
  have h_seed_cons : Temporal.SetConsistent ({Formula.neg φ} ∪ g_content w.formulas : Set (Formula Atom)) := by
    intro L hL ⟨d⟩
    by_cases h_negφ_in : Formula.neg φ ∈ L
    · have h_sub_reord : ∀ x, x ∈ L → x ∈ Formula.neg φ :: L.filter (fun y => decide (y ≠ Formula.neg φ)) := by
        intro x hx
        by_cases hxn : x = Formula.neg φ
        · exact List.mem_cons.mpr (Or.inl hxn)
        · exact List.mem_cons.mpr (Or.inr (by simp [List.mem_filter, decide_eq_true_eq]; exact ⟨hx, hxn⟩))
      have d_reord := DerivationTree.weakening L _ Formula.bot d h_sub_reord
      have d_negneg := deduction_theorem _ (Formula.neg φ) Formula.bot d_reord
      have h_filt_in_g : ∀ ψ ∈ L.filter (fun y => decide (y ≠ Formula.neg φ)), ψ ∈ g_content w.formulas := by
        intro ψ hψ
        have h_and := List.mem_filter.mp hψ
        have h_ne : ψ ≠ Formula.neg φ := by simpa using h_and.2
        have h_mem := hL ψ h_and.1
        simp only [Set.mem_union, Set.mem_singleton_iff] at h_mem
        rcases h_mem with rfl | h
        · exact absurd rfl h_ne
        · exact h
      have h_dne := double_negation φ
      have d_dne_weak := DerivationTree.weakening [] (L.filter (fun y => decide (y ≠ Formula.neg φ))) _ h_dne (fun _ h => nomatch h)
      have d_phi := DerivationTree.modus_ponens (L.filter (fun y => decide (y ≠ Formula.neg φ))) _ _ d_dne_weak d_negneg
      exact h_not_G (g_content_closed_derivation w.is_mcs _ h_filt_in_g d_phi)
    · have h_L_in_g : ∀ ψ ∈ L, ψ ∈ g_content w.formulas := by
        intro ψ hψ
        have h_mem := hL ψ hψ
        simp only [Set.mem_union, Set.mem_singleton_iff] at h_mem
        rcases h_mem with rfl | h
        · exact absurd hψ h_negφ_in
        · exact h
      exact g_content_set_consistent w.is_mcs L h_L_in_g ⟨d⟩
  obtain ⟨M, hM_sup, hM_mcs⟩ := temporal_lindenbaum h_seed_cons
  exact ⟨⟨M, hM_mcs⟩,
    fun χ hχ => hM_sup (Set.mem_union_right _ hχ),
    mcs_not_mem_of_neg hM_mcs (hM_sup (Set.mem_union_left _ (Set.mem_singleton _)))⟩

/-! ## H-content Forward and Backward -/

theorem t_H_forward {w v : TPoint Atom} {φ : Formula Atom}
    (h_le : t_le v w) (h_H : Formula.all_past φ ∈ w.formulas) :
    φ ∈ v.formulas :=
  g_content_subset_implies_h_content_reverse v.formulas w.formulas
    v.is_mcs w.is_mcs h_le h_H

noncomputable def t_H_backward (w : TPoint Atom) (φ : Formula Atom)
    (h_not_H : Formula.all_past φ ∉ w.formulas) :
    ∃ v : TPoint Atom, t_le v w ∧ φ ∉ v.formulas := by
  have h_seed_cons : Temporal.SetConsistent ({Formula.neg φ} ∪ h_content w.formulas : Set (Formula Atom)) := by
    intro L hL ⟨d⟩
    by_cases h_negφ_in : Formula.neg φ ∈ L
    · have h_sub_reord : ∀ x, x ∈ L → x ∈ Formula.neg φ :: L.filter (fun y => decide (y ≠ Formula.neg φ)) := by
        intro x hx
        by_cases hxn : x = Formula.neg φ
        · exact List.mem_cons.mpr (Or.inl hxn)
        · exact List.mem_cons.mpr (Or.inr (by simp [List.mem_filter, decide_eq_true_eq]; exact ⟨hx, hxn⟩))
      have d_reord := DerivationTree.weakening L _ Formula.bot d h_sub_reord
      have d_negneg := deduction_theorem _ (Formula.neg φ) Formula.bot d_reord
      have h_filt_in_h : ∀ ψ ∈ L.filter (fun y => decide (y ≠ Formula.neg φ)), ψ ∈ h_content w.formulas := by
        intro ψ hψ
        have h_and := List.mem_filter.mp hψ
        have h_ne : ψ ≠ Formula.neg φ := by simpa using h_and.2
        have h_mem := hL ψ h_and.1
        simp only [Set.mem_union, Set.mem_singleton_iff] at h_mem
        rcases h_mem with rfl | h
        · exact absurd rfl h_ne
        · exact h
      have h_dne := double_negation φ
      have d_dne_weak := DerivationTree.weakening [] (L.filter (fun y => decide (y ≠ Formula.neg φ))) _ h_dne (fun _ h => nomatch h)
      have d_phi := DerivationTree.modus_ponens (L.filter (fun y => decide (y ≠ Formula.neg φ))) _ _ d_dne_weak d_negneg
      exact h_not_H (h_content_closed_derivation w.is_mcs _ h_filt_in_h d_phi)
    · have h_L_in_h : ∀ ψ ∈ L, ψ ∈ h_content w.formulas := by
        intro ψ hψ
        have h_mem := hL ψ hψ
        simp only [Set.mem_union, Set.mem_singleton_iff] at h_mem
        rcases h_mem with rfl | h
        · exact absurd hψ h_negφ_in
        · exact h
      exact h_content_set_consistent w.is_mcs L h_L_in_h ⟨d⟩
  obtain ⟨M, hM_sup, hM_mcs⟩ := temporal_lindenbaum h_seed_cons
  have h_h_sub : h_content w.formulas ⊆ M :=
    fun χ hχ => hM_sup (Set.mem_union_right _ hχ)
  exact ⟨⟨M, hM_mcs⟩,
    h_content_subset_implies_g_content_reverse w.formulas M w.is_mcs hM_mcs h_h_sub,
    mcs_not_mem_of_neg hM_mcs (hM_sup (Set.mem_union_left _ (Set.mem_singleton _)))⟩

/-! ## Eventuality Resolution for Until/Since -/

noncomputable def t_until_eventuality_resolution
    (w : TPoint Atom) (φ ψ : Formula Atom)
    (h_until : Formula.untl ψ φ ∈ w.formulas)
    (h_not_psi : ψ ∉ w.formulas) :
    ∃ v : TPoint Atom, t_le w v ∧ ψ ∈ v.formulas := by
  have h_F_psi : Formula.some_future ψ ∈ w.formulas := by
    have h_ax := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.until_F φ ψ) trivial
    exact temporal_implication_property w.is_mcs (theorem_in_mcs w.is_mcs h_ax) h_until
  exact t_forward_witness w ψ h_F_psi

noncomputable def t_since_eventuality_resolution
    (w : TPoint Atom) (φ ψ : Formula Atom)
    (h_since : Formula.snce ψ φ ∈ w.formulas)
    (h_not_psi : ψ ∉ w.formulas) :
    ∃ v : TPoint Atom, t_le v w ∧ ψ ∈ v.formulas := by
  have h_P_psi : Formula.some_past ψ ∈ w.formulas := by
    have h_ax := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.since_P φ ψ) trivial
    exact temporal_implication_property w.is_mcs (theorem_in_mcs w.is_mcs h_ax) h_since
  exact t_backward_witness w ψ h_P_psi

end Cslib.Logic.Temporal.Metalogic.Chronicle
