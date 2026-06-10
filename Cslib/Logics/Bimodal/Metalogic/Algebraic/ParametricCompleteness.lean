/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import Cslib.Logics.Bimodal.Metalogic.Algebraic.ParametricTruthLemma
import Cslib.Logics.Bimodal.Metalogic.Bundle.Construction
import Cslib.Logics.Bimodal.Metalogic.Bundle.ModalSaturation

/-!
# D-Parametric Algebraic Completeness Theorem

Proves the D-parametric algebraic completeness theorem for TaskFrame semantics.

## References

* Ported from BimodalLogic/Theories/Bimodal/Metalogic/Algebraic/ParametricCompleteness.lean
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Cslib.Logic.Bimodal.Metalogic.Algebraic.ParametricCompleteness

open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Metalogic.Core
open Cslib.Logic.Bimodal.Metalogic.Bundle
open Cslib.Logic.Bimodal.Metalogic.Algebraic.ParametricCanonical
open Cslib.Logic.Bimodal.Metalogic.Algebraic.ParametricHistory
open Cslib.Logic.Bimodal.Metalogic.Algebraic.ParametricTruthLemma

variable {Atom : Type} {D : Type*} [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]

/-- If a formula is not provable, then its negation is consistent. -/
theorem not_provable_implies_neg_set_consistent (φ : Formula Atom)
    (h_not_prov : ¬Nonempty (DerivationTree FrameClass.Base [] φ)) :
    SetConsistent (fc := FrameClass.Base) ({φ.neg} : Set (Formula Atom)) := by
  intro L hL ⟨d⟩
  by_cases h_mem : φ.neg ∈ L
  · have h_weak : ∀ x ∈ L, x ∈ [φ.neg] := fun x hx => by
      have := hL x hx
      simp only [Set.mem_singleton_iff] at this
      simp [this]
    have d_single : DerivationTree FrameClass.Base [φ.neg] (Formula.bot : Formula Atom) :=
      DerivationTree.weakening L [φ.neg] (Formula.bot : Formula Atom) d h_weak
    have d_neg_neg : DerivationTree FrameClass.Base [] (φ.neg.neg) :=
      deduction_theorem [] φ.neg (Formula.bot : Formula Atom) d_single
    have h_dne : DerivationTree FrameClass.Base [] (φ.neg.neg.imp φ) :=
      Theorems.Propositional.double_negation φ
    have d_phi : DerivationTree FrameClass.Base [] φ :=
      DerivationTree.modus_ponens [] φ.neg.neg φ h_dne d_neg_neg
    exact h_not_prov ⟨d_phi⟩
  · have h_L_empty : L = [] := by
      cases L with
      | nil => rfl
      | cons x xs =>
        exfalso
        have hx := hL x List.mem_cons_self
        simp only [Set.mem_singleton_iff] at hx
        rw [hx] at h_mem
        exact h_mem List.mem_cons_self
    rw [h_L_empty] at d
    have d_efq : DerivationTree FrameClass.Base [] ((Formula.bot : Formula Atom).imp φ) :=
      DerivationTree.axiom [] _ (Axiom.efq φ) trivial
    have d_phi : DerivationTree FrameClass.Base [] φ :=
      DerivationTree.modus_ponens [] (Formula.bot : Formula Atom) φ d_efq d
    exact h_not_prov ⟨d_phi⟩

/-- Relative completeness theorem. -/
theorem parametric_canonical_completeness_relative
    (B : BFMCS Atom D FrameClass.Base) (h_tc : B.temporally_coherent)
    (h_buc : B.backward_until_since_coherent)
    (h_fuc : B.forward_until_since_coherent)
    (φ : Formula Atom) (_h_not_prov : ¬Nonempty (DerivationTree FrameClass.Base [] φ))
    (fam : FMCS Atom D FrameClass.Base) (hfam : fam ∈ B.families)
    (t : D) (h_neg_in : φ.neg ∈ fam.mcs t) :
    ¬truth_at ParametricCanonicalTaskModel (ShiftClosedParametricCanonicalOmega B)
      (parametric_to_history fam) t φ := by
  intro h_phi_true
  have h_phi_in := (parametric_shifted_truth_lemma B h_tc h_buc h_fuc φ fam hfam t).mpr h_phi_true
  exact set_consistent_not_both (fam.is_mcs t).1 φ h_phi_in h_neg_in

/-- Completeness from neg membership. -/
theorem parametric_completeness_from_neg_membership
    (B : BFMCS Atom D FrameClass.Base) (h_tc : B.temporally_coherent)
    (h_buc : B.backward_until_since_coherent)
    (h_fuc : B.forward_until_since_coherent)
    (φ : Formula Atom)
    (fam : FMCS Atom D FrameClass.Base) (hfam : fam ∈ B.families)
    (t : D) (h_neg_in : φ.neg ∈ fam.mcs t) :
    ¬truth_at ParametricCanonicalTaskModel (ShiftClosedParametricCanonicalOmega B)
      (parametric_to_history fam) t φ := by
  intro h_phi_true
  have h_phi_in := (parametric_shifted_truth_lemma B h_tc h_buc h_fuc φ fam hfam t).mpr h_phi_true
  exact set_consistent_not_both (fam.is_mcs t).1 φ h_phi_in h_neg_in

/-- If not provable, neg extends to MCS. -/
theorem not_provable_implies_neg_extends_to_mcs
    (φ : Formula Atom) (h_not_prov : ¬Nonempty (DerivationTree FrameClass.Base [] φ)) :
    ∃ M : Set (Formula Atom), SetMaximalConsistent (fc := FrameClass.Base) M ∧ φ.neg ∈ M := by
  have h_cons := not_provable_implies_neg_set_consistent φ h_not_prov
  obtain ⟨M, h_sub, h_mcs⟩ := set_lindenbaum_base h_cons
  exact ⟨M, h_mcs, h_sub (Set.mem_singleton φ.neg)⟩

/-- Conditional completeness theorem. -/
theorem parametric_canonical_completeness_conditional
    (φ : Formula Atom) (h_not_prov : ¬Nonempty (DerivationTree FrameClass.Base [] φ))
    (construct_bfmcs : (M : Set (Formula Atom)) → SetMaximalConsistent (fc := FrameClass.Base) M →
      Σ' (B : BFMCS Atom D FrameClass.Base) (_h_tc : B.temporally_coherent)
         (_h_buc : B.backward_until_since_coherent)
         (_h_fuc : B.forward_until_since_coherent)
         (fam : FMCS Atom D FrameClass.Base) (_hfam : fam ∈ B.families) (t : D),
         M = fam.mcs t) :
    ∃ (B : BFMCS Atom D FrameClass.Base) (_h_tc : B.temporally_coherent)
      (fam : FMCS Atom D FrameClass.Base) (_hfam : fam ∈ B.families) (t : D),
      ¬truth_at ParametricCanonicalTaskModel (ShiftClosedParametricCanonicalOmega B)
        (parametric_to_history fam) t φ := by
  obtain ⟨M, h_mcs, h_neg_in⟩ := not_provable_implies_neg_extends_to_mcs φ h_not_prov
  obtain ⟨B, h_tc, h_buc, h_fuc, fam, hfam, t, h_eq⟩ := construct_bfmcs M h_mcs
  have h_neg_in_fam : φ.neg ∈ fam.mcs t := h_eq ▸ h_neg_in
  exact ⟨B, h_tc, fam, hfam, t, parametric_completeness_from_neg_membership B h_tc h_buc h_fuc φ fam hfam t h_neg_in_fam⟩

/-- Countermodel implies not provable. -/
theorem countermodel_implies_not_provable
    (B : BFMCS Atom D FrameClass.Base) (h_tc : B.temporally_coherent)
    (h_buc : B.backward_until_since_coherent)
    (h_fuc : B.forward_until_since_coherent)
    (φ : Formula Atom)
    (fam : FMCS Atom D FrameClass.Base) (hfam : fam ∈ B.families) (t : D)
    (h_false : ¬truth_at ParametricCanonicalTaskModel (ShiftClosedParametricCanonicalOmega B)
      (parametric_to_history fam) t φ) :
    ¬Nonempty (DerivationTree FrameClass.Base [] φ) := by
  intro ⟨d⟩
  have h_in : φ ∈ fam.mcs t := by
    exact SetMaximalConsistent.closed_under_derivation (fam.is_mcs t) [] (fun _ h => by simp at h) d
  have h_true := (parametric_shifted_truth_lemma B h_tc h_buc h_fuc φ fam hfam t).mp h_in
  exact h_false h_true

end Cslib.Logic.Bimodal.Metalogic.Algebraic.ParametricCompleteness
