/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/

import Cslib.Logics.Bimodal.Metalogic.BXCanonical.Frame
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image

/-!
# Defect-Discharge Chain Construction

Sigma defect count on BXPoints and defect-discharge infrastructure.

## References

* Ported from BimodalLogic/Theories/Bimodal/Metalogic/BXCanonical/Filtration/DefectChain.lean
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Cslib.Logic.Bimodal.Metalogic.BXCanonical.Filtration

open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Metalogic.Core
open Cslib.Logic.Bimodal.Metalogic.Bundle
open Cslib.Logic.Bimodal.Metalogic.BXCanonical
open Classical

variable {Atom : Type*} [DecidableEq Atom]

/-! ## Until Defect Count -/

def is_until_defect (w : BXPoint Atom) (Sigma : Finset (Formula Atom)) (f : Formula Atom) : Prop :=
  f ∈ Sigma ∧ f ∈ w.formulas ∧
  ∃ φ ψ : Formula Atom, f = Formula.untl ψ φ ∧ ψ ∉ w.formulas

noncomputable def sigma_defect_count (w : BXPoint Atom) (Sigma : Finset (Formula Atom)) : Nat :=
  (Sigma.filter (fun f =>
    f ∈ w.formulas ∧
    ∃ φ ψ : Formula Atom, f = Formula.untl ψ φ ∧ ψ ∉ w.formulas)).card

theorem sigma_defect_count_bounded (w : BXPoint Atom) (Sigma : Finset (Formula Atom)) :
    sigma_defect_count w Sigma ≤ Sigma.card := by
  unfold sigma_defect_count
  exact Finset.card_filter_le Sigma _

/-! ## Defect Step Properties -/

private noncomputable def theorem_in_mcs_fc {M : Set (Formula Atom)} {phi : Formula Atom}
    (h_mcs : SetMaximalConsistent FrameClass.Base M)
    (h_deriv : DerivationTree FrameClass.Base [] phi) : phi ∈ M :=
  SetMaximalConsistent.closed_under_derivation h_mcs [] (fun _ h => by simp at h) h_deriv

theorem defect_step_F_psi {w : BXPoint Atom} {φ ψ : Formula Atom}
    (h_until : Formula.untl ψ φ ∈ w.formulas) :
    Formula.some_future ψ ∈ w.formulas := by
  have h_ax : DerivationTree FrameClass.Base [] _ := DerivationTree.axiom [] _ (Axiom.until_F φ ψ) trivial
  exact SetMaximalConsistent.implication_property w.is_mcs
    (theorem_in_mcs_fc w.is_mcs h_ax) h_until

theorem defect_step_connect {w : BXPoint Atom} {φ ψ : Formula Atom}
    (h_until : Formula.untl ψ φ ∈ w.formulas) :
    Formula.all_future (Formula.some_past (Formula.untl ψ φ)) ∈ w.formulas := by
  have h_ax : DerivationTree FrameClass.Base [] _ := DerivationTree.axiom [] _ (Axiom.connect_future (Formula.untl ψ φ)) trivial
  exact SetMaximalConsistent.implication_property w.is_mcs
    (theorem_in_mcs_fc w.is_mcs h_ax) h_until

theorem defect_step_self_accum {w : BXPoint Atom} {φ ψ : Formula Atom}
    (h_until : Formula.untl ψ φ ∈ w.formulas) :
    Formula.untl ψ (Formula.and φ (Formula.untl ψ φ)) ∈ w.formulas := by
  have h_ax : DerivationTree FrameClass.Base [] _ := DerivationTree.axiom [] _ (Axiom.self_accum_until φ ψ) trivial
  exact SetMaximalConsistent.implication_property w.is_mcs
    (theorem_in_mcs_fc w.is_mcs h_ax) h_until

/-! ## Since Defect Properties -/

noncomputable def sigma_since_defect_count (w : BXPoint Atom) (Sigma : Finset (Formula Atom)) : Nat :=
  (Sigma.filter (fun f =>
    f ∈ w.formulas ∧
    ∃ φ ψ : Formula Atom, f = Formula.snce ψ φ ∧ ψ ∉ w.formulas)).card

theorem since_defect_step_P_psi {w : BXPoint Atom} {φ ψ : Formula Atom}
    (h_since : Formula.snce ψ φ ∈ w.formulas) :
    Formula.some_past ψ ∈ w.formulas := by
  have h_ax : DerivationTree FrameClass.Base [] _ := DerivationTree.axiom [] _ (Axiom.since_P φ ψ) trivial
  exact SetMaximalConsistent.implication_property w.is_mcs
    (theorem_in_mcs_fc w.is_mcs h_ax) h_since

theorem since_defect_step_connect {w : BXPoint Atom} {φ ψ : Formula Atom}
    (h_since : Formula.snce ψ φ ∈ w.formulas) :
    Formula.all_past (Formula.some_future (Formula.snce ψ φ)) ∈ w.formulas := by
  have h_ax : DerivationTree FrameClass.Base [] _ := DerivationTree.axiom [] _ (Axiom.connect_past (Formula.snce ψ φ)) trivial
  exact SetMaximalConsistent.implication_property w.is_mcs
    (theorem_in_mcs_fc w.is_mcs h_ax) h_since

end Cslib.Logic.Bimodal.Metalogic.BXCanonical.Filtration
