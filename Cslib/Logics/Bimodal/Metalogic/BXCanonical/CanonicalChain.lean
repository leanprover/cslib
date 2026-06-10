/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.BXCanonical.Frame
public import Cslib.Logics.Bimodal.Metalogic.BXCanonical.Filtration.DefectChain

/-!
# Canonical Chain Infrastructure

MCS-level lemmas for BX axioms and delegation bridges.

## References

* Ported from BimodalLogic/Theories/Bimodal/Metalogic/BXCanonical/CanonicalChain.lean
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.BXCanonical

open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Metalogic.Core
open Cslib.Logic.Bimodal.Metalogic.Bundle
open Cslib.Logic.Bimodal.Metalogic.BXCanonical.Filtration

variable {Atom : Type*}

/-! ## BX12 at MCS level: F(ψ) → ⊤ U ψ -/

theorem F_imp_top_until_mcs {w : BXPoint Atom} {ψ : Formula Atom}
    (h : Formula.someFuture ψ ∈ w.formulas) :
    Formula.untl ψ ((Formula.bot : Formula Atom).imp (Formula.bot : Formula Atom)) ∈ w.formulas := by
  have h_ax : DerivationTree FrameClass.Base [] ((Formula.someFuture ψ).imp
    (Formula.untl ψ ((Formula.bot : Formula Atom).imp (Formula.bot : Formula Atom)))) :=
    DerivationTree.axiom [] _ (Axiom.F_until_equiv ψ) trivial
  exact SetMaximalConsistent.implication_property w.is_mcs
    (theorem_in_mcs_fc w.is_mcs h_ax) h

theorem P_imp_top_since_mcs {w : BXPoint Atom} {ψ : Formula Atom}
    (h : Formula.somePast ψ ∈ w.formulas) :
    Formula.snce ψ ((Formula.bot : Formula Atom).imp (Formula.bot : Formula Atom)) ∈ w.formulas := by
  have h_ax : DerivationTree FrameClass.Base [] ((Formula.somePast ψ).imp
    (Formula.snce ψ ((Formula.bot : Formula Atom).imp (Formula.bot : Formula Atom)))) :=
    DerivationTree.axiom [] _ (Axiom.P_since_equiv ψ) trivial
  exact SetMaximalConsistent.implication_property w.is_mcs
    (theorem_in_mcs_fc w.is_mcs h_ax) h

/-! ## BX6 at MCS level: absorption -/

theorem absorb_until_mcs {w : BXPoint Atom} {φ ψ : Formula Atom}
    (h : Formula.untl (Formula.and φ (Formula.untl ψ φ)) φ ∈ w.formulas) :
    Formula.untl ψ φ ∈ w.formulas := by
  have h_ax : DerivationTree FrameClass.Base [] ((Formula.untl (Formula.and φ (Formula.untl ψ φ)) φ).imp
    (Formula.untl ψ φ)) :=
    DerivationTree.axiom [] _ (Axiom.absorb_until φ ψ) trivial
  exact SetMaximalConsistent.implication_property w.is_mcs
    (theorem_in_mcs_fc w.is_mcs h_ax) h

theorem absorb_since_mcs {w : BXPoint Atom} {φ ψ : Formula Atom}
    (h : Formula.snce (Formula.and φ (Formula.snce ψ φ)) φ ∈ w.formulas) :
    Formula.snce ψ φ ∈ w.formulas := by
  have h_ax : DerivationTree FrameClass.Base [] ((Formula.snce (Formula.and φ (Formula.snce ψ φ)) φ).imp
    (Formula.snce ψ φ)) :=
    DerivationTree.axiom [] _ (Axiom.absorb_since φ ψ) trivial
  exact SetMaximalConsistent.implication_property w.is_mcs
    (theorem_in_mcs_fc w.is_mcs h_ax) h

/-! ## Delegation bridges -/

theorem delegation_until_eventuality
    (w : BXPoint Atom) (φ ψ : Formula Atom)
    (h_until : Formula.untl ψ φ ∈ w.formulas)
    (h_not_psi : ψ ∉ w.formulas) :
    ∃ v : BXPoint Atom, bx_le w v ∧ ψ ∈ v.formulas :=
  bx_until_eventuality_resolution w φ ψ h_until h_not_psi

theorem delegation_since_eventuality
    (w : BXPoint Atom) (φ ψ : Formula Atom)
    (h_since : Formula.snce ψ φ ∈ w.formulas)
    (h_not_psi : ψ ∉ w.formulas) :
    ∃ v : BXPoint Atom, bx_le v w ∧ ψ ∈ v.formulas :=
  bx_since_eventuality_resolution w φ ψ h_since h_not_psi

end Cslib.Logic.Bimodal.Metalogic.BXCanonical
