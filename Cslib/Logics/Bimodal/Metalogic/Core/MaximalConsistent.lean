/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/

import Cslib.Logics.Bimodal.Metalogic.Core.DeductionTheorem

/-!
# Maximal Consistent Sets for TM Bimodal Logic

This module provides the theory of maximal consistent sets (MCS) for the
TM bimodal logic system. These are foundational for canonical model construction.

## Main Results

- `Consistent`: List-based consistency definition
- `MaximalConsistent`: List-based maximal consistency definition
- Bimodal-specific abbreviations delegating to the generic MCS framework
- `bimodal_lindenbaum`: Lindenbaum's lemma (delegates to generic)
- `bimodal_closed_under_derivation`: MCS closure (delegates to generic)
- List-based MCS closure properties using the deduction theorem directly

## Design

List-based definitions are retained for backward compatibility and direct proof use.
Set-based MCS theory delegates to `Cslib.Foundations.Logic.Metalogic.Consistency`
via `bimodalDerivationSystem` and `bimodal_has_deduction_theorem`.

## References

* Ported from BimodalLogic/Theories/Bimodal/Metalogic/Core/MaximalConsistent.lean
* Cslib/Foundations/Logic/Metalogic/Consistency.lean — generic MCS framework
-/

set_option linter.style.emptyLine false
set_option linter.flexible false

namespace Cslib.Logic.Bimodal.Metalogic.Core

open Cslib.Logic.Bimodal
open Cslib.Logic

variable {Atom : Type*}

/-!
## List-Based Consistency

A context `Γ` is **consistent** if no contradiction is derivable from it.
-/

/--
A context `Γ` is **consistent** if it does not derive bottom (⊥).
-/
def Consistent {fc : FrameClass} (Γ : Context Atom) : Prop :=
  ¬Nonempty (DerivationTree fc Γ Formula.bot)

/--
A context `Γ` is **maximal consistent** if it's consistent and adding any
formula not already in `Γ` makes it inconsistent.
-/
def MaximalConsistent {fc : FrameClass} (Γ : Context Atom) : Prop :=
  Consistent (fc := fc) Γ ∧ ∀ φ : Formula Atom, φ ∉ Γ → ¬Consistent (fc := fc) (φ :: Γ)

/-!
## Set-Based Consistency (Bimodal-Specific Abbreviations)

These delegate to the generic framework, instantiated with `bimodalDerivationSystem`.
-/

/-- Bimodal set-consistency: abbreviation for the generic version. -/
abbrev BimodalSetConsistent (Ω : Set (Formula Atom)) : Prop :=
  Metalogic.SetConsistent (bimodalDerivationSystem (Atom := Atom)) Ω

/-- Bimodal set-maximal consistency: abbreviation for the generic version. -/
abbrev BimodalSetMaximalConsistent (Ω : Set (Formula Atom)) : Prop :=
  Metalogic.SetMaximalConsistent (bimodalDerivationSystem (Atom := Atom)) Ω

/-!
## Generic Framework Delegation Wrappers

These provide convenient bimodal-specific names for generic MCS properties.
-/

/-- Lindenbaum's lemma for bimodal logic: every consistent set extends to MCS.
Delegates to the generic `set_lindenbaum`. -/
theorem bimodal_lindenbaum (Ω : Set (Formula Atom))
    (hΩ : BimodalSetConsistent Ω) :
    ∃ M : Set (Formula Atom), Ω ⊆ M ∧ BimodalSetMaximalConsistent M :=
  Metalogic.set_lindenbaum bimodalDerivationSystem hΩ

/-- MCS closure under derivation for bimodal logic.
Delegates to the generic `closed_under_derivation`. -/
noncomputable def bimodal_closed_under_derivation
    {Ω : Set (Formula Atom)}
    (h_mcs : BimodalSetMaximalConsistent Ω)
    {L : List (Formula Atom)} (h_sub : ∀ ψ ∈ L, ψ ∈ Ω)
    {φ : Formula Atom} (h_deriv : Bimodal.Deriv L φ) : φ ∈ Ω :=
  Metalogic.SetMaximalConsistent.closed_under_derivation
    bimodalDerivationSystem bimodal_has_deduction_theorem h_mcs h_sub h_deriv

/-- MCS implication property for bimodal logic.
Delegates to the generic `implication_property`. -/
noncomputable def bimodal_implication_property
    {Ω : Set (Formula Atom)}
    (h_mcs : BimodalSetMaximalConsistent Ω)
    {φ ψ : Formula Atom}
    (h_imp : φ.imp ψ ∈ Ω) (h_phi : φ ∈ Ω) : ψ ∈ Ω :=
  Metalogic.SetMaximalConsistent.implication_property
    bimodalDerivationSystem bimodal_has_deduction_theorem h_mcs h_imp h_phi

/-- MCS negation completeness for bimodal logic.
Delegates to the generic `negation_complete`. -/
noncomputable def bimodal_negation_complete
    {Ω : Set (Formula Atom)}
    (h_mcs : BimodalSetMaximalConsistent Ω)
    (φ : Formula Atom) : φ ∈ Ω ∨ Formula.neg φ ∈ Ω :=
  Metalogic.SetMaximalConsistent.negation_complete
    bimodalDerivationSystem bimodal_has_deduction_theorem h_mcs φ

/-!
## Helper Lemmas for List-Based MCS

These use the deduction theorem directly on list-based MCS definitions.
-/

/--
If a context is inconsistent, it derives bottom.
-/
lemma inconsistent_derives_bot {fc : FrameClass} {Γ : Context Atom}
    (h : ¬Consistent (fc := fc) Γ) :
    Nonempty (DerivationTree fc Γ Formula.bot) := by
  unfold Consistent at h
  push_neg at h
  exact h

/--
If extending a consistent context with φ makes it inconsistent, then the original
context derives ¬φ (i.e., φ → ⊥).

Uses the deduction theorem.
-/
noncomputable def derives_neg_from_inconsistent_extension {fc : FrameClass}
    {Γ : Context Atom} {φ : Formula Atom}
    (h_incons : ¬Consistent (fc := fc) (φ :: Γ)) :
    Nonempty (DerivationTree fc Γ (Formula.neg φ)) := by
  have ⟨d_bot⟩ := inconsistent_derives_bot h_incons
  exact ⟨deduction_theorem Γ φ Formula.bot d_bot⟩

/--
From Γ ⊢ φ and Γ ⊢ ¬φ (i.e., φ → ⊥), derive Γ ⊢ ⊥.
-/
def derives_bot_from_phi_neg_phi {fc : FrameClass} {Γ : Context Atom} {φ : Formula Atom}
    (h_phi : DerivationTree fc Γ φ)
    (h_neg : DerivationTree fc Γ (Formula.neg φ)) :
    DerivationTree fc Γ Formula.bot :=
  DerivationTree.modus_ponens Γ φ Formula.bot h_neg h_phi

/--
For maximal consistent sets, if φ ∉ Γ then the extension φ :: Γ is inconsistent.
-/
lemma maximal_extends_inconsistent {fc : FrameClass} {Γ : Context Atom} {φ : Formula Atom}
    (h_max : MaximalConsistent (fc := fc) Γ) (h_not_mem : φ ∉ Γ) :
    ¬Consistent (fc := fc) (φ :: Γ) :=
  h_max.2 φ h_not_mem

/-!
## MCS Closure Properties (List-Based)
-/

/--
Maximal consistent sets are deductively closed.

**Statement**: `MaximalConsistent Γ → (Γ ⊢ φ → φ ∈ Γ)`
-/
noncomputable def maximal_consistent_closed {fc : FrameClass} (Γ : Context Atom)
    (φ : Formula Atom)
    (h_max : MaximalConsistent (fc := fc) Γ)
    (h_deriv : DerivationTree fc Γ φ) : φ ∈ Γ := by
  by_contra h_not_mem
  have h_incons := maximal_extends_inconsistent h_max h_not_mem
  have ⟨h_neg_deriv⟩ := derives_neg_from_inconsistent_extension h_incons
  have h_bot := derives_bot_from_phi_neg_phi h_deriv h_neg_deriv
  exact h_max.1 ⟨h_bot⟩

/--
Maximal consistent sets are negation complete.

**Statement**: `MaximalConsistent Γ → (φ ∉ Γ → ¬φ ∈ Γ)`
-/
noncomputable def maximal_negation_complete {fc : FrameClass} (Γ : Context Atom)
    (φ : Formula Atom)
    (h_max : MaximalConsistent (fc := fc) Γ) (h_not_mem : φ ∉ Γ) :
    Formula.neg φ ∈ Γ := by
  have h_incons := maximal_extends_inconsistent h_max h_not_mem
  have ⟨h_neg_deriv⟩ := derives_neg_from_inconsistent_extension h_incons
  exact maximal_consistent_closed Γ (Formula.neg φ) h_max h_neg_deriv

/-!
## Theorem Membership
-/

/--
Theorems (formulas derivable from empty context) are in every MCS (set-based).

Uses `bimodal_closed_under_derivation` with empty list.
-/
noncomputable def theorem_in_mcs {Ω : Set (Formula Atom)} {φ : Formula Atom}
    (h_mcs : BimodalSetMaximalConsistent Ω)
    (h_deriv : DerivationTree FrameClass.Base [] φ) : φ ∈ Ω := by
  exact bimodal_closed_under_derivation h_mcs (L := []) (fun _ h => by simp at h)
    ⟨DerivationTree.weakening [] [] φ h_deriv (fun _ h => h)⟩

end Cslib.Logic.Bimodal.Metalogic.Core
