/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/

import Cslib.Logics.Bimodal.Metalogic.Bundle.BFMCS
import Cslib.Logics.Bimodal.Metalogic.Bundle.CanonicalFrame
import Cslib.Logics.Bimodal.Metalogic.Bundle.ModalSaturation
import Cslib.Logics.Bimodal.Metalogic.Core.MaximalConsistent
import Cslib.Logics.Bimodal.Metalogic.Core.MCSProperties
import Cslib.Logics.Bimodal.Metalogic.Core.DeductionTheorem
import Cslib.Logics.Bimodal.Syntax.Formula
import Cslib.Logics.Bimodal.Theorems.Propositional.Core

/-!
# BFMCS Construction Primitives

Provides primitive building blocks for BFMCS construction.

## References

* Ported from BimodalLogic/Theories/Bimodal/Metalogic/Bundle/Construction.lean
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Cslib.Logic.Bimodal.Metalogic.Bundle

open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Metalogic.Core

variable {Atom : Type*} {D : Type*} [Preorder D]

/-! ## Extending Context to MCS -/

def contextAsSet (Gamma : List (Formula Atom)) : Set (Formula Atom) := {phi | phi ∈ Gamma}

lemma list_consistent_to_set_consistent {Gamma : List (Formula Atom)}
    (h_cons : Consistent (fc := FrameClass.Base) Gamma) :
    SetConsistent (FrameClass.Base : FrameClass) (contextAsSet Gamma) := by
  intro L hL
  intro ⟨d⟩
  apply h_cons
  exact ⟨DerivationTree.weakening L Gamma (Formula.bot : Formula Atom) d hL⟩

/-! ## Core Definitions -/

def ContextConsistent (Gamma : List (Formula Atom)) : Prop :=
  ¬Nonempty (DerivationTree FrameClass.Base Gamma (Formula.bot : Formula Atom))

noncomputable def lindenbaumMCS (Gamma : List (Formula Atom)) (h_cons : ContextConsistent Gamma) :
    Set (Formula Atom) :=
  let h_set_cons : SetConsistent (FrameClass.Base : FrameClass) (contextAsSet Gamma) := list_consistent_to_set_consistent h_cons
  Classical.choose (set_lindenbaum_base h_set_cons)

lemma lindenbaumMCS_extends (Gamma : List (Formula Atom)) (h_cons : ContextConsistent Gamma) :
    contextAsSet Gamma ⊆ lindenbaumMCS Gamma h_cons :=
  let h_set_cons : SetConsistent (FrameClass.Base : FrameClass) (contextAsSet Gamma) := list_consistent_to_set_consistent h_cons
  (Classical.choose_spec (set_lindenbaum_base h_set_cons)).1

lemma lindenbaumMCS_is_mcs (Gamma : List (Formula Atom)) (h_cons : ContextConsistent Gamma) :
    SetMaximalConsistent (FrameClass.Base : FrameClass) (lindenbaumMCS Gamma h_cons) :=
  let h_set_cons : SetConsistent (FrameClass.Base : FrameClass) (contextAsSet Gamma) := list_consistent_to_set_consistent h_cons
  (Classical.choose_spec (set_lindenbaum_base h_set_cons)).2

noncomputable def lindenbaumMCS_set (Omega : Set (Formula Atom)) (h_cons : SetConsistent (FrameClass.Base : FrameClass) Omega) :
    Set (Formula Atom) :=
  Classical.choose (set_lindenbaum_base h_cons)

lemma lindenbaumMCS_set_extends (Omega : Set (Formula Atom)) (h_cons : SetConsistent (FrameClass.Base : FrameClass) Omega) :
    Omega ⊆ lindenbaumMCS_set Omega h_cons :=
  (Classical.choose_spec (set_lindenbaum_base h_cons)).1

lemma lindenbaumMCS_set_is_mcs (Omega : Set (Formula Atom)) (h_cons : SetConsistent (FrameClass.Base : FrameClass) Omega) :
    SetMaximalConsistent (FrameClass.Base : FrameClass) (lindenbaumMCS_set Omega h_cons) :=
  (Classical.choose_spec (set_lindenbaum_base h_cons)).2

/-! ## Context Derivability Utilities -/

def ContextDerivable (Γ : List (Formula Atom)) (φ : Formula Atom) : Prop :=
  Nonempty (DerivationTree FrameClass.Base Γ φ)

lemma not_derivable_implies_neg_consistent (φ : Formula Atom)
    (h_not_deriv : ¬Nonempty (DerivationTree FrameClass.Base [] φ)) :
    ContextConsistent [φ.neg] := by
  intro ⟨d_bot⟩
  have d_neg_neg : DerivationTree FrameClass.Base [] (φ.neg.neg) :=
    deduction_theorem [] φ.neg (Formula.bot : Formula Atom) d_bot
  have h_dne : DerivationTree FrameClass.Base [] (φ.neg.neg.imp φ) :=
    Theorems.Propositional.double_negation φ
  have d_phi : DerivationTree FrameClass.Base [] φ :=
    DerivationTree.modus_ponens [] φ.neg.neg φ h_dne d_neg_neg
  exact h_not_deriv ⟨d_phi⟩

lemma context_not_derivable_implies_extended_consistent (Γ : List (Formula Atom)) (φ : Formula Atom)
    (h_not_deriv : ¬ContextDerivable Γ φ) :
    ContextConsistent (Γ ++ [φ.neg]) := by
  intro ⟨d_bot⟩
  have h_subset : Γ ++ [φ.neg] ⊆ φ.neg :: Γ := by
    intro x hx
    simp at hx ⊢
    tauto
  have d_bot_reordered : DerivationTree FrameClass.Base (φ.neg :: Γ) (Formula.bot : Formula Atom) :=
    DerivationTree.weakening (Γ ++ [φ.neg]) (φ.neg :: Γ) (Formula.bot : Formula Atom) d_bot h_subset
  have d_neg_neg : DerivationTree FrameClass.Base Γ φ.neg.neg :=
    deduction_theorem Γ φ.neg (Formula.bot : Formula Atom) d_bot_reordered
  have h_dne : DerivationTree FrameClass.Base [] (φ.neg.neg.imp φ) :=
    Theorems.Propositional.double_negation φ
  have h_dne_ctx : DerivationTree FrameClass.Base Γ (φ.neg.neg.imp φ) :=
    DerivationTree.weakening [] Γ (φ.neg.neg.imp φ) h_dne (by intro; simp)
  have d_phi : DerivationTree FrameClass.Base Γ φ :=
    DerivationTree.modus_ponens Γ φ.neg.neg φ h_dne_ctx d_neg_neg
  exact h_not_deriv ⟨d_phi⟩

end Cslib.Logic.Bimodal.Metalogic.Bundle
