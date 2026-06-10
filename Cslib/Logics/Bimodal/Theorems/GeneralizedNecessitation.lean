/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import Cslib.Logics.Bimodal.ProofSystem.Derivation
import Cslib.Logics.Bimodal.Syntax.Context
import Cslib.Logics.Bimodal.Metalogic.Core.DeductionTheorem
import Cslib.Logics.Bimodal.ProofSystem.Axioms
import Cslib.Logics.Bimodal.Theorems.Combinators
import Cslib.Logics.Bimodal.Theorems.Propositional.Connectives

/-!
# Generalized Necessitation Rules

Derived generalized necessitation rules for modal, temporal future, and temporal past.

Ported from BimodalLogic/Theories/Bimodal/Theorems/GeneralizedNecessitation.lean
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Cslib.Logic.Bimodal.Theorems

open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Theorems.Combinators
open Cslib.Logic.Bimodal.Theorems.Propositional

variable {Atom : Type*}

private noncomputable def temp_k_dist_local (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base [] ((φ.imp ψ).allFuture.imp (φ.allFuture.imp ψ.allFuture)) :=
  let neg_contra := mp (contrapose_imp φ ψ) (contrapose_imp (φ.imp ψ) (ψ.neg.imp φ.neg))
  let F_step := mp (DerivationTree.temporal_necessitation _ neg_contra)
    (DerivationTree.axiom [] _
      (Axiom.right_mono_until (ψ.neg.imp φ.neg).neg (φ.imp ψ).neg Formula.top) trivial)
  let G_contra := contraposition F_step
  let G_to_GK := imp_trans
    (DerivationTree.axiom [] _ (Axiom.right_mono_until ψ.neg φ.neg Formula.top) trivial)
    (contrapose_imp (Formula.someFuture ψ.neg) (Formula.someFuture φ.neg))
  imp_trans G_contra G_to_GK

def reverse_deduction {fc : FrameClass} {Γ : Context Atom} {A B : Formula Atom}
    (h : DerivationTree fc Γ (A.imp B)) : DerivationTree fc (A :: Γ) B := by
  have h_weak : DerivationTree fc (A :: Γ) (A.imp B) :=
    DerivationTree.weakening _ _ _ h
      (by intro x hx; simp; right; exact hx)
  have h_assum : DerivationTree fc (A :: Γ) A := DerivationTree.assumption (A :: Γ) A (by simp)
  exact DerivationTree.modus_ponens (A :: Γ) A B h_weak h_assum

noncomputable def past_necessitation {fc : FrameClass} (φ : Formula Atom)
    (d : DerivationTree fc [] φ) : DerivationTree fc [] (Formula.allPast φ) := by
  have h_swap : DerivationTree fc [] φ.swapTemporal := DerivationTree.temporal_duality _ d
  have g_swap : DerivationTree fc [] φ.swapTemporal.allFuture :=
    DerivationTree.temporal_necessitation _ h_swap
  have final : DerivationTree fc [] φ.swapTemporal.allFuture.swapTemporal :=
    DerivationTree.temporal_duality _ g_swap
  simp only [Formula.swapTemporal_allFuture, Formula.swapTemporal,
    Formula.swapTemporal_involution] at final
  exact final

noncomputable def past_k_dist {fc : FrameClass} (A B : Formula Atom) :
    DerivationTree fc [] ((A.imp B).allPast.imp (A.allPast.imp B.allPast)) := by
  have fk : DerivationTree FrameClass.Base []
      ((A.swapTemporal.imp B.swapTemporal).allFuture.imp
       (A.swapTemporal.allFuture.imp B.swapTemporal.allFuture)) :=
    temp_k_dist_local A.swapTemporal B.swapTemporal
  have fk_fc := DerivationTree.lift (FrameClass.base_le fc) fk
  have td : DerivationTree fc []
      ((A.swapTemporal.imp B.swapTemporal).allFuture.imp
       (A.swapTemporal.allFuture.imp B.swapTemporal.allFuture)).swapTemporal :=
    DerivationTree.temporal_duality _ fk_fc
  simp only [Formula.swapTemporal_allFuture,
    Formula.swapTemporal, Formula.swapTemporal_involution] at td
  exact td

noncomputable def generalized_modal_k {fc : FrameClass} :
    (Γ : Context Atom) → (φ : Formula Atom) →
    (h : DerivationTree fc Γ φ) →
    (DerivationTree fc (Context.map Formula.box Γ) (Formula.box φ))
  | [], φ, h => DerivationTree.necessitation φ h
  | A :: Γ', φ, h =>
    let h_deduction := Cslib.Logic.Bimodal.Metalogic.Core.deduction_theorem Γ' A φ h
    let ih_res := generalized_modal_k Γ' (A.imp φ) h_deduction
    let k_dist : DerivationTree fc [] ((Formula.box (A.imp φ)).imp ((Formula.box A).imp (Formula.box φ))) :=
      DerivationTree.axiom [] _ (Axiom.modal_k_dist A φ) trivial
    let k_dist_weak :=
      DerivationTree.weakening [] (Context.map Formula.box Γ') _ k_dist (List.nil_subset _)
    let h_mp :=
      DerivationTree.modus_ponens _ _ _ k_dist_weak ih_res
    reverse_deduction h_mp

noncomputable def generalized_temporal_k {fc : FrameClass} :
    (Γ : Context Atom) → (φ : Formula Atom) →
    (h : DerivationTree fc Γ φ) →
    (DerivationTree fc (Context.map Formula.allFuture Γ) (Formula.allFuture φ))
  | [], φ, h => DerivationTree.temporal_necessitation φ h
  | A :: Γ', φ, h =>
    let h_deduction := Cslib.Logic.Bimodal.Metalogic.Core.deduction_theorem Γ' A φ h
    let ih_res := generalized_temporal_k Γ' (A.imp φ) h_deduction
    let k_dist_base := temp_k_dist_local A φ
    let k_dist := DerivationTree.lift (FrameClass.base_le fc) k_dist_base
    let k_dist_weak :=
      DerivationTree.weakening [] (Context.map Formula.allFuture Γ') _ k_dist (List.nil_subset _)
    let h_mp :=
      DerivationTree.modus_ponens _ _ _ k_dist_weak ih_res
    reverse_deduction h_mp

noncomputable def generalized_past_k {fc : FrameClass} :
    (Γ : Context Atom) → (φ : Formula Atom) →
    (h : DerivationTree fc Γ φ) →
    (DerivationTree fc (Context.map Formula.allPast Γ) (Formula.allPast φ))
  | [], φ, h => past_necessitation φ h
  | A :: Γ', φ, h =>
    let h_deduction := Cslib.Logic.Bimodal.Metalogic.Core.deduction_theorem Γ' A φ h
    let ih_res := generalized_past_k Γ' (A.imp φ) h_deduction
    let k_dist := past_k_dist (fc := fc) A φ
    let k_dist_weak :=
      DerivationTree.weakening [] (Context.map Formula.allPast Γ') _ k_dist (List.nil_subset _)
    let h_mp :=
      DerivationTree.modus_ponens _ _ _ k_dist_weak ih_res
    reverse_deduction h_mp

end Cslib.Logic.Bimodal.Theorems
