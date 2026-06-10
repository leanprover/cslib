/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.ProofSystem.Derivation
public import Cslib.Logics.Bimodal.Syntax.Context
public import Cslib.Logics.Bimodal.Metalogic.Core.DeductionTheorem
public import Cslib.Logics.Bimodal.ProofSystem.Axioms
public import Cslib.Logics.Bimodal.Theorems.Combinators
public import Cslib.Logics.Bimodal.Theorems.Propositional.Connectives

/-!
# Generalized Necessitation Rules

Derived generalized necessitation rules for modal, temporal future, and temporal past.

Ported from BimodalLogic/Theories/Bimodal/Theorems/GeneralizedNecessitation.lean
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false

@[expose] public section

namespace Cslib.Logic.Bimodal.Theorems

open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Theorems.Combinators
open Cslib.Logic.Bimodal.Theorems.Propositional

variable {Atom : Type*}

noncomputable def tempKDistLocal (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base [] ((φ.imp ψ).allFuture.imp (φ.allFuture.imp ψ.allFuture)) :=
  let neg_contra := mp (contraposeImp φ ψ) (contraposeImp (φ.imp ψ) (ψ.neg.imp φ.neg))
  let F_step := mp (DerivationTree.temporal_necessitation _ neg_contra)
    (DerivationTree.axiom [] _
      (Axiom.right_mono_until (ψ.neg.imp φ.neg).neg (φ.imp ψ).neg Formula.top) trivial)
  let G_contra := contraposition F_step
  let G_to_GK := impTrans
    (DerivationTree.axiom [] _ (Axiom.right_mono_until ψ.neg φ.neg Formula.top) trivial)
    (contraposeImp (Formula.someFuture ψ.neg) (Formula.someFuture φ.neg))
  impTrans G_contra G_to_GK

def reverseDeduction {fc : FrameClass} {Γ : Context Atom} {A B : Formula Atom}
    (h : DerivationTree fc Γ (A.imp B)) : DerivationTree fc (A :: Γ) B := by
  have h_weak : DerivationTree fc (A :: Γ) (A.imp B) :=
    DerivationTree.weakening _ _ _ h
      (by intro x hx; simp; right; exact hx)
  have h_assum : DerivationTree fc (A :: Γ) A := DerivationTree.assumption (A :: Γ) A (by simp)
  exact DerivationTree.modus_ponens (A :: Γ) A B h_weak h_assum

noncomputable def pastNecessitation {fc : FrameClass} (φ : Formula Atom)
    (d : DerivationTree fc [] φ) : DerivationTree fc [] (Formula.allPast φ) := by
  have h_swap : DerivationTree fc [] φ.swapTemporal := DerivationTree.temporal_duality _ d
  have g_swap : DerivationTree fc [] φ.swapTemporal.allFuture :=
    DerivationTree.temporal_necessitation _ h_swap
  have final : DerivationTree fc [] φ.swapTemporal.allFuture.swapTemporal :=
    DerivationTree.temporal_duality _ g_swap
  simp only [Formula.swapTemporal_allFuture, Formula.swapTemporal,
    Formula.swapTemporal_involution] at final
  exact final

noncomputable def pastKDist {fc : FrameClass} (A B : Formula Atom) :
    DerivationTree fc [] ((A.imp B).allPast.imp (A.allPast.imp B.allPast)) := by
  have fk : DerivationTree FrameClass.Base []
      ((A.swapTemporal.imp B.swapTemporal).allFuture.imp
       (A.swapTemporal.allFuture.imp B.swapTemporal.allFuture)) :=
    tempKDistLocal A.swapTemporal B.swapTemporal
  have fk_fc := DerivationTree.lift (FrameClass.base_le fc) fk
  have td : DerivationTree fc []
      ((A.swapTemporal.imp B.swapTemporal).allFuture.imp
       (A.swapTemporal.allFuture.imp B.swapTemporal.allFuture)).swapTemporal :=
    DerivationTree.temporal_duality _ fk_fc
  simp only [Formula.swapTemporal_allFuture,
    Formula.swapTemporal, Formula.swapTemporal_involution] at td
  exact td

noncomputable def generalizedModalK {fc : FrameClass} :
    (Γ : Context Atom) → (φ : Formula Atom) →
    (h : DerivationTree fc Γ φ) →
    (DerivationTree fc (Context.map Formula.box Γ) (Formula.box φ))
  | [], φ, h => DerivationTree.necessitation φ h
  | A :: Γ', φ, h =>
    let h_deduction := Cslib.Logic.Bimodal.Metalogic.Core.deductionTheorem Γ' A φ h
    let ih_res := generalizedModalK Γ' (A.imp φ) h_deduction
    let k_dist : DerivationTree fc [] ((Formula.box (A.imp φ)).imp ((Formula.box A).imp (Formula.box φ))) :=
      DerivationTree.axiom [] _ (Axiom.modal_k_dist A φ) trivial
    let k_dist_weak :=
      DerivationTree.weakening [] (Context.map Formula.box Γ') _ k_dist (List.nil_subset _)
    let h_mp :=
      DerivationTree.modus_ponens _ _ _ k_dist_weak ih_res
    reverseDeduction h_mp

noncomputable def generalizedTemporalK {fc : FrameClass} :
    (Γ : Context Atom) → (φ : Formula Atom) →
    (h : DerivationTree fc Γ φ) →
    (DerivationTree fc (Context.map Formula.allFuture Γ) (Formula.allFuture φ))
  | [], φ, h => DerivationTree.temporal_necessitation φ h
  | A :: Γ', φ, h =>
    let h_deduction := Cslib.Logic.Bimodal.Metalogic.Core.deductionTheorem Γ' A φ h
    let ih_res := generalizedTemporalK Γ' (A.imp φ) h_deduction
    let k_dist_base := tempKDistLocal A φ
    let k_dist := DerivationTree.lift (FrameClass.base_le fc) k_dist_base
    let k_dist_weak :=
      DerivationTree.weakening [] (Context.map Formula.allFuture Γ') _ k_dist (List.nil_subset _)
    let h_mp :=
      DerivationTree.modus_ponens _ _ _ k_dist_weak ih_res
    reverseDeduction h_mp

noncomputable def generalizedPastK {fc : FrameClass} :
    (Γ : Context Atom) → (φ : Formula Atom) →
    (h : DerivationTree fc Γ φ) →
    (DerivationTree fc (Context.map Formula.allPast Γ) (Formula.allPast φ))
  | [], φ, h => pastNecessitation φ h
  | A :: Γ', φ, h =>
    let h_deduction := Cslib.Logic.Bimodal.Metalogic.Core.deductionTheorem Γ' A φ h
    let ih_res := generalizedPastK Γ' (A.imp φ) h_deduction
    let k_dist := pastKDist (fc := fc) A φ
    let k_dist_weak :=
      DerivationTree.weakening [] (Context.map Formula.allPast Γ') _ k_dist (List.nil_subset _)
    let h_mp :=
      DerivationTree.modus_ponens _ _ _ k_dist_weak ih_res
    reverseDeduction h_mp

end Cslib.Logic.Bimodal.Theorems
