/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import Cslib.Logics.Temporal.Metalogic.MCS

/-!
# Generalized Necessitation for Temporal Logic

Temporal versions of generalized temporal K, past K, past necessitation,
temp_k_dist_derived, and past_k_dist at the DerivationTree level.

## References

* Ported from Cslib/Logics/Bimodal/Theorems/GeneralizedNecessitation.lean
-/

set_option linter.style.emptyLine false
set_option maxHeartbeats 400000

namespace Cslib.Logic.Temporal.Metalogic

open Cslib.Logic.Temporal

variable {Atom : Type*}

/-! ## Imp Trans helper -/

/-- Transitivity of implication at FrameClass.Base level. -/
private noncomputable def imp_trans_base {A B C : Formula Atom}
    (h1 : DerivationTree FrameClass.Base [] (A.imp B))
    (h2 : DerivationTree FrameClass.Base [] (B.imp C)) :
    DerivationTree FrameClass.Base [] (A.imp C) := by
  have s_axiom := DerivationTree.axiom (fc := FrameClass.Base) [] _
      (Axiom.imp_s (B.imp C) A) trivial
  have h3 := DerivationTree.modus_ponens [] (B.imp C) (A.imp (B.imp C)) s_axiom h2
  have k_axiom := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.imp_k A B C) trivial
  have h4 := DerivationTree.modus_ponens [] (A.imp (B.imp C)) ((A.imp B).imp (A.imp C)) k_axiom h3
  exact DerivationTree.modus_ponens [] (A.imp B) (A.imp C) h4 h1

/-- Reverse deduction: from Γ ⊢ A → B derive A :: Γ ⊢ B. -/
private noncomputable def reverse_deduction {Γ : Context Atom} {A B : Formula Atom}
    (h : DerivationTree FrameClass.Base Γ (A.imp B)) :
    DerivationTree FrameClass.Base (A :: Γ) B := by
  have h_weak : DerivationTree FrameClass.Base (A :: Γ) (A.imp B) :=
    DerivationTree.weakening _ _ _ h
      (by intro x hx; simp; right; exact hx)
  have h_assum : DerivationTree FrameClass.Base (A :: Γ) A :=
    DerivationTree.assumption (A :: Γ) A (by simp)
  exact DerivationTree.modus_ponens (A :: Γ) A B h_weak h_assum

/-! ## Contrapositive -/

/-- Derive ⊢ (A→B) → (¬B→¬A) (contraposition). -/
private noncomputable def contrapose_imp (A B : Formula Atom) :
    DerivationTree FrameClass.Base [] ((A.imp B).imp (B.neg.imp A.neg)) := by
  let ctx := [A, Formula.neg B, A.imp B]
  have d_B : DerivationTree FrameClass.Base ctx B :=
    .modus_ponens ctx A B
      (.assumption ctx (A.imp B) (by simp [List.mem_cons, ctx]))
      (.assumption ctx A (by simp [List.mem_cons, ctx]))
  have d_bot : DerivationTree FrameClass.Base ctx Formula.bot :=
    .modus_ponens ctx B Formula.bot
      (.assumption ctx (Formula.neg B) (by simp [List.mem_cons, ctx]))
      d_B
  have d1 := deduction_theorem [Formula.neg B, A.imp B] A Formula.bot d_bot
  have d2 := deduction_theorem [A.imp B] (Formula.neg B) (Formula.neg A) d1
  exact deduction_theorem [] (A.imp B) (B.neg.imp A.neg) d2

/-- From ⊢ A → B derive ⊢ ¬B → ¬A (contraposition of a proof). -/
noncomputable def contraposition {A B : Formula Atom}
    (h : DerivationTree FrameClass.Base [] (A.imp B)) :
    DerivationTree FrameClass.Base [] (B.neg.imp A.neg) :=
  DerivationTree.modus_ponens [] _ _ (contrapose_imp A B) h

/-! ## Past Necessitation -/

/-- Past necessitation: from ⊢ φ derive ⊢ H(φ). -/
noncomputable def past_necessitation (φ : Formula Atom)
    (d : DerivationTree FrameClass.Base [] φ) :
    DerivationTree FrameClass.Base [] (Formula.all_past φ) := by
  have h_swap : DerivationTree FrameClass.Base [] φ.swap_temporal :=
    DerivationTree.temporal_duality _ d
  have g_swap : DerivationTree FrameClass.Base [] φ.swap_temporal.all_future :=
    DerivationTree.temporal_necessitation _ h_swap
  have final : DerivationTree FrameClass.Base [] φ.swap_temporal.all_future.swap_temporal :=
    DerivationTree.temporal_duality _ g_swap
  simp only [Formula.swap_temporal_all_future, Formula.swap_temporal,
    Formula.swap_temporal_involution] at final
  exact final

/-! ## K-distribution -/

/-- G-distribution at DerivationTree level: ⊢ G(φ→ψ) → (G(φ) → G(ψ)). -/
noncomputable def temp_k_dist_derived (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp ψ).all_future.imp (φ.all_future.imp ψ.all_future)) := by
  have neg_contra : DerivationTree FrameClass.Base [] ((ψ.neg.imp φ.neg).neg.imp (φ.imp ψ).neg) :=
    DerivationTree.modus_ponens [] _ _ (contrapose_imp (φ.imp ψ) (ψ.neg.imp φ.neg))
      (contrapose_imp φ ψ)
  have F_step : DerivationTree FrameClass.Base []
      ((Formula.some_future (ψ.neg.imp φ.neg).neg).imp (Formula.some_future (φ.imp ψ).neg)) :=
    DerivationTree.modus_ponens [] _ _
      (DerivationTree.axiom [] _
        (Axiom.right_mono_until (ψ.neg.imp φ.neg).neg (φ.imp ψ).neg Formula.top) trivial)
      (DerivationTree.temporal_necessitation _ neg_contra)
  have G_contra := contraposition F_step
  have G_to_GK := imp_trans_base
    (DerivationTree.axiom [] _ (Axiom.right_mono_until ψ.neg φ.neg Formula.top) trivial)
    (contrapose_imp (Formula.some_future ψ.neg) (Formula.some_future φ.neg))
  exact imp_trans_base G_contra G_to_GK

/-- H-distribution at DerivationTree level: ⊢ H(φ→ψ) → (H(φ) → H(ψ)). -/
noncomputable def past_k_dist (A B : Formula Atom) :
    DerivationTree FrameClass.Base [] ((A.imp B).all_past.imp (A.all_past.imp B.all_past)) := by
  have fk : DerivationTree FrameClass.Base []
      ((A.swap_temporal.imp B.swap_temporal).all_future.imp
       (A.swap_temporal.all_future.imp B.swap_temporal.all_future)) :=
    temp_k_dist_derived A.swap_temporal B.swap_temporal
  have td : DerivationTree FrameClass.Base []
      ((A.swap_temporal.imp B.swap_temporal).all_future.imp
       (A.swap_temporal.all_future.imp B.swap_temporal.all_future)).swap_temporal :=
    DerivationTree.temporal_duality _ fk
  simp only [Formula.swap_temporal_all_future,
    Formula.swap_temporal, Formula.swap_temporal_involution] at td
  exact td

/-! ## Generalized K -/

/-- Generalized temporal K: from L ⊢ φ derive G(L) ⊢ G(φ). -/
noncomputable def generalized_temporal_k :
    (Γ : Context Atom) → (φ : Formula Atom) →
    (h : DerivationTree FrameClass.Base Γ φ) →
    (DerivationTree FrameClass.Base (Context.map Formula.all_future Γ) (Formula.all_future φ))
  | [], φ, h => DerivationTree.temporal_necessitation φ h
  | A :: Γ', φ, h =>
    let h_deduction := deduction_theorem Γ' A φ h
    let ih_res := generalized_temporal_k Γ' (A.imp φ) h_deduction
    let k_dist := temp_k_dist_derived A φ
    let k_dist_weak :=
      DerivationTree.weakening [] (Context.map Formula.all_future Γ') _ k_dist (List.nil_subset _)
    let h_mp :=
      DerivationTree.modus_ponens _ _ _ k_dist_weak ih_res
    reverse_deduction h_mp

/-- Generalized past K: from L ⊢ φ derive H(L) ⊢ H(φ). -/
noncomputable def generalized_past_k :
    (Γ : Context Atom) → (φ : Formula Atom) →
    (h : DerivationTree FrameClass.Base Γ φ) →
    (DerivationTree FrameClass.Base (Context.map Formula.all_past Γ) (Formula.all_past φ))
  | [], φ, h => past_necessitation φ h
  | A :: Γ', φ, h =>
    let h_deduction := deduction_theorem Γ' A φ h
    let ih_res := generalized_past_k Γ' (A.imp φ) h_deduction
    let k_dist := past_k_dist A φ
    let k_dist_weak :=
      DerivationTree.weakening [] (Context.map Formula.all_past Γ') _ k_dist (List.nil_subset _)
    let h_mp :=
      DerivationTree.modus_ponens _ _ _ k_dist_weak ih_res
    reverse_deduction h_mp

end Cslib.Logic.Temporal.Metalogic
