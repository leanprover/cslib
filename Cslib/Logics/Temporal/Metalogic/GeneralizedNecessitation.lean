/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Temporal.Metalogic.MCS
public import Cslib.Logics.Temporal.Metalogic.PropositionalHelpers

/-!
# Generalized Necessitation for Temporal Logic

Temporal versions of generalized temporal K, past K, past necessitation,
tempKDistDerived, and pastKDist at the DerivationTree level.

## References

* Ported from Cslib/Logics/Bimodal/Theorems/GeneralizedNecessitation.lean
-/

set_option linter.style.emptyLine false
set_option maxHeartbeats 400000

@[expose] public section

namespace Cslib.Logic.Temporal.Metalogic

open Cslib.Logic.Temporal

variable {Atom : Type*}

/-! ## Imp Trans helper -/

/-- Transitivity of implication at FrameClass.Base level.
    Delegates to `Metalogic.impTrans` from PropositionalHelpers. -/
noncomputable abbrev impTransBase {A B C : Formula Atom}
    (h1 : DerivationTree FrameClass.Base [] (A → B))
    (h2 : DerivationTree FrameClass.Base [] (B → C)) :
    DerivationTree FrameClass.Base [] (A → C) :=
  impTrans h1 h2

/-- Reverse deduction: from Γ ⊢ A → B derive A :: Γ ⊢ B. -/
noncomputable def reverseDeduction {Γ : Context Atom} {A B : Formula Atom}
    (h : DerivationTree FrameClass.Base Γ (A → B)) :
    DerivationTree FrameClass.Base (A :: Γ) B := by
  have h_weak : DerivationTree FrameClass.Base (A :: Γ) (A.imp B) :=
    DerivationTree.weakening _ _ _ h
      (by intro x hx; simp; right; exact hx)
  have h_assum : DerivationTree FrameClass.Base (A :: Γ) A :=
    DerivationTree.assumption (A :: Γ) A (by simp)
  exact DerivationTree.modus_ponens (A :: Γ) A B h_weak h_assum

/-! ## Contrapositive -/

/-- Derive ⊢ (A→B) → (¬B→¬A) (contraposition).
    Delegates to Foundations via wrap/unwrap. -/
noncomputable def contraposeImp (A B : Formula Atom) :
    DerivationTree FrameClass.Base [] ((A.imp B).imp (B.neg.imp A.neg)) :=
  unwrap (@Cslib.Logic.Theorems.Propositional.Connectives.contrapose_imp
    _ _ _ Temporal.HilbertBX _ _ (φ := A) (ψ := B))

/-- From ⊢ A → B derive ⊢ ¬B → ¬A (contraposition of a proof).
    Delegates to Foundations via wrap/unwrap. -/
noncomputable def contraposition {A B : Formula Atom}
    (h : DerivationTree FrameClass.Base [] (A.imp B)) :
    DerivationTree FrameClass.Base [] (B.neg.imp A.neg) :=
  unwrap (Cslib.Logic.Theorems.Propositional.Connectives.contraposition (wrap h))

/-! ## Past Necessitation -/

/-- Past necessitation: from ⊢ φ derive ⊢ H(φ). -/
noncomputable def pastNecessitation (φ : Formula Atom)
    (d : DerivationTree FrameClass.Base [] φ) :
    DerivationTree FrameClass.Base [] (Formula.allPast φ) := by
  have h_swap : DerivationTree FrameClass.Base [] φ.swapTemporal :=
    DerivationTree.temporal_duality _ d
  have g_swap : DerivationTree FrameClass.Base [] φ.swapTemporal.allFuture :=
    DerivationTree.temporal_necessitation _ h_swap
  have final : DerivationTree FrameClass.Base [] φ.swapTemporal.allFuture.swapTemporal :=
    DerivationTree.temporal_duality _ g_swap
  simp only [Formula.swapTemporal_allFuture, Formula.swapTemporal,
    Formula.swapTemporal_involution] at final
  exact final

/-! ## K-distribution -/

/-- G-distribution at DerivationTree level: ⊢ G(φ→ψ) → (G(φ) → G(ψ)). -/
noncomputable def tempKDistDerived (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp ψ).allFuture.imp (φ.allFuture.imp ψ.allFuture)) := by
  have neg_contra : DerivationTree FrameClass.Base [] ((ψ.neg.imp φ.neg).neg.imp (φ.imp ψ).neg) :=
    DerivationTree.modus_ponens [] _ _ (contraposeImp (φ.imp ψ) (ψ.neg.imp φ.neg))
      (contraposeImp φ ψ)
  have F_step : DerivationTree FrameClass.Base []
      ((Formula.someFuture (ψ.neg.imp φ.neg).neg).imp (Formula.someFuture (φ.imp ψ).neg)) :=
    DerivationTree.modus_ponens [] _ _
      (DerivationTree.axiom [] _
        (Axiom.right_mono_until (ψ.neg.imp φ.neg).neg (φ.imp ψ).neg Formula.top) trivial)
      (DerivationTree.temporal_necessitation _ neg_contra)
  have G_contra := contraposition F_step
  have G_to_GK := impTransBase
    (DerivationTree.axiom [] _ (Axiom.right_mono_until ψ.neg φ.neg Formula.top) trivial)
    (contraposeImp (Formula.someFuture ψ.neg) (Formula.someFuture φ.neg))
  exact impTransBase G_contra G_to_GK

/-- H-distribution at DerivationTree level: ⊢ H(φ→ψ) → (H(φ) → H(ψ)). -/
noncomputable def pastKDist (A B : Formula Atom) :
    DerivationTree FrameClass.Base [] ((A.imp B).allPast.imp (A.allPast.imp B.allPast)) := by
  have fk : DerivationTree FrameClass.Base []
      ((A.swapTemporal.imp B.swapTemporal).allFuture.imp
       (A.swapTemporal.allFuture.imp B.swapTemporal.allFuture)) :=
    tempKDistDerived A.swapTemporal B.swapTemporal
  have td : DerivationTree FrameClass.Base []
      ((A.swapTemporal.imp B.swapTemporal).allFuture.imp
       (A.swapTemporal.allFuture.imp B.swapTemporal.allFuture)).swapTemporal :=
    DerivationTree.temporal_duality _ fk
  simp only [Formula.swapTemporal_allFuture,
    Formula.swapTemporal, Formula.swapTemporal_involution] at td
  exact td

/-! ## Generalized K -/

/-- Generalized temporal K: from L ⊢ φ derive G(L) ⊢ G(φ). -/
noncomputable def generalizedTemporalK :
    (Γ : Context Atom) → (φ : Formula Atom) →
    (h : DerivationTree FrameClass.Base Γ φ) →
    (DerivationTree FrameClass.Base (Context.map Formula.allFuture Γ) (Formula.allFuture φ))
  | [], φ, h => DerivationTree.temporal_necessitation φ h
  | A :: Γ', φ, h =>
    let h_deduction := deductionTheorem Γ' A φ h
    let ih_res := generalizedTemporalK Γ' (A → φ) h_deduction
    let k_dist := tempKDistDerived A φ
    let k_dist_weak :=
      DerivationTree.weakening [] (Context.map Formula.allFuture Γ') _ k_dist (List.nil_subset _)
    let h_mp :=
      DerivationTree.modus_ponens _ _ _ k_dist_weak ih_res
    reverseDeduction h_mp

/-- Generalized past K: from L ⊢ φ derive H(L) ⊢ H(φ). -/
noncomputable def generalizedPastK :
    (Γ : Context Atom) → (φ : Formula Atom) →
    (h : DerivationTree FrameClass.Base Γ φ) →
    (DerivationTree FrameClass.Base (Context.map Formula.allPast Γ) (Formula.allPast φ))
  | [], φ, h => pastNecessitation φ h
  | A :: Γ', φ, h =>
    let h_deduction := deductionTheorem Γ' A φ h
    let ih_res := generalizedPastK Γ' (A → φ) h_deduction
    let k_dist := pastKDist A φ
    let k_dist_weak :=
      DerivationTree.weakening [] (Context.map Formula.allPast Γ') _ k_dist (List.nil_subset _)
    let h_mp :=
      DerivationTree.modus_ponens _ _ _ k_dist_weak ih_res
    reverseDeduction h_mp

end Cslib.Logic.Temporal.Metalogic
