/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import Cslib.Logics.Bimodal.ProofSystem.Derivation
import Cslib.Logics.Bimodal.Syntax.Formula
import Cslib.Logics.Bimodal.Theorems.Combinators
import Cslib.Logics.Bimodal.Theorems.GeneralizedNecessitation
import Cslib.Logics.Bimodal.Theorems.Propositional.Connectives

/-!
# Temporal Derived Theorems from BX Axioms

Temporal theorems derived from the Burgess-Xu (BX) axiom system.

Ported from BimodalLogic/Theories/Bimodal/Theorems/TemporalDerived.lean
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Cslib.Logic.Bimodal.Theorems.TemporalDerived

open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Theorems.Combinators
open Cslib.Logic.Bimodal.Theorems.Propositional
open Cslib.Logic.Bimodal.Theorems

variable {Atom : Type*}

noncomputable section

section DerivedAxioms

private noncomputable def neg_contrapositive_imp_neg (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base [] ((ψ.neg.imp φ.neg).neg.imp (φ.imp ψ).neg) :=
  mp (contrapose_imp φ ψ) (contrapose_imp (φ.imp ψ) (ψ.neg.imp φ.neg))

private def top_and_intro (X : Formula Atom) :
    DerivationTree FrameClass.Base [] (X.imp (Formula.top.and X)) :=
  mp (identity Formula.bot) (pairing Formula.top X)

private noncomputable def F_neg_contra_imp_F_neg (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((Formula.some_future (ψ.neg.imp φ.neg).neg).imp
       (Formula.some_future (φ.imp ψ).neg)) :=
  mp (DerivationTree.temporal_necessitation _ (neg_contrapositive_imp_neg φ ψ))
     (DerivationTree.axiom [] _
       (Axiom.right_mono_until (ψ.neg.imp φ.neg).neg (φ.imp ψ).neg Formula.top) trivial)

private noncomputable def G_imp_to_G_contra (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp ψ).all_future.imp (ψ.neg.imp φ.neg).all_future) :=
  contraposition (F_neg_contra_imp_F_neg φ ψ)

private noncomputable def G_contra_to_GK (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((ψ.neg.imp φ.neg).all_future.imp (φ.all_future.imp ψ.all_future)) :=
  imp_trans
    (DerivationTree.axiom [] _ (Axiom.right_mono_until ψ.neg φ.neg Formula.top) trivial)
    (contrapose_imp (Formula.some_future ψ.neg) (Formula.some_future φ.neg))

noncomputable def temp_k_dist_derived (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp ψ).all_future.imp (φ.all_future.imp ψ.all_future)) :=
  imp_trans (G_imp_to_G_contra φ ψ) (G_contra_to_GK φ ψ)

private noncomputable def dne_lift_F (φ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((Formula.some_future (Formula.some_future φ.neg).neg.neg).imp
       (Formula.some_future (Formula.some_future φ.neg))) :=
  mp (DerivationTree.temporal_necessitation _ (double_negation (Formula.some_future φ.neg)))
     (DerivationTree.axiom [] _
       (Axiom.right_mono_until
         (Formula.some_future φ.neg).neg.neg (Formula.some_future φ.neg) Formula.top) trivial)

private noncomputable def FF_to_F_top_and (φ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((Formula.some_future (Formula.some_future φ.neg)).imp
       (Formula.some_future (Formula.top.and (Formula.some_future φ.neg)))) :=
  mp (DerivationTree.temporal_necessitation _ (top_and_intro (Formula.some_future φ.neg)))
     (DerivationTree.axiom [] _
       (Axiom.right_mono_until
         (Formula.some_future φ.neg)
         (Formula.top.and (Formula.some_future φ.neg)) Formula.top) trivial)

private def F_top_and_absorb (φ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((Formula.some_future (Formula.top.and (Formula.some_future φ.neg))).imp
       (Formula.some_future φ.neg)) :=
  DerivationTree.axiom [] _ (Axiom.absorb_until Formula.top φ.neg) trivial

noncomputable def temp_4_derived (φ : Formula Atom) :
    DerivationTree FrameClass.Base []
      (φ.all_future.imp φ.all_future.all_future) :=
  contraposition (imp_trans (imp_trans (dne_lift_F φ) (FF_to_F_top_and φ)) (F_top_and_absorb φ))

end DerivedAxioms

noncomputable def G_distribution (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp ψ).all_future.imp (φ.all_future.imp ψ.all_future)) :=
  temp_k_dist_derived φ ψ

noncomputable def H_distribution (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp ψ).all_past.imp (φ.all_past.imp ψ.all_past)) :=
  past_k_dist φ ψ

noncomputable def G_transitivity (φ : Formula Atom) :
    DerivationTree FrameClass.Base []
      (φ.all_future.imp φ.all_future.all_future) :=
  temp_4_derived φ

noncomputable def H_transitivity (φ : Formula Atom) :
    DerivationTree FrameClass.Base []
      (φ.all_past.imp φ.all_past.all_past) := by
  let ψ := φ.swap_temporal
  have h1 := temp_4_derived ψ
  have h2 := DerivationTree.temporal_duality _ h1
  simp only [Formula.swap_temporal_all_future, Formula.swap_temporal] at h2
  have h_inv : ψ.swap_temporal = φ := Formula.swap_temporal_involution φ
  rw [h_inv] at h2
  exact h2

def connect_future_thm (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] (φ.imp (φ.some_past.all_future)) :=
  DerivationTree.axiom [] _ (Axiom.connect_future φ) trivial

def connect_past_thm (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] (φ.imp (φ.some_future.all_past)) :=
  DerivationTree.axiom [] _ (Axiom.connect_past φ) trivial

def G_implies_G_id (a : Formula Atom) :
    DerivationTree FrameClass.Base []
      (a.all_future.imp (a.imp a).all_future) :=
  mp (DerivationTree.temporal_necessitation _ (identity a))
     (DerivationTree.axiom [] _ (Axiom.imp_s (a.imp a).all_future a.all_future) trivial)

def until_implies_some_future (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((Formula.untl ψ φ).imp (Formula.some_future ψ)) :=
  DerivationTree.axiom [] _ (Axiom.until_F φ ψ) trivial

def since_implies_some_past (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((Formula.snce ψ φ).imp (Formula.some_past ψ)) :=
  DerivationTree.axiom [] _ (Axiom.since_P φ ψ) trivial

def until_imp_F (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((Formula.untl ψ φ).imp (Formula.some_future ψ)) :=
  DerivationTree.axiom [] _ (Axiom.until_F φ ψ) trivial

def since_imp_P (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((Formula.snce ψ φ).imp (Formula.some_past ψ)) :=
  DerivationTree.axiom [] _ (Axiom.since_P φ ψ) trivial

noncomputable def contrapositive_thm (A B : Formula Atom) :
    DerivationTree FrameClass.Base [] ((A.imp B).imp (B.neg.imp A.neg)) :=
  mp b_combinator (theorem_flip (A := (B.imp Formula.bot)) (B := (A.imp B)) (C := (A.imp Formula.bot)))

private noncomputable def ctx_mp {Γ : Context Atom} {A B : Formula Atom}
    (h1 : DerivationTree FrameClass.Base Γ (A.imp B))
    (h2 : DerivationTree FrameClass.Base Γ A) :
    DerivationTree FrameClass.Base Γ B :=
  DerivationTree.modus_ponens Γ A B h1 h2

private noncomputable def ctx_thm {Γ : Context Atom} {A : Formula Atom}
    (h : DerivationTree FrameClass.Base [] A) :
    DerivationTree FrameClass.Base Γ A :=
  DerivationTree.weakening [] Γ A h (List.nil_subset Γ)

noncomputable def formula_or_comm (A B : Formula Atom) :
    DerivationTree FrameClass.Base [] ((A.or B).imp (B.or A)) := by
  apply Cslib.Logic.Bimodal.Metalogic.Core.deduction_theorem [] (A.neg.imp B) (B.neg.imp A)
  apply Cslib.Logic.Bimodal.Metalogic.Core.deduction_theorem [A.neg.imp B] B.neg A
  have h1 : DerivationTree FrameClass.Base [B.neg, A.neg.imp B] (A.neg.imp B) :=
    DerivationTree.assumption _ _ (by simp)
  have h2 : DerivationTree FrameClass.Base [B.neg, A.neg.imp B] B.neg :=
    DerivationTree.assumption _ _ (by simp)
  have h3 := ctx_mp (ctx_mp (ctx_thm b_combinator) h2) h1
  exact ctx_mp (ctx_thm (double_negation A)) h3

section TemporalMonotonicity

def F_mono (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp ψ).all_future.imp (φ.some_future.imp ψ.some_future)) :=
  DerivationTree.axiom [] _ (Axiom.right_mono_until φ ψ Formula.top) trivial

def P_mono (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp ψ).all_past.imp (φ.some_past.imp ψ.some_past)) :=
  DerivationTree.axiom [] _ (Axiom.right_mono_since φ ψ Formula.top) trivial

noncomputable abbrev G_mono (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp ψ).all_future.imp (φ.all_future.imp ψ.all_future)) :=
  G_distribution φ ψ

noncomputable abbrev H_mono (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp ψ).all_past.imp (φ.all_past.imp ψ.all_past)) :=
  H_distribution φ ψ

end TemporalMonotonicity

section UntilSinceStructural

def until_mono_guard (φ χ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp χ).all_future.imp ((Formula.untl ψ φ).imp (Formula.untl ψ χ))) :=
  DerivationTree.axiom [] _ (Axiom.left_mono_until_G φ χ ψ) trivial

def since_mono_guard (φ χ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp χ).all_past.imp ((Formula.snce ψ φ).imp (Formula.snce ψ χ))) :=
  DerivationTree.axiom [] _ (Axiom.left_mono_since_H φ χ ψ) trivial

def until_mono_event (φ ψ χ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp ψ).all_future.imp ((Formula.untl φ χ).imp (Formula.untl ψ χ))) :=
  DerivationTree.axiom [] _ (Axiom.right_mono_until φ ψ χ) trivial

def since_mono_event (φ ψ χ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp ψ).all_past.imp ((Formula.snce φ χ).imp (Formula.snce ψ χ))) :=
  DerivationTree.axiom [] _ (Axiom.right_mono_since φ ψ χ) trivial

end UntilSinceStructural

section TemporalDuality

def F_neg_G (φ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.neg.some_future).imp φ.all_future.neg) :=
  dni (φ.neg.some_future)

def P_neg_H (φ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.neg.some_past).imp φ.all_past.neg) :=
  dni (φ.neg.some_past)

end TemporalDuality

section DistributionVariants

noncomputable def G_and_intro (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      (φ.all_future.imp (ψ.all_future.imp (φ.and ψ).all_future)) :=
  let g_pair := DerivationTree.temporal_necessitation _ (pairing (fc := FrameClass.Base) φ ψ)
  let step1 := mp g_pair (G_distribution φ (ψ.imp (φ.and ψ)))
  imp_trans step1 (G_distribution ψ (φ.and ψ))

noncomputable def H_and_intro (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      (φ.all_past.imp (ψ.all_past.imp (φ.and ψ).all_past)) :=
  let h_pair := past_necessitation _ (pairing (fc := FrameClass.Base) φ ψ)
  let step1 := mp h_pair (H_distribution φ (ψ.imp (φ.and ψ)))
  imp_trans step1 (H_distribution ψ (φ.and ψ))

noncomputable def G_imp_trans (φ ψ χ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp ψ).all_future.imp ((ψ.imp χ).all_future.imp (φ.imp χ).all_future)) :=
  let g_b := DerivationTree.temporal_necessitation _
    (@b_combinator Atom .Base (A := φ) (B := ψ) (C := χ))
  let step1 := mp g_b (G_distribution (ψ.imp χ) ((φ.imp ψ).imp (φ.imp χ)))
  let step2 := imp_trans step1 (G_distribution (φ.imp ψ) (φ.imp χ))
  mp step2 (@theorem_flip Atom .Base
    (A := (ψ.imp χ).all_future)
    (B := (φ.imp ψ).all_future)
    (C := (φ.imp χ).all_future))

noncomputable def H_imp_trans (φ ψ χ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp ψ).all_past.imp ((ψ.imp χ).all_past.imp (φ.imp χ).all_past)) :=
  let h_b := past_necessitation _
    (@b_combinator Atom .Base (A := φ) (B := ψ) (C := χ))
  let step1 := mp h_b (H_distribution (ψ.imp χ) ((φ.imp ψ).imp (φ.imp χ)))
  let step2 := imp_trans step1 (H_distribution (φ.imp ψ) (φ.imp χ))
  mp step2 (@theorem_flip Atom .Base
    (A := (ψ.imp χ).all_past)
    (B := (φ.imp ψ).all_past)
    (C := (φ.imp χ).all_past))

end DistributionVariants

section TemporalContraposition

noncomputable def G_contrapose (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp ψ).all_future.imp (ψ.neg.imp φ.neg).all_future) :=
  let g_cp := DerivationTree.temporal_necessitation _ (contrapose_imp φ ψ)
  mp g_cp (G_distribution (φ.imp ψ) (ψ.neg.imp φ.neg))

noncomputable def H_contrapose (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp ψ).all_past.imp (ψ.neg.imp φ.neg).all_past) :=
  let h_cp := past_necessitation _ (contrapose_imp φ ψ)
  mp h_cp (H_distribution (φ.imp ψ) (ψ.neg.imp φ.neg))

end TemporalContraposition

section FuturePastChains

noncomputable def connect_future_G (φ : Formula Atom) :
    DerivationTree FrameClass.Base []
      (φ.all_future.imp (φ.some_past.all_future).all_future) :=
  let g_cf := DerivationTree.temporal_necessitation _ (connect_future_thm φ)
  mp g_cf (G_distribution φ (φ.some_past.all_future))

noncomputable def connect_past_H (φ : Formula Atom) :
    DerivationTree FrameClass.Base []
      (φ.all_past.imp (φ.some_future.all_past).all_past) :=
  let h_cp := past_necessitation _ (connect_past_thm φ)
  mp h_cp (H_distribution φ (φ.some_future.all_past))

noncomputable def connect_future_chain (φ : Formula Atom) :
    DerivationTree FrameClass.Base []
      (φ.imp ((φ.some_past.some_future.all_past).all_future)) :=
  let step1 := DerivationTree.temporal_necessitation _ (connect_past_thm φ.some_past)
  let step2 := mp step1 (G_distribution φ.some_past (φ.some_past.some_future.all_past))
  imp_trans (connect_future_thm φ) step2

noncomputable def connect_past_chain (φ : Formula Atom) :
    DerivationTree FrameClass.Base []
      (φ.imp ((φ.some_future.some_past.all_future).all_past)) :=
  let step1 := past_necessitation _ (connect_future_thm φ.some_future)
  let step2 := mp step1 (H_distribution φ.some_future (φ.some_future.some_past.all_future))
  imp_trans (connect_past_thm φ) step2

end FuturePastChains

section ConjunctionElimination

noncomputable def always_to_present (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] (φ.always.imp φ) :=
  imp_trans (rce_imp φ.all_past (φ.and φ.all_future)) (lce_imp φ φ.all_future)

noncomputable def present_to_sometimes (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] (φ.imp φ.sometimes) := by
  exact imp_trans (dni φ) (contraposition (always_to_present φ.neg))

noncomputable def weakFutureLeft (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] ((φ.and φ.all_future).imp φ) :=
  lce_imp φ φ.all_future

noncomputable def weakFutureRight (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] ((φ.and φ.all_future).imp φ.all_future) :=
  rce_imp φ φ.all_future

noncomputable def weakPastLeft (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] ((φ.and φ.all_past).imp φ) :=
  lce_imp φ φ.all_past

noncomputable def weakPastRight (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] ((φ.and φ.all_past).imp φ.all_past) :=
  rce_imp φ φ.all_past

noncomputable def always_imp_all_future (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] (φ.always.imp φ.all_future) :=
  imp_trans (rce_imp φ.all_past (φ.and φ.all_future)) (rce_imp φ φ.all_future)

noncomputable def always_imp_all_past (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] (φ.always.imp φ.all_past) :=
  lce_imp φ.all_past (φ.and φ.all_future)

end ConjunctionElimination

end -- noncomputable section

end Cslib.Logic.Bimodal.Theorems.TemporalDerived
