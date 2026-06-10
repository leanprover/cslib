/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.ProofSystem.Derivation
public import Cslib.Logics.Bimodal.Syntax.Formula
public import Cslib.Logics.Bimodal.Theorems.Combinators
public import Cslib.Logics.Bimodal.Theorems.GeneralizedNecessitation
public import Cslib.Logics.Bimodal.Theorems.Propositional.Connectives
public import Cslib.Foundations.Logic.Theorems.Temporal.TemporalDerived

/-!
# Temporal Derived Theorems from BX Axioms

Temporal theorems derived from the Burgess-Xu (BX) axiom system.

Ported from BimodalLogic/Theories/Bimodal/Theorems/TemporalDerived.lean
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false

@[expose] public section

namespace Cslib.Logic.Bimodal.Theorems.TemporalDerived

open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Theorems.Combinators
open Cslib.Logic.Bimodal.Theorems.Propositional
open Cslib.Logic.Bimodal.Theorems
open Cslib.Logic.Bimodal.Theorems.Perpetuity (unwrap)

variable {Atom : Type*}

noncomputable section

section DerivedAxioms

noncomputable def neg_contrapositive_imp_neg (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base [] ((ψ.neg.imp φ.neg).neg.imp (φ.imp ψ).neg) :=
  mp (contrapose_imp φ ψ) (contrapose_imp (φ.imp ψ) (ψ.neg.imp φ.neg))

def top_and_intro (X : Formula Atom) :
    DerivationTree FrameClass.Base [] (X.imp (Formula.top.and X)) :=
  mp (identity Formula.bot) (pairing Formula.top X)

noncomputable def F_neg_contra_imp_F_neg (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((Formula.someFuture (ψ.neg.imp φ.neg).neg).imp
       (Formula.someFuture (φ.imp ψ).neg)) :=
  mp (DerivationTree.temporal_necessitation _ (neg_contrapositive_imp_neg φ ψ))
     (DerivationTree.axiom [] _
       (Axiom.right_mono_until (ψ.neg.imp φ.neg).neg (φ.imp ψ).neg Formula.top) trivial)

noncomputable def G_imp_to_G_contra (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp ψ).allFuture.imp (ψ.neg.imp φ.neg).allFuture) :=
  contraposition (F_neg_contra_imp_F_neg φ ψ)

noncomputable def G_contra_to_GK (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((ψ.neg.imp φ.neg).allFuture.imp (φ.allFuture.imp ψ.allFuture)) :=
  imp_trans
    (DerivationTree.axiom [] _ (Axiom.right_mono_until ψ.neg φ.neg Formula.top) trivial)
    (contrapose_imp (Formula.someFuture ψ.neg) (Formula.someFuture φ.neg))

noncomputable def temp_k_dist_derived (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp ψ).allFuture.imp (φ.allFuture.imp ψ.allFuture)) :=
  imp_trans (G_imp_to_G_contra φ ψ) (G_contra_to_GK φ ψ)

noncomputable def dne_lift_F (φ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((Formula.someFuture (Formula.someFuture φ.neg).neg.neg).imp
       (Formula.someFuture (Formula.someFuture φ.neg))) :=
  mp (DerivationTree.temporal_necessitation _ (double_negation (Formula.someFuture φ.neg)))
     (DerivationTree.axiom [] _
       (Axiom.right_mono_until
         (Formula.someFuture φ.neg).neg.neg (Formula.someFuture φ.neg) Formula.top) trivial)

noncomputable def FF_to_F_top_and (φ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((Formula.someFuture (Formula.someFuture φ.neg)).imp
       (Formula.someFuture (Formula.top.and (Formula.someFuture φ.neg)))) :=
  mp (DerivationTree.temporal_necessitation _ (top_and_intro (Formula.someFuture φ.neg)))
     (DerivationTree.axiom [] _
       (Axiom.right_mono_until
         (Formula.someFuture φ.neg)
         (Formula.top.and (Formula.someFuture φ.neg)) Formula.top) trivial)

def F_top_and_absorb (φ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((Formula.someFuture (Formula.top.and (Formula.someFuture φ.neg))).imp
       (Formula.someFuture φ.neg)) :=
  DerivationTree.axiom [] _ (Axiom.absorb_until Formula.top φ.neg) trivial

noncomputable def temp_4_derived (φ : Formula Atom) :
    DerivationTree FrameClass.Base []
      (φ.allFuture.imp φ.allFuture.allFuture) :=
  contraposition (imp_trans (imp_trans (dne_lift_F φ) (FF_to_F_top_and φ)) (F_top_and_absorb φ))

end DerivedAxioms

noncomputable def G_distribution (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp ψ).allFuture.imp (φ.allFuture.imp ψ.allFuture)) :=
  unwrap (@Cslib.Logic.Theorems.Temporal.TemporalDerived.G_distribution
    _ _ _ _ _ Bimodal.HilbertTM _ _ (φ := φ) (ψ := ψ))

noncomputable def H_distribution (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp ψ).allPast.imp (φ.allPast.imp ψ.allPast)) :=
  unwrap (@Cslib.Logic.Theorems.Temporal.TemporalDerived.H_distribution
    _ _ _ _ _ Bimodal.HilbertTM _ _ (φ := φ) (ψ := ψ))

noncomputable def G_transitivity (φ : Formula Atom) :
    DerivationTree FrameClass.Base []
      (φ.allFuture.imp φ.allFuture.allFuture) :=
  temp_4_derived φ

noncomputable def H_transitivity (φ : Formula Atom) :
    DerivationTree FrameClass.Base []
      (φ.allPast.imp φ.allPast.allPast) := by
  let ψ := φ.swapTemporal
  have h1 := temp_4_derived ψ
  have h2 := DerivationTree.temporal_duality _ h1
  simp only [Formula.swapTemporal_allFuture, Formula.swapTemporal] at h2
  have h_inv : ψ.swapTemporal = φ := Formula.swapTemporal_involution φ
  rw [h_inv] at h2
  exact h2

def connect_future_thm (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] (φ.imp (φ.somePast.allFuture)) :=
  DerivationTree.axiom [] _ (Axiom.connect_future φ) trivial

def connect_past_thm (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] (φ.imp (φ.someFuture.allPast)) :=
  DerivationTree.axiom [] _ (Axiom.connect_past φ) trivial

def G_implies_G_id (a : Formula Atom) :
    DerivationTree FrameClass.Base []
      (a.allFuture.imp (a.imp a).allFuture) :=
  mp (DerivationTree.temporal_necessitation _ (identity a))
     (DerivationTree.axiom [] _ (Axiom.imp_s (a.imp a).allFuture a.allFuture) trivial)

def until_implies_someFuture (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((Formula.untl ψ φ).imp (Formula.someFuture ψ)) :=
  DerivationTree.axiom [] _ (Axiom.until_F φ ψ) trivial

def since_implies_somePast (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((Formula.snce ψ φ).imp (Formula.somePast ψ)) :=
  DerivationTree.axiom [] _ (Axiom.since_P φ ψ) trivial

def until_imp_F (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((Formula.untl ψ φ).imp (Formula.someFuture ψ)) :=
  DerivationTree.axiom [] _ (Axiom.until_F φ ψ) trivial

def since_imp_P (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((Formula.snce ψ φ).imp (Formula.somePast ψ)) :=
  DerivationTree.axiom [] _ (Axiom.since_P φ ψ) trivial

noncomputable def contrapositive_thm (A B : Formula Atom) :
    DerivationTree FrameClass.Base [] ((A.imp B).imp (B.neg.imp A.neg)) :=
  mp b_combinator (theorem_flip (A := (B.imp Formula.bot)) (B := (A.imp B)) (C := (A.imp Formula.bot)))

noncomputable def ctx_mp {Γ : Context Atom} {A B : Formula Atom}
    (h1 : DerivationTree FrameClass.Base Γ (A.imp B))
    (h2 : DerivationTree FrameClass.Base Γ A) :
    DerivationTree FrameClass.Base Γ B :=
  DerivationTree.modus_ponens Γ A B h1 h2

noncomputable def ctx_thm {Γ : Context Atom} {A : Formula Atom}
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
      ((φ.imp ψ).allFuture.imp (φ.someFuture.imp ψ.someFuture)) :=
  DerivationTree.axiom [] _ (Axiom.right_mono_until φ ψ Formula.top) trivial

def P_mono (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp ψ).allPast.imp (φ.somePast.imp ψ.somePast)) :=
  DerivationTree.axiom [] _ (Axiom.right_mono_since φ ψ Formula.top) trivial

noncomputable abbrev G_mono (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp ψ).allFuture.imp (φ.allFuture.imp ψ.allFuture)) :=
  G_distribution φ ψ

noncomputable abbrev H_mono (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp ψ).allPast.imp (φ.allPast.imp ψ.allPast)) :=
  H_distribution φ ψ

end TemporalMonotonicity

section UntilSinceStructural

def until_mono_guard (φ χ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp χ).allFuture.imp ((Formula.untl ψ φ).imp (Formula.untl ψ χ))) :=
  DerivationTree.axiom [] _ (Axiom.left_mono_until_G φ χ ψ) trivial

def since_mono_guard (φ χ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp χ).allPast.imp ((Formula.snce ψ φ).imp (Formula.snce ψ χ))) :=
  DerivationTree.axiom [] _ (Axiom.left_mono_since_H φ χ ψ) trivial

def until_mono_event (φ ψ χ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp ψ).allFuture.imp ((Formula.untl φ χ).imp (Formula.untl ψ χ))) :=
  DerivationTree.axiom [] _ (Axiom.right_mono_until φ ψ χ) trivial

def since_mono_event (φ ψ χ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp ψ).allPast.imp ((Formula.snce φ χ).imp (Formula.snce ψ χ))) :=
  DerivationTree.axiom [] _ (Axiom.right_mono_since φ ψ χ) trivial

end UntilSinceStructural

section TemporalDuality

def F_neg_G (φ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.neg.someFuture).imp φ.allFuture.neg) :=
  dni (φ.neg.someFuture)

def P_neg_H (φ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.neg.somePast).imp φ.allPast.neg) :=
  dni (φ.neg.somePast)

end TemporalDuality

section DistributionVariants

noncomputable def G_and_intro (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      (φ.allFuture.imp (ψ.allFuture.imp (φ.and ψ).allFuture)) :=
  unwrap (@Cslib.Logic.Theorems.Temporal.TemporalDerived.G_and_intro
    _ _ _ _ _ Bimodal.HilbertTM _ _ (φ := φ) (ψ := ψ))

noncomputable def H_and_intro (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      (φ.allPast.imp (ψ.allPast.imp (φ.and ψ).allPast)) :=
  unwrap (@Cslib.Logic.Theorems.Temporal.TemporalDerived.H_and_intro
    _ _ _ _ _ Bimodal.HilbertTM _ _ (φ := φ) (ψ := ψ))

noncomputable def G_imp_trans (φ ψ χ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp ψ).allFuture.imp ((ψ.imp χ).allFuture.imp (φ.imp χ).allFuture)) :=
  unwrap (@Cslib.Logic.Theorems.Temporal.TemporalDerived.G_imp_trans'
    _ _ _ _ _ Bimodal.HilbertTM _ _ (φ := φ) (ψ := ψ) (χ := χ))

noncomputable def H_imp_trans (φ ψ χ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp ψ).allPast.imp ((ψ.imp χ).allPast.imp (φ.imp χ).allPast)) :=
  unwrap (@Cslib.Logic.Theorems.Temporal.TemporalDerived.H_imp_trans'
    _ _ _ _ _ Bimodal.HilbertTM _ _ (φ := φ) (ψ := ψ) (χ := χ))

end DistributionVariants

section TemporalContraposition

noncomputable def G_contrapose (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp ψ).allFuture.imp (ψ.neg.imp φ.neg).allFuture) :=
  unwrap (@Cslib.Logic.Theorems.Temporal.TemporalDerived.G_contrapose
    _ _ _ _ _ Bimodal.HilbertTM _ _ (φ := φ) (ψ := ψ))

noncomputable def H_contrapose (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp ψ).allPast.imp (ψ.neg.imp φ.neg).allPast) :=
  unwrap (@Cslib.Logic.Theorems.Temporal.TemporalDerived.H_contrapose
    _ _ _ _ _ Bimodal.HilbertTM _ _ (φ := φ) (ψ := ψ))

end TemporalContraposition

section FuturePastChains

noncomputable def connect_future_G (φ : Formula Atom) :
    DerivationTree FrameClass.Base []
      (φ.allFuture.imp (φ.somePast.allFuture).allFuture) :=
  unwrap (@Cslib.Logic.Theorems.Temporal.TemporalDerived.connect_future_G
    _ _ _ _ _ Bimodal.HilbertTM _ _ (φ := φ))

noncomputable def connect_past_H (φ : Formula Atom) :
    DerivationTree FrameClass.Base []
      (φ.allPast.imp (φ.someFuture.allPast).allPast) :=
  unwrap (@Cslib.Logic.Theorems.Temporal.TemporalDerived.connect_past_H
    _ _ _ _ _ Bimodal.HilbertTM _ _ (φ := φ))

noncomputable def connect_future_chain (φ : Formula Atom) :
    DerivationTree FrameClass.Base []
      (φ.imp ((φ.somePast.someFuture.allPast).allFuture)) :=
  let step1 := DerivationTree.temporal_necessitation _ (connect_past_thm φ.somePast)
  let step2 := mp step1 (G_distribution φ.somePast (φ.somePast.someFuture.allPast))
  imp_trans (connect_future_thm φ) step2

noncomputable def connect_past_chain (φ : Formula Atom) :
    DerivationTree FrameClass.Base []
      (φ.imp ((φ.someFuture.somePast.allFuture).allPast)) :=
  let step1 := past_necessitation _ (connect_future_thm φ.someFuture)
  let step2 := mp step1 (H_distribution φ.someFuture (φ.someFuture.somePast.allFuture))
  imp_trans (connect_past_thm φ) step2

end FuturePastChains

section ConjunctionElimination

noncomputable def always_to_present (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] (φ.always.imp φ) :=
  imp_trans (rce_imp φ.allPast (φ.and φ.allFuture)) (lce_imp φ φ.allFuture)

noncomputable def present_to_sometimes (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] (φ.imp φ.sometimes) := by
  exact imp_trans (dni φ) (contraposition (always_to_present φ.neg))

noncomputable def weakFutureLeft (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] ((φ.and φ.allFuture).imp φ) :=
  lce_imp φ φ.allFuture

noncomputable def weakFutureRight (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] ((φ.and φ.allFuture).imp φ.allFuture) :=
  rce_imp φ φ.allFuture

noncomputable def weakPastLeft (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] ((φ.and φ.allPast).imp φ) :=
  lce_imp φ φ.allPast

noncomputable def weakPastRight (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] ((φ.and φ.allPast).imp φ.allPast) :=
  rce_imp φ φ.allPast

noncomputable def always_imp_allFuture (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] (φ.always.imp φ.allFuture) :=
  imp_trans (rce_imp φ.allPast (φ.and φ.allFuture)) (rce_imp φ φ.allFuture)

noncomputable def always_imp_allPast (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] (φ.always.imp φ.allPast) :=
  lce_imp φ.allPast (φ.and φ.allFuture)

end ConjunctionElimination

end -- noncomputable section

end Cslib.Logic.Bimodal.Theorems.TemporalDerived
