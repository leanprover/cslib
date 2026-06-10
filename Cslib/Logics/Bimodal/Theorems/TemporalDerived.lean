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

/-- `⊢ ¬(¬ψ → ¬φ) → ¬(φ → ψ)`: negation of contrapositive implies negation of implication. -/
noncomputable def negContrapositiveImpNeg (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base [] ((ψ.neg.imp φ.neg).neg.imp (φ.imp ψ).neg) :=
  mp (contraposeImp φ ψ) (contraposeImp (φ.imp ψ) (ψ.neg.imp φ.neg))

/-- `⊢ X → (⊤ ∧ X)`: introduce top conjunction. -/
def topAndIntro (X : Formula Atom) :
    DerivationTree FrameClass.Base [] (X.imp (Formula.top.and X)) :=
  mp (identity Formula.bot) (pairing Formula.top X)

noncomputable def F_neg_contra_imp_F_neg (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((Formula.someFuture (ψ.neg.imp φ.neg).neg).imp
       (Formula.someFuture (φ.imp ψ).neg)) :=
  mp (DerivationTree.temporal_necessitation _ (negContrapositiveImpNeg φ ψ))
     (DerivationTree.axiom [] _
       (Axiom.right_mono_until (ψ.neg.imp φ.neg).neg (φ.imp ψ).neg Formula.top) trivial)

noncomputable def G_imp_to_G_contra (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp ψ).allFuture.imp (ψ.neg.imp φ.neg).allFuture) :=
  contraposition (F_neg_contra_imp_F_neg φ ψ)

noncomputable def G_contra_to_GK (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((ψ.neg.imp φ.neg).allFuture.imp (φ.allFuture.imp ψ.allFuture)) :=
  impTrans
    (DerivationTree.axiom [] _ (Axiom.right_mono_until ψ.neg φ.neg Formula.top) trivial)
    (contraposeImp (Formula.someFuture ψ.neg) (Formula.someFuture φ.neg))

/-- Temporal K-distribution derived from BX axioms: `⊢ G(φ → ψ) → (Gφ → Gψ)`. -/
noncomputable def tempKDistDerived (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp ψ).allFuture.imp (φ.allFuture.imp ψ.allFuture)) :=
  impTrans (G_imp_to_G_contra φ ψ) (G_contra_to_GK φ ψ)

noncomputable def dneLiftF (φ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((Formula.someFuture (Formula.someFuture φ.neg).neg.neg).imp
       (Formula.someFuture (Formula.someFuture φ.neg))) :=
  mp (DerivationTree.temporal_necessitation _ (doubleNegation (Formula.someFuture φ.neg)))
     (DerivationTree.axiom [] _
       (Axiom.right_mono_until
         (Formula.someFuture φ.neg).neg.neg (Formula.someFuture φ.neg) Formula.top) trivial)

noncomputable def FF_to_F_top_and (φ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((Formula.someFuture (Formula.someFuture φ.neg)).imp
       (Formula.someFuture (Formula.top.and (Formula.someFuture φ.neg)))) :=
  mp (DerivationTree.temporal_necessitation _ (topAndIntro (Formula.someFuture φ.neg)))
     (DerivationTree.axiom [] _
       (Axiom.right_mono_until
         (Formula.someFuture φ.neg)
         (Formula.top.and (Formula.someFuture φ.neg)) Formula.top) trivial)

def F_top_and_absorb (φ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((Formula.someFuture (Formula.top.and (Formula.someFuture φ.neg))).imp
       (Formula.someFuture φ.neg)) :=
  DerivationTree.axiom [] _ (Axiom.absorb_until Formula.top φ.neg) trivial

/-- Temporal 4-axiom derived from BX axioms: `⊢ Gφ → GGφ`. -/
noncomputable def temp_4_derived (φ : Formula Atom) :
    DerivationTree FrameClass.Base []
      (φ.allFuture.imp φ.allFuture.allFuture) :=
  contraposition (impTrans (impTrans (dneLiftF φ) (FF_to_F_top_and φ)) (F_top_and_absorb φ))

end DerivedAxioms

/-- G-distribution: `⊢ G(φ → ψ) → (Gφ → Gψ)` (unwrapped from Foundations). -/
noncomputable def G_distribution (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp ψ).allFuture.imp (φ.allFuture.imp ψ.allFuture)) :=
  unwrap (@Cslib.Logic.Theorems.Temporal.TemporalDerived.G_distribution
    _ _ _ _ _ Bimodal.HilbertTM _ _ (φ := φ) (ψ := ψ))

/-- H-distribution: `⊢ H(φ → ψ) → (Hφ → Hψ)` (unwrapped from Foundations). -/
noncomputable def H_distribution (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp ψ).allPast.imp (φ.allPast.imp ψ.allPast)) :=
  unwrap (@Cslib.Logic.Theorems.Temporal.TemporalDerived.H_distribution
    _ _ _ _ _ Bimodal.HilbertTM _ _ (φ := φ) (ψ := ψ))

/-- G-transitivity (temporal 4-axiom): `⊢ Gφ → GGφ`. -/
noncomputable def G_transitivity (φ : Formula Atom) :
    DerivationTree FrameClass.Base []
      (φ.allFuture.imp φ.allFuture.allFuture) :=
  temp_4_derived φ

/-- H-transitivity (temporal 4-axiom for past): `⊢ Hφ → HHφ` (via temporal duality). -/
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

/-- Future connection axiom: `⊢ φ → G(Pφ)`. -/
def connectFutureThm (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] (φ.imp (φ.somePast.allFuture)) :=
  DerivationTree.axiom [] _ (Axiom.connect_future φ) trivial

/-- Past connection axiom: `⊢ φ → H(Fφ)`. -/
def connectPastThm (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] (φ.imp (φ.someFuture.allPast)) :=
  DerivationTree.axiom [] _ (Axiom.connect_past φ) trivial

def G_implies_G_id (a : Formula Atom) :
    DerivationTree FrameClass.Base []
      (a.allFuture.imp (a.imp a).allFuture) :=
  mp (DerivationTree.temporal_necessitation _ (identity a))
     (DerivationTree.axiom [] _ (Axiom.imp_s (a.imp a).allFuture a.allFuture) trivial)

def untilImpliesSomeFuture (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((Formula.untl ψ φ).imp (Formula.someFuture ψ)) :=
  DerivationTree.axiom [] _ (Axiom.until_F φ ψ) trivial

def sinceImpliesSomePast (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((Formula.snce ψ φ).imp (Formula.somePast ψ)) :=
  DerivationTree.axiom [] _ (Axiom.since_P φ ψ) trivial

def untilImpF (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((Formula.untl ψ φ).imp (Formula.someFuture ψ)) :=
  DerivationTree.axiom [] _ (Axiom.until_F φ ψ) trivial

def sinceImpP (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((Formula.snce ψ φ).imp (Formula.somePast ψ)) :=
  DerivationTree.axiom [] _ (Axiom.since_P φ ψ) trivial

noncomputable def contrapositiveThm (A B : Formula Atom) :
    DerivationTree FrameClass.Base [] ((A.imp B).imp (B.neg.imp A.neg)) :=
  mp bCombinator (flip (A := (B.imp Formula.bot)) (B := (A.imp B)) (C := (A.imp Formula.bot)))

noncomputable def ctxMp {Γ : Context Atom} {A B : Formula Atom}
    (h1 : DerivationTree FrameClass.Base Γ (A.imp B))
    (h2 : DerivationTree FrameClass.Base Γ A) :
    DerivationTree FrameClass.Base Γ B :=
  DerivationTree.modus_ponens Γ A B h1 h2

noncomputable def ctxThm {Γ : Context Atom} {A : Formula Atom}
    (h : DerivationTree FrameClass.Base [] A) :
    DerivationTree FrameClass.Base Γ A :=
  DerivationTree.weakening [] Γ A h (List.nil_subset Γ)

noncomputable def formulaOrComm (A B : Formula Atom) :
    DerivationTree FrameClass.Base [] ((A.or B).imp (B.or A)) := by
  apply Cslib.Logic.Bimodal.Metalogic.Core.deductionTheorem [] (A.neg.imp B) (B.neg.imp A)
  apply Cslib.Logic.Bimodal.Metalogic.Core.deductionTheorem [A.neg.imp B] B.neg A
  have h1 : DerivationTree FrameClass.Base [B.neg, A.neg.imp B] (A.neg.imp B) :=
    DerivationTree.assumption _ _ (by simp)
  have h2 : DerivationTree FrameClass.Base [B.neg, A.neg.imp B] B.neg :=
    DerivationTree.assumption _ _ (by simp)
  have h3 := ctxMp (ctxMp (ctxThm bCombinator) h2) h1
  exact ctxMp (ctxThm (doubleNegation A)) h3

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

def untilMonoGuard (φ χ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp χ).allFuture.imp ((Formula.untl ψ φ).imp (Formula.untl ψ χ))) :=
  DerivationTree.axiom [] _ (Axiom.left_mono_until_G φ χ ψ) trivial

def sinceMonoGuard (φ χ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp χ).allPast.imp ((Formula.snce ψ φ).imp (Formula.snce ψ χ))) :=
  DerivationTree.axiom [] _ (Axiom.left_mono_since_H φ χ ψ) trivial

def untilMonoEvent (φ ψ χ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp ψ).allFuture.imp ((Formula.untl φ χ).imp (Formula.untl ψ χ))) :=
  DerivationTree.axiom [] _ (Axiom.right_mono_until φ ψ χ) trivial

def sinceMonoEvent (φ ψ χ : Formula Atom) :
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
  unwrap (@Cslib.Logic.Theorems.Temporal.TemporalDerived.G_imp_trans
    _ _ _ _ _ Bimodal.HilbertTM _ _ (φ := φ) (ψ := ψ) (χ := χ))

noncomputable def H_imp_trans (φ ψ χ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp ψ).allPast.imp ((ψ.imp χ).allPast.imp (φ.imp χ).allPast)) :=
  unwrap (@Cslib.Logic.Theorems.Temporal.TemporalDerived.H_imp_trans
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

noncomputable def connectFutureG (φ : Formula Atom) :
    DerivationTree FrameClass.Base []
      (φ.allFuture.imp (φ.somePast.allFuture).allFuture) :=
  unwrap (@Cslib.Logic.Theorems.Temporal.TemporalDerived.connect_future_G
    _ _ _ _ _ Bimodal.HilbertTM _ _ (φ := φ))

noncomputable def connectPastH (φ : Formula Atom) :
    DerivationTree FrameClass.Base []
      (φ.allPast.imp (φ.someFuture.allPast).allPast) :=
  unwrap (@Cslib.Logic.Theorems.Temporal.TemporalDerived.connect_past_H
    _ _ _ _ _ Bimodal.HilbertTM _ _ (φ := φ))

noncomputable def connectFutureChain (φ : Formula Atom) :
    DerivationTree FrameClass.Base []
      (φ.imp ((φ.somePast.someFuture.allPast).allFuture)) :=
  let step1 := DerivationTree.temporal_necessitation _ (connectPastThm φ.somePast)
  let step2 := mp step1 (G_distribution φ.somePast (φ.somePast.someFuture.allPast))
  impTrans (connectFutureThm φ) step2

noncomputable def connectPastChain (φ : Formula Atom) :
    DerivationTree FrameClass.Base []
      (φ.imp ((φ.someFuture.somePast.allFuture).allPast)) :=
  let step1 := pastNecessitation _ (connectFutureThm φ.someFuture)
  let step2 := mp step1 (H_distribution φ.someFuture (φ.someFuture.somePast.allFuture))
  impTrans (connectPastThm φ) step2

end FuturePastChains

section ConjunctionElimination

/-- Always implies present: `⊢ Aφ → φ` where `A = H ∧ (id ∧ G)`. -/
noncomputable def alwaysToPresent (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] (φ.always.imp φ) :=
  impTrans (rceImp φ.allPast (φ.and φ.allFuture)) (lceImp φ φ.allFuture)

/-- Present implies sometimes: `⊢ φ → Sφ` where `S = ¬A¬`. -/
noncomputable def presentToSometimes (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] (φ.imp φ.sometimes) := by
  exact impTrans (dni φ) (contraposition (alwaysToPresent φ.neg))

noncomputable def weakFutureLeft (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] ((φ.and φ.allFuture).imp φ) :=
  lceImp φ φ.allFuture

noncomputable def weakFutureRight (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] ((φ.and φ.allFuture).imp φ.allFuture) :=
  rceImp φ φ.allFuture

noncomputable def weakPastLeft (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] ((φ.and φ.allPast).imp φ) :=
  lceImp φ φ.allPast

noncomputable def weakPastRight (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] ((φ.and φ.allPast).imp φ.allPast) :=
  rceImp φ φ.allPast

noncomputable def alwaysImpAllFuture (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] (φ.always.imp φ.allFuture) :=
  impTrans (rceImp φ.allPast (φ.and φ.allFuture)) (rceImp φ φ.allFuture)

noncomputable def alwaysImpAllPast (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] (φ.always.imp φ.allPast) :=
  lceImp φ.allPast (φ.and φ.allFuture)

end ConjunctionElimination

end -- noncomputable section

end Cslib.Logic.Bimodal.Theorems.TemporalDerived
