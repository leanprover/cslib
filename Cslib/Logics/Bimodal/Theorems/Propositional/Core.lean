/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.ProofSystem.Derivation
public import Cslib.Logics.Bimodal.ProofSystem.Instances
public import Cslib.Logics.Bimodal.Syntax.Formula
public import Cslib.Logics.Bimodal.Theorems.Combinators
public import Cslib.Logics.Bimodal.Metalogic.Core.DeductionTheorem
public import Cslib.Foundations.Logic.Theorems.Propositional.Core

/-!
# Core Propositional Proof Combinators

Core propositional reasoning combinators for the Hilbert-style proof system.
Contains LEM, efq, ecq, raa, disjunction intro, conjunction elim, and rcp.

Most theorems delegate to the generic Foundations equivalents via the wrap/unwrap
bridge pattern.

Ported from BimodalLogic/Theories/Bimodal/Theorems/Propositional/Core.lean
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false

@[expose] public section

namespace Cslib.Logic.Bimodal.Theorems.Propositional

open Cslib.Logic
open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Theorems.Combinators
open Cslib.Logic.Bimodal.Theorems.Perpetuity (unwrap)

variable {Atom : Type*}

noncomputable section

def lem (A : Formula Atom) : DerivationTree FrameClass.Base [] (A.or A.neg) :=
  unwrap (@_root_.Cslib.Logic.Theorems.Propositional.Core.lem
    _ _ _ Bimodal.HilbertTM _ _ (φ := A))

def efqAxiom {fc : FrameClass} (φ : Formula Atom) :
    DerivationTree fc [] (Formula.bot.imp φ) :=
  DerivationTree.lift (FrameClass.base_le fc)
    (unwrap (@_root_.Cslib.Logic.Theorems.Propositional.Core.efq_axiom
      _ _ _ Bimodal.HilbertTM _ _ (φ := φ)))

def peirceAxiom {fc : FrameClass} (φ ψ : Formula Atom) :
    DerivationTree fc [] (((φ.imp ψ).imp φ).imp φ) :=
  DerivationTree.lift (FrameClass.base_le fc)
    (unwrap (@_root_.Cslib.Logic.Theorems.Propositional.Core.peirce_axiom
      _ _ _ Bimodal.HilbertTM _ _ (φ := φ) (ψ := ψ)))

def doubleNegation {fc : FrameClass} (φ : Formula Atom) :
    DerivationTree fc [] (φ.neg.neg.imp φ) :=
  DerivationTree.lift (FrameClass.base_le fc)
    (unwrap (@_root_.Cslib.Logic.Theorems.Propositional.Core.double_negation
      _ _ _ Bimodal.HilbertTM _ _ (φ := φ)))

def raa (A B : Formula Atom) :
    DerivationTree FrameClass.Base [] (A.imp (A.neg.imp B)) :=
  unwrap (@_root_.Cslib.Logic.Theorems.Propositional.Core.raa
    _ _ _ Bimodal.HilbertTM _ _ (φ := A) (ψ := B))

def efqNeg (A B : Formula Atom) :
    DerivationTree FrameClass.Base [] (A.neg.imp (A.imp B)) :=
  unwrap (@_root_.Cslib.Logic.Theorems.Propositional.Core.efq_neg
    _ _ _ Bimodal.HilbertTM _ _ (φ := A) (ψ := B))

def lceImp {fc : FrameClass} (A B : Formula Atom) :
    DerivationTree fc [] ((A.and B).imp A) :=
  DerivationTree.lift (FrameClass.base_le fc)
    (unwrap (@_root_.Cslib.Logic.Theorems.Propositional.Core.lce_imp
      _ _ _ Bimodal.HilbertTM _ _ (φ := A) (ψ := B)))

def rceImp {fc : FrameClass} (A B : Formula Atom) :
    DerivationTree fc [] ((A.and B).imp B) :=
  DerivationTree.lift (FrameClass.base_le fc)
    (unwrap (@_root_.Cslib.Logic.Theorems.Propositional.Core.rce_imp
      _ _ _ Bimodal.HilbertTM _ _ (φ := A) (ψ := B)))

-- ecq, ldi, rdi, lce, rce use context-based proofs and are kept as-is

def ecq (A B : Formula Atom) :
    DerivationTree FrameClass.Base [A, A.neg] B := by
  have h_neg_a : DerivationTree FrameClass.Base [A, A.neg] A.neg := by
    apply DerivationTree.assumption; simp
  have h_a : DerivationTree FrameClass.Base [A, A.neg] A := by
    apply DerivationTree.assumption; simp
  have h_bot : DerivationTree FrameClass.Base [A, A.neg] Formula.bot :=
    DerivationTree.modus_ponens [A, A.neg] A Formula.bot h_neg_a h_a
  have bot_to_neg_neg_b : DerivationTree FrameClass.Base [] (Formula.bot.imp B.neg.neg) :=
    DerivationTree.axiom [] _ (Axiom.imp_s Formula.bot B.neg) trivial
  have bot_to_neg_neg_b_ctx :
      DerivationTree FrameClass.Base [A, A.neg] (Formula.bot.imp B.neg.neg) :=
    DerivationTree.weakening [] [A, A.neg] _ bot_to_neg_neg_b (by intro; simp)
  have neg_neg_b : DerivationTree FrameClass.Base [A, A.neg] B.neg.neg :=
    DerivationTree.modus_ponens [A, A.neg] Formula.bot B.neg.neg bot_to_neg_neg_b_ctx h_bot
  have dne_b : DerivationTree FrameClass.Base [] (B.neg.neg.imp B) :=
    doubleNegation B
  have dne_b_ctx : DerivationTree FrameClass.Base [A, A.neg] (B.neg.neg.imp B) :=
    DerivationTree.weakening [] [A, A.neg] _ dne_b (by intro; simp)
  exact DerivationTree.modus_ponens [A, A.neg] B.neg.neg B dne_b_ctx neg_neg_b

def ldi (A B : Formula Atom) :
    DerivationTree FrameClass.Base [A] (A.or B) := by
  have efq_inst : DerivationTree FrameClass.Base [] (A.neg.imp (A.imp B)) :=
    efqNeg A B
  have h_a : DerivationTree FrameClass.Base [A] A := by
    apply DerivationTree.assumption; simp
  have efq_ctx : DerivationTree FrameClass.Base [A] (A.neg.imp (A.imp B)) :=
    DerivationTree.weakening [] [A] _ efq_inst (by intro; simp)
  have k_inst : DerivationTree FrameClass.Base []
      ((A.neg.imp (A.imp B)).imp ((A.neg.imp A).imp (A.neg.imp B))) :=
    DerivationTree.axiom [] _ (Axiom.imp_k A.neg A B) trivial
  have k_ctx : DerivationTree FrameClass.Base [A]
      ((A.neg.imp (A.imp B)).imp ((A.neg.imp A).imp (A.neg.imp B))) :=
    DerivationTree.weakening [] [A] _ k_inst (by intro; simp)
  have step1 : DerivationTree FrameClass.Base [A] ((A.neg.imp A).imp (A.neg.imp B)) :=
    DerivationTree.modus_ponens [A] _ _ k_ctx efq_ctx
  have s_inst : DerivationTree FrameClass.Base [] (A.imp (A.neg.imp A)) :=
    DerivationTree.axiom [] _ (Axiom.imp_s A A.neg) trivial
  have s_ctx : DerivationTree FrameClass.Base [A] (A.imp (A.neg.imp A)) :=
    DerivationTree.weakening [] [A] _ s_inst (by intro; simp)
  have step2 : DerivationTree FrameClass.Base [A] (A.neg.imp A) :=
    DerivationTree.modus_ponens [A] A _ s_ctx h_a
  exact DerivationTree.modus_ponens [A] _ _ step1 step2

def rdi (A B : Formula Atom) :
    DerivationTree FrameClass.Base [B] (A.or B) := by
  have s_inst : DerivationTree FrameClass.Base [] (B.imp (A.neg.imp B)) :=
    DerivationTree.axiom [] _ (Axiom.imp_s B A.neg) trivial
  have h_b : DerivationTree FrameClass.Base [B] B := by
    apply DerivationTree.assumption; simp
  have s_ctx : DerivationTree FrameClass.Base [B] (B.imp (A.neg.imp B)) :=
    DerivationTree.weakening [] [B] _ s_inst (by intro; simp)
  exact DerivationTree.modus_ponens [B] B _ s_ctx h_b

def rcp {fc : FrameClass} (Γ : Context Atom) (A B : Formula Atom)
    (h : DerivationTree fc Γ (A.neg.imp B.neg)) :
    DerivationTree fc Γ (B.imp A) := by
  have dni_b : DerivationTree FrameClass.Base [] (B.imp B.neg.neg) :=
    dni B
  have dni_b_ctx : DerivationTree fc Γ (B.imp B.neg.neg) :=
    DerivationTree.weakening [] Γ _ (dni_b.lift (FrameClass.base_le fc)) (by intro; simp)
  have contra_thm : DerivationTree FrameClass.Base []
      ((A.neg.imp B.neg).imp (B.neg.neg.imp A.neg.neg)) := by
    have bc : DerivationTree FrameClass.Base []
        (((B.imp Formula.bot).imp Formula.bot).imp
         (((A.imp Formula.bot).imp (B.imp Formula.bot)).imp
          ((A.imp Formula.bot).imp Formula.bot))) :=
      @bCombinator Atom FrameClass.Base (A.imp Formula.bot) (B.imp Formula.bot) Formula.bot
    have flip' : DerivationTree FrameClass.Base []
        ((((B.imp Formula.bot).imp Formula.bot).imp
         (((A.imp Formula.bot).imp (B.imp Formula.bot)).imp
          ((A.imp Formula.bot).imp Formula.bot))).imp
        (((A.imp Formula.bot).imp (B.imp Formula.bot)).imp
         (((B.imp Formula.bot).imp Formula.bot).imp
          ((A.imp Formula.bot).imp Formula.bot)))) :=
      @flip Atom FrameClass.Base ((B.imp Formula.bot).imp Formula.bot)
                    ((A.imp Formula.bot).imp (B.imp Formula.bot))
                    ((A.imp Formula.bot).imp Formula.bot)
    exact DerivationTree.modus_ponens [] _ _ flip' bc
  have contra_thm_ctx : DerivationTree fc Γ
      ((A.neg.imp B.neg).imp (B.neg.neg.imp A.neg.neg)) :=
    DerivationTree.weakening [] Γ _ (contra_thm.lift (FrameClass.base_le fc)) (by intro; simp)
  have contraposed : DerivationTree fc Γ (B.neg.neg.imp A.neg.neg) :=
    DerivationTree.modus_ponens Γ _ _ contra_thm_ctx h
  have b_comp1 : DerivationTree FrameClass.Base []
      ((B.neg.neg.imp A.neg.neg).imp ((B.imp B.neg.neg).imp (B.imp A.neg.neg))) :=
    @bCombinator Atom FrameClass.Base B B.neg.neg A.neg.neg
  have b_comp1_ctx : DerivationTree fc Γ
      ((B.neg.neg.imp A.neg.neg).imp ((B.imp B.neg.neg).imp (B.imp A.neg.neg))) :=
    DerivationTree.weakening [] Γ _ (b_comp1.lift (FrameClass.base_le fc)) (by intro; simp)
  have step1 : DerivationTree fc Γ ((B.imp B.neg.neg).imp (B.imp A.neg.neg)) :=
    DerivationTree.modus_ponens Γ _ _ b_comp1_ctx contraposed
  have b_to_neg_neg_a : DerivationTree fc Γ (B.imp A.neg.neg) :=
    DerivationTree.modus_ponens Γ _ _ step1 dni_b_ctx
  have dne_a : DerivationTree FrameClass.Base [] (A.neg.neg.imp A) :=
    doubleNegation A
  have dne_a_ctx : DerivationTree fc Γ (A.neg.neg.imp A) :=
    DerivationTree.weakening [] Γ _ (dne_a.lift (FrameClass.base_le fc)) (by intro; simp)
  have b_final : DerivationTree FrameClass.Base []
      ((A.neg.neg.imp A).imp ((B.imp A.neg.neg).imp (B.imp A))) :=
    @bCombinator Atom FrameClass.Base B A.neg.neg A
  have b_final_ctx : DerivationTree fc Γ
      ((A.neg.neg.imp A).imp ((B.imp A.neg.neg).imp (B.imp A))) :=
    DerivationTree.weakening [] Γ _ (b_final.lift (FrameClass.base_le fc)) (by intro; simp)
  have step2 : DerivationTree fc Γ ((B.imp A.neg.neg).imp (B.imp A)) :=
    DerivationTree.modus_ponens Γ _ _ b_final_ctx dne_a_ctx
  exact DerivationTree.modus_ponens Γ _ _ step2 b_to_neg_neg_a

def lce (A B : Formula Atom) :
    DerivationTree FrameClass.Base [A.and B] A := by
  have h_conj : DerivationTree FrameClass.Base [A.and B] (A.and B) := by
    apply DerivationTree.assumption; simp
  have h_conj_unf : DerivationTree FrameClass.Base [A.and B] (A.imp B.neg).neg := h_conj
  have efq_helper : DerivationTree FrameClass.Base [] (A.neg.imp (A.imp B.neg)) :=
    efqNeg A B.neg
  have efq_ctx : DerivationTree FrameClass.Base [A.and B] (A.neg.imp (A.imp B.neg)) :=
    DerivationTree.weakening [] [A.and B] _ efq_helper (by intro; simp)
  have contra_step : DerivationTree FrameClass.Base []
      ((A.neg.imp (A.imp B.neg)).imp ((A.imp B.neg).neg.imp A.neg.neg)) := by
    have bc : DerivationTree FrameClass.Base []
        (((A.imp (B.imp Formula.bot)).imp Formula.bot).imp
         (((A.imp Formula.bot).imp (A.imp (B.imp Formula.bot))).imp
          ((A.imp Formula.bot).imp Formula.bot))) :=
      @bCombinator Atom FrameClass.Base (A.imp Formula.bot) (A.imp (B.imp Formula.bot)) Formula.bot
    have flip' : DerivationTree FrameClass.Base []
        ((((A.imp (B.imp Formula.bot)).imp Formula.bot).imp
         (((A.imp Formula.bot).imp (A.imp (B.imp Formula.bot))).imp
          ((A.imp Formula.bot).imp Formula.bot))).imp
        (((A.imp Formula.bot).imp (A.imp (B.imp Formula.bot))).imp
         (((A.imp (B.imp Formula.bot)).imp Formula.bot).imp
          ((A.imp Formula.bot).imp Formula.bot)))) :=
      @flip Atom FrameClass.Base ((A.imp (B.imp Formula.bot)).imp Formula.bot)
                    ((A.imp Formula.bot).imp (A.imp (B.imp Formula.bot)))
                    ((A.imp Formula.bot).imp Formula.bot)
    exact DerivationTree.modus_ponens [] _ _ flip' bc
  have contra_step_ctx : DerivationTree FrameClass.Base [A.and B]
      ((A.neg.imp (A.imp B.neg)).imp ((A.imp B.neg).neg.imp A.neg.neg)) :=
    DerivationTree.weakening [] [A.and B] _ contra_step (by intro; simp)
  have step1 : DerivationTree FrameClass.Base [A.and B]
      ((A.imp B.neg).neg.imp A.neg.neg) :=
    DerivationTree.modus_ponens [A.and B] _ _ contra_step_ctx efq_ctx
  have neg_neg_a : DerivationTree FrameClass.Base [A.and B] A.neg.neg :=
    DerivationTree.modus_ponens [A.and B] _ _ step1 h_conj_unf
  have dne_a : DerivationTree FrameClass.Base [] (A.neg.neg.imp A) :=
    doubleNegation A
  have dne_a_ctx : DerivationTree FrameClass.Base [A.and B] (A.neg.neg.imp A) :=
    DerivationTree.weakening [] [A.and B] _ dne_a (by intro; simp)
  exact DerivationTree.modus_ponens [A.and B] _ _ dne_a_ctx neg_neg_a

def rce (A B : Formula Atom) :
    DerivationTree FrameClass.Base [A.and B] B := by
  have h_conj : DerivationTree FrameClass.Base [A.and B] (A.and B) := by
    apply DerivationTree.assumption; simp
  have h_conj_unf : DerivationTree FrameClass.Base [A.and B] (A.imp B.neg).neg := h_conj
  have s_helper : DerivationTree FrameClass.Base [] (B.neg.imp (A.imp B.neg)) :=
    DerivationTree.axiom [] _ (Axiom.imp_s B.neg A) trivial
  have s_ctx : DerivationTree FrameClass.Base [A.and B] (B.neg.imp (A.imp B.neg)) :=
    DerivationTree.weakening [] [A.and B] _ s_helper (by intro; simp)
  have contra_step : DerivationTree FrameClass.Base []
      ((B.neg.imp (A.imp B.neg)).imp ((A.imp B.neg).neg.imp B.neg.neg)) := by
    have bc : DerivationTree FrameClass.Base []
        (((A.imp (B.imp Formula.bot)).imp Formula.bot).imp
         (((B.imp Formula.bot).imp (A.imp (B.imp Formula.bot))).imp
          ((B.imp Formula.bot).imp Formula.bot))) :=
      @bCombinator Atom FrameClass.Base (B.imp Formula.bot) (A.imp (B.imp Formula.bot)) Formula.bot
    have flip' : DerivationTree FrameClass.Base []
        ((((A.imp (B.imp Formula.bot)).imp Formula.bot).imp
         (((B.imp Formula.bot).imp (A.imp (B.imp Formula.bot))).imp
          ((B.imp Formula.bot).imp Formula.bot))).imp
        (((B.imp Formula.bot).imp (A.imp (B.imp Formula.bot))).imp
         (((A.imp (B.imp Formula.bot)).imp Formula.bot).imp
          ((B.imp Formula.bot).imp Formula.bot)))) :=
      @flip Atom FrameClass.Base ((A.imp (B.imp Formula.bot)).imp Formula.bot)
                    ((B.imp Formula.bot).imp (A.imp (B.imp Formula.bot)))
                    ((B.imp Formula.bot).imp Formula.bot)
    exact DerivationTree.modus_ponens [] _ _ flip' bc
  have contra_step_ctx : DerivationTree FrameClass.Base [A.and B]
      ((B.neg.imp (A.imp B.neg)).imp ((A.imp B.neg).neg.imp B.neg.neg)) :=
    DerivationTree.weakening [] [A.and B] _ contra_step (by intro; simp)
  have step1 : DerivationTree FrameClass.Base [A.and B]
      ((A.imp B.neg).neg.imp B.neg.neg) :=
    DerivationTree.modus_ponens [A.and B] _ _ contra_step_ctx s_ctx
  have neg_neg_b : DerivationTree FrameClass.Base [A.and B] B.neg.neg :=
    DerivationTree.modus_ponens [A.and B] _ _ step1 h_conj_unf
  have dne_b : DerivationTree FrameClass.Base [] (B.neg.neg.imp B) :=
    doubleNegation B
  have dne_b_ctx : DerivationTree FrameClass.Base [A.and B] (B.neg.neg.imp B) :=
    DerivationTree.weakening [] [A.and B] _ dne_b (by intro; simp)
  exact DerivationTree.modus_ponens [A.and B] _ _ dne_b_ctx neg_neg_b

end -- noncomputable section

end Cslib.Logic.Bimodal.Theorems.Propositional
