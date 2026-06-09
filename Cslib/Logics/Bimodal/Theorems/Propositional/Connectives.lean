/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/

import Cslib.Logics.Bimodal.Theorems.Propositional.Core

/-!
# Derived Connective Reasoning

Classical merge, iff introduction/elimination, contraposition, and De Morgan laws
for the Hilbert-style proof system.

Ported from BimodalLogic/Theories/Bimodal/Theorems/Propositional/Connectives.lean
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Cslib.Logic.Bimodal.Theorems.Propositional

open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Theorems.Combinators

variable {Atom : Type*}

noncomputable section

def classical_merge (Q R : Formula Atom) :
    DerivationTree FrameClass.Base [] ((Q.imp R).imp ((Q.neg.imp R).imp R)) := by
  have contradiction_intro : ∀ A B : Formula Atom,
      DerivationTree FrameClass.Base [] ((A.imp B).imp ((A.imp B.neg).imp A.neg)) := by
    intro A B
    have h_in_ctx :
        DerivationTree FrameClass.Base [A, (A.imp B.neg), (A.imp B)] Formula.bot := by
      have h_a : DerivationTree FrameClass.Base [A, (A.imp B.neg), (A.imp B)] A := by
        apply DerivationTree.assumption; simp
      have h_ab : DerivationTree FrameClass.Base [A, (A.imp B.neg), (A.imp B)] (A.imp B) := by
        apply DerivationTree.assumption; simp
      have h_a_neg_b :
          DerivationTree FrameClass.Base [A, (A.imp B.neg), (A.imp B)] (A.imp B.neg) := by
        apply DerivationTree.assumption; simp
      have h_b := DerivationTree.modus_ponens _ A B h_ab h_a
      have h_neg_b := DerivationTree.modus_ponens _ A B.neg h_a_neg_b h_a
      exact DerivationTree.modus_ponens _ B Formula.bot h_neg_b h_b
    have step1 : DerivationTree FrameClass.Base [(A.imp B.neg), (A.imp B)] A.neg :=
      Cslib.Logic.Bimodal.Metalogic.Core.deduction_theorem
        [(A.imp B.neg), (A.imp B)] A Formula.bot h_in_ctx
    have step2 : DerivationTree FrameClass.Base [(A.imp B)] ((A.imp B.neg).imp A.neg) :=
      Cslib.Logic.Bimodal.Metalogic.Core.deduction_theorem
        [(A.imp B)] (A.imp B.neg) A.neg step1
    exact Cslib.Logic.Bimodal.Metalogic.Core.deduction_theorem
      [] (A.imp B) ((A.imp B.neg).imp A.neg) step2
  have ci_inst : DerivationTree FrameClass.Base []
      ((R.neg.imp Q.neg).imp ((R.neg.imp Q.neg.neg).imp R.neg.neg)) :=
    contradiction_intro R.neg Q.neg
  have contrapose_thm : ∀ A B : Formula Atom,
      DerivationTree FrameClass.Base [] ((A.imp B).imp (B.neg.imp A.neg)) := by
    intro A B
    have b : DerivationTree FrameClass.Base []
        ((B.imp Formula.bot).imp ((A.imp B).imp (A.imp Formula.bot))) :=
      b_combinator
    have flip_inst : DerivationTree FrameClass.Base []
        (((B.imp Formula.bot).imp ((A.imp B).imp (A.imp Formula.bot))).imp
         ((A.imp B).imp ((B.imp Formula.bot).imp (A.imp Formula.bot)))) :=
      @theorem_flip Atom FrameClass.Base (B.imp Formula.bot) (A.imp B) (A.imp Formula.bot)
    exact DerivationTree.modus_ponens [] _ _ flip_inst b
  have contra1 := contrapose_thm Q R
  have contra2 := contrapose_thm Q.neg R
  have dne_q : DerivationTree FrameClass.Base [] (R.neg.neg.imp R) := double_negation R
  have h_combined :
      DerivationTree FrameClass.Base [(Q.neg.imp R), (Q.imp R)] R := by
    have h_pq : DerivationTree FrameClass.Base [(Q.neg.imp R), (Q.imp R)] (Q.imp R) := by
      apply DerivationTree.assumption; simp
    have h_npq : DerivationTree FrameClass.Base [(Q.neg.imp R), (Q.imp R)] (Q.neg.imp R) := by
      apply DerivationTree.assumption; simp
    have contra1_ctx : DerivationTree FrameClass.Base [(Q.neg.imp R), (Q.imp R)] ((Q.imp R).imp (R.neg.imp Q.neg)) :=
      DerivationTree.weakening [] [(Q.neg.imp R), (Q.imp R)] _ contra1 (by intro; simp)
    have contra2_ctx : DerivationTree FrameClass.Base [(Q.neg.imp R), (Q.imp R)] ((Q.neg.imp R).imp (R.neg.imp Q.neg.neg)) :=
      DerivationTree.weakening [] [(Q.neg.imp R), (Q.imp R)] _ contra2 (by intro; simp)
    have ci_ctx : DerivationTree FrameClass.Base [(Q.neg.imp R), (Q.imp R)] ((R.neg.imp Q.neg).imp ((R.neg.imp Q.neg.neg).imp R.neg.neg)) :=
      DerivationTree.weakening [] [(Q.neg.imp R), (Q.imp R)] _ ci_inst (by intro; simp)
    have dne_ctx : DerivationTree FrameClass.Base [(Q.neg.imp R), (Q.imp R)] (R.neg.neg.imp R) :=
      DerivationTree.weakening [] [(Q.neg.imp R), (Q.imp R)] _ dne_q (by intro; simp)
    have h_nq_np := DerivationTree.modus_ponens _ _ _ contra1_ctx h_pq
    have h_nq_nnp := DerivationTree.modus_ponens _ _ _ contra2_ctx h_npq
    have step1 := DerivationTree.modus_ponens _ _ _ ci_ctx h_nq_np
    have step2 := DerivationTree.modus_ponens _ _ _ step1 h_nq_nnp
    exact DerivationTree.modus_ponens _ _ _ dne_ctx step2
  have step1 :=
    Cslib.Logic.Bimodal.Metalogic.Core.deduction_theorem [(Q.imp R)] (Q.neg.imp R) R h_combined
  exact Cslib.Logic.Bimodal.Metalogic.Core.deduction_theorem [] (Q.imp R) ((Q.neg.imp R).imp R) step1

def iff_intro (A B : Formula Atom)
    (h1 : DerivationTree FrameClass.Base [] (A.imp B))
    (h2 : DerivationTree FrameClass.Base [] (B.imp A)) :
    DerivationTree FrameClass.Base [] ((A.imp B).and (B.imp A)) := by
  have pair_inst : DerivationTree FrameClass.Base []
      ((A.imp B).imp ((B.imp A).imp ((A.imp B).and (B.imp A)))) :=
    pairing (fc := FrameClass.Base) (A.imp B) (B.imp A)
  have step1 := DerivationTree.modus_ponens [] _ _ pair_inst h1
  exact DerivationTree.modus_ponens [] _ _ step1 h2

def iff_elim_left (A B : Formula Atom) :
    DerivationTree FrameClass.Base [((A.imp B).and (B.imp A)), A] B := by
  have h_a : DerivationTree FrameClass.Base [((A.imp B).and (B.imp A)), A] A := by
    apply DerivationTree.assumption; simp
  have h_imp : DerivationTree FrameClass.Base [((A.imp B).and (B.imp A)), A] (A.imp B) := by
    have lce_inst := lce (A.imp B) (B.imp A)
    exact DerivationTree.weakening [(A.imp B).and (B.imp A)] _ _ lce_inst
      (by intro x; simp; intro h; left; exact h)
  exact DerivationTree.modus_ponens _ _ _ h_imp h_a

def iff_elim_right (A B : Formula Atom) :
    DerivationTree FrameClass.Base [((A.imp B).and (B.imp A)), B] A := by
  have h_b : DerivationTree FrameClass.Base [((A.imp B).and (B.imp A)), B] B := by
    apply DerivationTree.assumption; simp
  have h_imp : DerivationTree FrameClass.Base [((A.imp B).and (B.imp A)), B] (B.imp A) := by
    have rce_inst := rce (A.imp B) (B.imp A)
    exact DerivationTree.weakening [(A.imp B).and (B.imp A)] _ _ rce_inst
      (by intro x; simp; intro h; left; exact h)
  exact DerivationTree.modus_ponens _ _ _ h_imp h_b

def contrapose_imp (A B : Formula Atom) :
    DerivationTree FrameClass.Base [] ((A.imp B).imp (B.neg.imp A.neg)) := by
  have bc : DerivationTree FrameClass.Base []
      ((B.imp Formula.bot).imp ((A.imp B).imp (A.imp Formula.bot))) :=
    b_combinator
  have flip' : DerivationTree FrameClass.Base []
      (((B.imp Formula.bot).imp ((A.imp B).imp (A.imp Formula.bot))).imp
       ((A.imp B).imp ((B.imp Formula.bot).imp (A.imp Formula.bot)))) :=
    @theorem_flip Atom FrameClass.Base (B.imp Formula.bot) (A.imp B) (A.imp Formula.bot)
  exact DerivationTree.modus_ponens [] _ _ flip' bc

def contraposition {A B : Formula Atom}
    (h : DerivationTree FrameClass.Base [] (A.imp B)) :
    DerivationTree FrameClass.Base [] (B.neg.imp A.neg) := by
  have cp := contrapose_imp A B
  exact DerivationTree.modus_ponens [] _ _ cp h

def contrapose_iff (A B : Formula Atom)
    (h : DerivationTree FrameClass.Base [] ((A.imp B).and (B.imp A))) :
    DerivationTree FrameClass.Base [] ((A.neg.imp B.neg).and (B.neg.imp A.neg)) := by
  have ab : DerivationTree FrameClass.Base [] (A.imp B) := by
    have l := lce_imp (fc := FrameClass.Base) (A.imp B) (B.imp A)
    exact DerivationTree.modus_ponens [] _ _ l h
  have ba : DerivationTree FrameClass.Base [] (B.imp A) := by
    have r := rce_imp (fc := FrameClass.Base) (A.imp B) (B.imp A)
    exact DerivationTree.modus_ponens [] _ _ r h
  have nb_na := by
    have cp := contrapose_imp A B
    exact DerivationTree.modus_ponens [] _ _ cp ab
  have na_nb := by
    have cp := contrapose_imp B A
    exact DerivationTree.modus_ponens [] _ _ cp ba
  exact iff_intro A.neg B.neg na_nb nb_na

def iff_neg_intro (A B : Formula Atom)
    (h1 : DerivationTree FrameClass.Base [] (A.neg.imp B.neg))
    (h2 : DerivationTree FrameClass.Base [] (B.neg.imp A.neg)) :
    DerivationTree FrameClass.Base [] ((A.neg.imp B.neg).and (B.neg.imp A.neg)) :=
  iff_intro A.neg B.neg h1 h2

def demorgan_conj_neg_forward (A B : Formula Atom) :
    DerivationTree FrameClass.Base [] ((A.and B).neg.imp (A.neg.or B.neg)) := by
  simp only [Formula.and, Formula.or, Formula.neg]
  have dne_inner :=
    double_negation (fc := FrameClass.Base) (A.imp (B.imp Formula.bot))
  have dne_a := double_negation (fc := FrameClass.Base) A
  have b1 : DerivationTree FrameClass.Base []
      ((A.imp (B.imp Formula.bot)).imp
       ((((A.imp Formula.bot).imp Formula.bot).imp A).imp
        (((A.imp Formula.bot).imp Formula.bot).imp (B.imp Formula.bot)))) :=
    b_combinator
  have flip' : DerivationTree FrameClass.Base []
      (((A.imp (B.imp Formula.bot)).imp
        ((((A.imp Formula.bot).imp Formula.bot).imp A).imp
         (((A.imp Formula.bot).imp Formula.bot).imp (B.imp Formula.bot)))).imp
       ((((A.imp Formula.bot).imp Formula.bot).imp A).imp
        ((A.imp (B.imp Formula.bot)).imp
         (((A.imp Formula.bot).imp Formula.bot).imp (B.imp Formula.bot))))) :=
    @theorem_flip Atom FrameClass.Base (A.imp (B.imp Formula.bot))
                  (((A.imp Formula.bot).imp Formula.bot).imp A)
                  (((A.imp Formula.bot).imp Formula.bot).imp (B.imp Formula.bot))
  have step1 := DerivationTree.modus_ponens [] _ _ flip' b1
  have step2 := DerivationTree.modus_ponens [] _ _ step1 dne_a
  exact imp_trans dne_inner step2

def demorgan_conj_neg_backward (A B : Formula Atom) :
    DerivationTree FrameClass.Base [] ((A.neg.or B.neg).imp (A.and B).neg) := by
  simp only [Formula.and, Formula.or, Formula.neg]
  have h_in_ctx :
    DerivationTree FrameClass.Base
      [(A.and B), (((A.imp Formula.bot).imp Formula.bot).imp (B.imp Formula.bot))]
      Formula.bot := by
    have h_conj :
        DerivationTree FrameClass.Base
          [(A.and B), (((A.imp Formula.bot).imp Formula.bot).imp (B.imp Formula.bot))]
          (A.and B) := by
      apply DerivationTree.assumption; simp
    have h_hyp :
        DerivationTree FrameClass.Base
          [(A.and B), (((A.imp Formula.bot).imp Formula.bot).imp (B.imp Formula.bot))]
          (((A.imp Formula.bot).imp Formula.bot).imp (B.imp Formula.bot)) := by
      apply DerivationTree.assumption; simp
    have lce_inst := lce_imp (fc := FrameClass.Base) A B
    have lce_ctx := DerivationTree.weakening [] [(A.and B), (((A.imp Formula.bot).imp Formula.bot).imp (B.imp Formula.bot))] _ lce_inst (by intro; simp)
    have h_a := DerivationTree.modus_ponens _ _ _ lce_ctx h_conj
    have rce_inst := rce_imp (fc := FrameClass.Base) A B
    have rce_ctx := DerivationTree.weakening [] [(A.and B), (((A.imp Formula.bot).imp Formula.bot).imp (B.imp Formula.bot))] _ rce_inst (by intro; simp)
    have h_b := DerivationTree.modus_ponens _ _ _ rce_ctx h_conj
    have dni_inst : DerivationTree FrameClass.Base []
        (A.imp ((A.imp Formula.bot).imp Formula.bot)) :=
      @theorem_app1 Atom FrameClass.Base A Formula.bot
    have dni_ctx := DerivationTree.weakening [] [(A.and B), (((A.imp Formula.bot).imp Formula.bot).imp (B.imp Formula.bot))] _ dni_inst (by intro; simp)
    have h_nna := DerivationTree.modus_ponens _ _ _ dni_ctx h_a
    have h_nb := DerivationTree.modus_ponens _ _ _ h_hyp h_nna
    exact DerivationTree.modus_ponens _ _ _ h_nb h_b
  have step1 :=
    Cslib.Logic.Bimodal.Metalogic.Core.deduction_theorem
      [(((A.imp Formula.bot).imp Formula.bot).imp (B.imp Formula.bot))]
      (A.and B) Formula.bot h_in_ctx
  have step2 :=
    Cslib.Logic.Bimodal.Metalogic.Core.deduction_theorem []
      (((A.imp Formula.bot).imp Formula.bot).imp (B.imp Formula.bot))
      ((A.and B).imp Formula.bot) step1
  simp only [Formula.and, Formula.neg] at step2
  exact step2

def demorgan_conj_neg (A B : Formula Atom) :
    DerivationTree FrameClass.Base []
      (((A.and B).neg.imp (A.neg.or B.neg)).and ((A.neg.or B.neg).imp (A.and B).neg)) :=
  iff_intro (A.and B).neg (A.neg.or B.neg)
    (demorgan_conj_neg_forward A B) (demorgan_conj_neg_backward A B)

def demorgan_disj_neg_forward (A B : Formula Atom) :
    DerivationTree FrameClass.Base [] ((A.or B).neg.imp (A.neg.and B.neg)) := by
  simp only [Formula.or, Formula.and, Formula.neg]
  have dne_b := double_negation (fc := FrameClass.Base) B
  have bc : DerivationTree FrameClass.Base []
      ((((B.imp Formula.bot).imp Formula.bot).imp B).imp
       (((A.imp Formula.bot).imp ((B.imp Formula.bot).imp Formula.bot)).imp
        ((A.imp Formula.bot).imp B))) :=
    b_combinator
  have impl := DerivationTree.modus_ponens [] _ _ bc dne_b
  exact contraposition impl

def demorgan_disj_neg_backward (A B : Formula Atom) :
    DerivationTree FrameClass.Base [] ((A.neg.and B.neg).imp (A.or B).neg) := by
  simp only [Formula.or, Formula.and, Formula.neg]
  have dni_b : DerivationTree FrameClass.Base []
      (B.imp ((B.imp Formula.bot).imp Formula.bot)) :=
    @theorem_app1 Atom FrameClass.Base B Formula.bot
  have bc : DerivationTree FrameClass.Base []
      ((B.imp ((B.imp Formula.bot).imp Formula.bot)).imp
       (((A.imp Formula.bot).imp B).imp
        ((A.imp Formula.bot).imp ((B.imp Formula.bot).imp Formula.bot)))) :=
    b_combinator
  have impl := DerivationTree.modus_ponens [] _ _ bc dni_b
  exact contraposition impl

def demorgan_disj_neg (A B : Formula Atom) :
    DerivationTree FrameClass.Base []
      (((A.or B).neg.imp (A.neg.and B.neg)).and ((A.neg.and B.neg).imp (A.or B).neg)) :=
  iff_intro (A.or B).neg (A.neg.and B.neg)
    (demorgan_disj_neg_forward A B) (demorgan_disj_neg_backward A B)

end -- noncomputable section

end Cslib.Logic.Bimodal.Theorems.Propositional
