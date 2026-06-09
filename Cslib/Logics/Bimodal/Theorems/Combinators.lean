/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/

import Cslib.Logics.Bimodal.ProofSystem.Derivation
import Cslib.Logics.Bimodal.Syntax.Formula

/-!
# Combinators - Propositional Reasoning Combinators

This module defines fundamental propositional reasoning combinators derived from
the K and S axioms. These combinators provide the foundation for both propositional
theorems and perpetuity principles.

## Main Combinators

### Propositional Reasoning
- `imp_trans`: Transitivity of implication (hypothetical syllogism)
- `mp`: Modus ponens wrapper
- `identity`: Identity combinator (SKK construction)
- `b_combinator`: B combinator (function composition)
- `theorem_flip`: C combinator (argument flip)

### Application Combinators
- `theorem_app1`: Single application lemma
- `theorem_app2`: Double application lemma (Vireo combinator)

### Conjunction Introduction
- `pairing`: Pairing combinator (derived from app2)
- `combine_imp_conj`: Combine two implications into conjunction
- `combine_imp_conj_3`: Combine three implications into nested conjunction

### Double Negation
- `dni`: Double negation introduction (derived from app1)

## References

Ported from BimodalLogic/Theories/Bimodal/Theorems/Combinators.lean
-/

set_option linter.style.emptyLine false

namespace Cslib.Logic.Bimodal.Theorems.Combinators

open Cslib.Logic.Bimodal

variable {Atom : Type*}

/--
Transitivity of implication: if `⊢ A → B` and `⊢ B → C` then `⊢ A → C`.
-/
def imp_trans {fc : FrameClass} {A B C : Formula Atom}
    (h1 : DerivationTree fc [] (A.imp B))
    (h2 : DerivationTree fc [] (B.imp C)) : DerivationTree fc [] (A.imp C) := by
  have s_axiom := DerivationTree.axiom (fc := fc) [] _ (Axiom.imp_s (B.imp C) A) (FrameClass.base_le fc)
  have h3 := DerivationTree.modus_ponens [] (B.imp C) (A.imp (B.imp C)) s_axiom h2
  have k_axiom := DerivationTree.axiom (fc := fc) [] _ (Axiom.imp_k A B C) (FrameClass.base_le fc)
  have h4 := DerivationTree.modus_ponens [] (A.imp (B.imp C)) ((A.imp B).imp (A.imp C)) k_axiom h3
  exact DerivationTree.modus_ponens [] (A.imp B) (A.imp C) h4 h1

/--
From `⊢ A` and `⊢ A → B`, derive `⊢ B` (modus ponens restated).
-/
def mp {fc : FrameClass} {A B : Formula Atom}
    (h1 : DerivationTree fc [] A) (h2 : DerivationTree fc [] (A.imp B)) : DerivationTree fc [] B := by
  exact DerivationTree.modus_ponens [] A B h2 h1

/--
Identity combinator: `⊢ A → A` (SKK construction).
-/
def identity {fc : FrameClass} (A : Formula Atom) : DerivationTree fc [] (A.imp A) := by
  have k1 : DerivationTree fc [] (A.imp ((A.imp A).imp A)) := DerivationTree.axiom [] _ (Axiom.imp_s A (A.imp A)) (FrameClass.base_le fc)
  have k2 : DerivationTree fc [] (A.imp (A.imp A)) := DerivationTree.axiom [] _ (Axiom.imp_s A A) (FrameClass.base_le fc)
  have s : DerivationTree fc [] ((A.imp ((A.imp A).imp A)).imp ((A.imp (A.imp A)).imp (A.imp A))) :=
    DerivationTree.axiom [] _ (Axiom.imp_k A (A.imp A) A) (FrameClass.base_le fc)
  have h1 : DerivationTree fc [] ((A.imp (A.imp A)).imp (A.imp A)) := DerivationTree.modus_ponens [] _ _ s k1
  exact DerivationTree.modus_ponens [] _ _ h1 k2

/--
B combinator (composition): `⊢ (B → C) → (A → B) → (A → C)`.
-/
def b_combinator {fc : FrameClass} {A B C : Formula Atom} : DerivationTree fc [] ((B.imp C).imp ((A.imp B).imp (A.imp C))) := by
  have s_axiom : DerivationTree fc [] ((B.imp C).imp (A.imp (B.imp C))) :=
    DerivationTree.axiom [] _ (Axiom.imp_s (B.imp C) A) (FrameClass.base_le fc)
  have k_axiom : DerivationTree fc [] ((A.imp (B.imp C)).imp ((A.imp B).imp (A.imp C))) :=
    DerivationTree.axiom [] _ (Axiom.imp_k A B C) (FrameClass.base_le fc)
  exact imp_trans s_axiom k_axiom

/--
Flip combinator (C): `⊢ (A → B → C) → (B → A → C)`.
-/
def theorem_flip {fc : FrameClass} {A B C : Formula Atom} : DerivationTree fc [] ((A.imp (B.imp C)).imp (B.imp (A.imp C))) := by
  have step1 : DerivationTree fc [] ((A.imp (B.imp C)).imp (B.imp (A.imp (B.imp C)))) :=
    DerivationTree.axiom [] _ (Axiom.imp_s (A.imp (B.imp C)) B) (FrameClass.base_le fc)
  have k_abc : DerivationTree fc [] ((A.imp (B.imp C)).imp ((A.imp B).imp (A.imp C))) :=
    DerivationTree.axiom [] _ (Axiom.imp_k A B C) (FrameClass.base_le fc)
  have weak_k : DerivationTree fc [] (((A.imp (B.imp C)).imp ((A.imp B).imp (A.imp C))).imp
                   (B.imp ((A.imp (B.imp C)).imp ((A.imp B).imp (A.imp C))))) :=
    DerivationTree.axiom [] _ (Axiom.imp_s ((A.imp (B.imp C)).imp ((A.imp B).imp (A.imp C))) B) (FrameClass.base_le fc)
  have step2 : DerivationTree fc [] (B.imp ((A.imp (B.imp C)).imp ((A.imp B).imp (A.imp C)))) :=
    DerivationTree.modus_ponens [] _ _ weak_k k_abc
  have k_step : DerivationTree fc [] ((B.imp ((A.imp (B.imp C)).imp ((A.imp B).imp (A.imp C)))).imp
                   ((B.imp (A.imp (B.imp C))).imp (B.imp ((A.imp B).imp (A.imp C))))) :=
    DerivationTree.axiom [] _ (Axiom.imp_k B (A.imp (B.imp C)) ((A.imp B).imp (A.imp C))) (FrameClass.base_le fc)
  have step3 : DerivationTree fc [] ((B.imp (A.imp (B.imp C))).imp (B.imp ((A.imp B).imp (A.imp C)))) :=
    DerivationTree.modus_ponens [] _ _ k_step step2
  have step4 : DerivationTree fc [] ((A.imp (B.imp C)).imp (B.imp ((A.imp B).imp (A.imp C)))) :=
    imp_trans step1 step3
  have s_ab : DerivationTree fc [] (B.imp (A.imp B)) := DerivationTree.axiom [] _ (Axiom.imp_s B A) (FrameClass.base_le fc)
  have k_final :
    DerivationTree fc [] ((B.imp ((A.imp B).imp (A.imp C))).imp
      ((B.imp (A.imp B)).imp (B.imp (A.imp C)))) :=
    DerivationTree.axiom [] _ (Axiom.imp_k B (A.imp B) (A.imp C)) (FrameClass.base_le fc)
  have weak_s_ab : DerivationTree fc [] ((B.imp (A.imp B)).imp ((A.imp (B.imp C)).imp (B.imp (A.imp B)))) :=
    DerivationTree.axiom [] _ (Axiom.imp_s (B.imp (A.imp B)) (A.imp (B.imp C))) (FrameClass.base_le fc)
  have step6 : DerivationTree fc [] ((A.imp (B.imp C)).imp (B.imp (A.imp B))) :=
    DerivationTree.modus_ponens [] _ _ weak_s_ab s_ab
  have k_combine :
    DerivationTree fc [] (((A.imp (B.imp C)).imp ((B.imp (A.imp B)).imp (B.imp (A.imp C)))).imp
      (((A.imp (B.imp C)).imp (B.imp (A.imp B))).imp
       ((A.imp (B.imp C)).imp (B.imp (A.imp C))))) :=
    DerivationTree.axiom [] _
      (Axiom.imp_k (A.imp (B.imp C)) (B.imp (A.imp B)) (B.imp (A.imp C))) (FrameClass.base_le fc)
  have step5 : DerivationTree fc [] ((A.imp (B.imp C)).imp ((B.imp (A.imp B)).imp (B.imp (A.imp C)))) :=
    imp_trans step4 k_final
  have step7 :
    DerivationTree fc [] (((A.imp (B.imp C)).imp (B.imp (A.imp B))).imp
      ((A.imp (B.imp C)).imp (B.imp (A.imp C)))) :=
    DerivationTree.modus_ponens [] _ _ k_combine step5
  exact DerivationTree.modus_ponens [] _ _ step7 step6

/--
Single application lemma (app1): `⊢ A → (A → B) → B`.
-/
def theorem_app1 {fc : FrameClass} {A B : Formula Atom} : DerivationTree fc [] (A.imp ((A.imp B).imp B)) := by
  have id_ab : DerivationTree fc [] ((A.imp B).imp (A.imp B)) := identity (A.imp B)
  have flip_inst : DerivationTree fc [] (((A.imp B).imp (A.imp B)).imp (A.imp ((A.imp B).imp B))) :=
    @theorem_flip Atom fc (A.imp B) A B
  exact DerivationTree.modus_ponens [] _ _ flip_inst id_ab

/--
Double application lemma (app2): `⊢ A → B → (A → B → C) → C`.
-/
def theorem_app2 {fc : FrameClass} {A B C : Formula Atom} : DerivationTree fc [] (A.imp (B.imp ((A.imp (B.imp C)).imp C))) := by
  have step_a : DerivationTree fc [] (A.imp ((A.imp (B.imp C)).imp (B.imp C))) := theorem_app1
  have step_b : DerivationTree fc [] (B.imp ((B.imp C).imp C)) := theorem_app1
  have weak_step_b : DerivationTree fc [] ((B.imp ((B.imp C).imp C)).imp (A.imp (B.imp ((B.imp C).imp C)))) :=
    DerivationTree.axiom [] _ (Axiom.imp_s (B.imp ((B.imp C).imp C)) A) (FrameClass.base_le fc)
  have a_b_bc_c : DerivationTree fc [] (A.imp (B.imp ((B.imp C).imp C))) :=
    DerivationTree.modus_ponens [] _ _ weak_step_b step_b
  have weak_step_a : DerivationTree fc [] ((A.imp ((A.imp (B.imp C)).imp (B.imp C))).imp
                        (B.imp (A.imp ((A.imp (B.imp C)).imp (B.imp C))))) :=
    DerivationTree.axiom [] _ (Axiom.imp_s (A.imp ((A.imp (B.imp C)).imp (B.imp C))) B) (FrameClass.base_le fc)
  have b_a_abc_bc : DerivationTree fc [] (B.imp (A.imp ((A.imp (B.imp C)).imp (B.imp C)))) :=
    DerivationTree.modus_ponens [] _ _ weak_step_a step_a
  have a_b_abc_bc : DerivationTree fc [] (A.imp (B.imp ((A.imp (B.imp C)).imp (B.imp C)))) :=
    DerivationTree.modus_ponens [] _ _ theorem_flip b_a_abc_bc
  have b_comp :
    DerivationTree fc [] (((B.imp C).imp C).imp
      (((A.imp (B.imp C)).imp (B.imp C)).imp ((A.imp (B.imp C)).imp C))) :=
    b_combinator
  have weak_b_comp :
    DerivationTree fc [] ((((B.imp C).imp C).imp
       (((A.imp (B.imp C)).imp (B.imp C)).imp ((A.imp (B.imp C)).imp C))).imp
      (B.imp (((B.imp C).imp C).imp
       (((A.imp (B.imp C)).imp (B.imp C)).imp ((A.imp (B.imp C)).imp C))))) :=
    DerivationTree.axiom [] _
      (Axiom.imp_s
        (((B.imp C).imp C).imp
         (((A.imp (B.imp C)).imp (B.imp C)).imp ((A.imp (B.imp C)).imp C)))
        B) (FrameClass.base_le fc)
  have b_b_comp :
    DerivationTree fc [] (B.imp (((B.imp C).imp C).imp
      (((A.imp (B.imp C)).imp (B.imp C)).imp ((A.imp (B.imp C)).imp C)))) :=
    DerivationTree.modus_ponens [] _ _ weak_b_comp b_comp
  have weak_a_b_comp :
    DerivationTree fc [] ((B.imp (((B.imp C).imp C).imp
       (((A.imp (B.imp C)).imp (B.imp C)).imp ((A.imp (B.imp C)).imp C)))).imp
      (A.imp (B.imp (((B.imp C).imp C).imp
       (((A.imp (B.imp C)).imp (B.imp C)).imp ((A.imp (B.imp C)).imp C)))))) :=
    DerivationTree.axiom [] _
      (Axiom.imp_s
        (B.imp (((B.imp C).imp C).imp
         (((A.imp (B.imp C)).imp (B.imp C)).imp ((A.imp (B.imp C)).imp C))))
        A) (FrameClass.base_le fc)
  have a_b_b_comp :
    DerivationTree fc [] (A.imp (B.imp (((B.imp C).imp C).imp
      (((A.imp (B.imp C)).imp (B.imp C)).imp ((A.imp (B.imp C)).imp C))))) :=
    DerivationTree.modus_ponens [] _ _ weak_a_b_comp b_b_comp
  have k_b :
    DerivationTree fc [] ((B.imp (((B.imp C).imp C).imp
       (((A.imp (B.imp C)).imp (B.imp C)).imp ((A.imp (B.imp C)).imp C)))).imp
      ((B.imp ((B.imp C).imp C)).imp
       (B.imp (((A.imp (B.imp C)).imp (B.imp C)).imp ((A.imp (B.imp C)).imp C))))) :=
    DerivationTree.axiom [] _
      (Axiom.imp_k B ((B.imp C).imp C)
        (((A.imp (B.imp C)).imp (B.imp C)).imp ((A.imp (B.imp C)).imp C))) (FrameClass.base_le fc)
  have step7_b :
    DerivationTree fc [] ((B.imp ((B.imp C).imp C)).imp
      (B.imp (((A.imp (B.imp C)).imp (B.imp C)).imp ((A.imp (B.imp C)).imp C)))) :=
    DerivationTree.modus_ponens [] _ _ k_b b_b_comp
  have k_a :
    DerivationTree fc [] ((A.imp ((B.imp ((B.imp C).imp C)).imp
       (B.imp (((A.imp (B.imp C)).imp (B.imp C)).imp ((A.imp (B.imp C)).imp C))))).imp
      ((A.imp (B.imp ((B.imp C).imp C))).imp
       (A.imp (B.imp (((A.imp (B.imp C)).imp (B.imp C)).imp
         ((A.imp (B.imp C)).imp C)))))) :=
    DerivationTree.axiom [] _
      (Axiom.imp_k A (B.imp ((B.imp C).imp C))
        (B.imp (((A.imp (B.imp C)).imp (B.imp C)).imp ((A.imp (B.imp C)).imp C)))) (FrameClass.base_le fc)
  have weak_step7 :
    DerivationTree fc [] (((B.imp ((B.imp C).imp C)).imp
       (B.imp (((A.imp (B.imp C)).imp (B.imp C)).imp ((A.imp (B.imp C)).imp C)))).imp
      (A.imp ((B.imp ((B.imp C).imp C)).imp
       (B.imp (((A.imp (B.imp C)).imp (B.imp C)).imp ((A.imp (B.imp C)).imp C)))))) :=
    DerivationTree.axiom [] _
      (Axiom.imp_s
        ((B.imp ((B.imp C).imp C)).imp
         (B.imp (((A.imp (B.imp C)).imp (B.imp C)).imp ((A.imp (B.imp C)).imp C))))
        A) (FrameClass.base_le fc)
  have a_step7 :
    DerivationTree fc [] (A.imp ((B.imp ((B.imp C).imp C)).imp
      (B.imp (((A.imp (B.imp C)).imp (B.imp C)).imp ((A.imp (B.imp C)).imp C))))) :=
    DerivationTree.modus_ponens [] _ _ weak_step7 step7_b
  have step8 :
    DerivationTree fc [] ((A.imp (B.imp ((B.imp C).imp C))).imp
      (A.imp (B.imp (((A.imp (B.imp C)).imp (B.imp C)).imp
        ((A.imp (B.imp C)).imp C))))) :=
    DerivationTree.modus_ponens [] _ _ k_a a_step7
  have step9 :
    DerivationTree fc [] (A.imp (B.imp (((A.imp (B.imp C)).imp (B.imp C)).imp
      ((A.imp (B.imp C)).imp C)))) :=
    DerivationTree.modus_ponens [] _ _ step8 a_b_bc_c
  have k_b_final :
    DerivationTree fc [] ((B.imp (((A.imp (B.imp C)).imp (B.imp C)).imp ((A.imp (B.imp C)).imp C))).imp
      ((B.imp ((A.imp (B.imp C)).imp (B.imp C))).imp
       (B.imp ((A.imp (B.imp C)).imp C)))) :=
    DerivationTree.axiom [] _
      (Axiom.imp_k B ((A.imp (B.imp C)).imp (B.imp C)) ((A.imp (B.imp C)).imp C)) (FrameClass.base_le fc)
  have weak_k_b :
    DerivationTree fc [] (((B.imp (((A.imp (B.imp C)).imp (B.imp C)).imp ((A.imp (B.imp C)).imp C))).imp
       ((B.imp ((A.imp (B.imp C)).imp (B.imp C))).imp
        (B.imp ((A.imp (B.imp C)).imp C)))).imp
      (A.imp ((B.imp (((A.imp (B.imp C)).imp (B.imp C)).imp
         ((A.imp (B.imp C)).imp C))).imp
        ((B.imp ((A.imp (B.imp C)).imp (B.imp C))).imp
         (B.imp ((A.imp (B.imp C)).imp C)))))) :=
    DerivationTree.axiom [] _
      (Axiom.imp_s
        ((B.imp (((A.imp (B.imp C)).imp (B.imp C)).imp ((A.imp (B.imp C)).imp C))).imp
         ((B.imp ((A.imp (B.imp C)).imp (B.imp C))).imp (B.imp ((A.imp (B.imp C)).imp C))))
        A) (FrameClass.base_le fc)
  have a_k_b :
    DerivationTree fc [] (A.imp ((B.imp (((A.imp (B.imp C)).imp (B.imp C)).imp
       ((A.imp (B.imp C)).imp C))).imp
      ((B.imp ((A.imp (B.imp C)).imp (B.imp C))).imp
       (B.imp ((A.imp (B.imp C)).imp C))))) :=
    DerivationTree.modus_ponens [] _ _ weak_k_b k_b_final
  have k_a_outer :
    DerivationTree fc [] ((A.imp ((B.imp (((A.imp (B.imp C)).imp (B.imp C)).imp
         ((A.imp (B.imp C)).imp C))).imp
       ((B.imp ((A.imp (B.imp C)).imp (B.imp C))).imp
        (B.imp ((A.imp (B.imp C)).imp C))))).imp
      ((A.imp (B.imp (((A.imp (B.imp C)).imp (B.imp C)).imp
         ((A.imp (B.imp C)).imp C)))).imp
       (A.imp ((B.imp ((A.imp (B.imp C)).imp (B.imp C))).imp
        (B.imp ((A.imp (B.imp C)).imp C)))))) :=
    DerivationTree.axiom [] _
      (Axiom.imp_k A
        (B.imp (((A.imp (B.imp C)).imp (B.imp C)).imp ((A.imp (B.imp C)).imp C)))
        ((B.imp ((A.imp (B.imp C)).imp (B.imp C))).imp
         (B.imp ((A.imp (B.imp C)).imp C)))) (FrameClass.base_le fc)
  have step10_a :
    DerivationTree fc [] ((A.imp (B.imp (((A.imp (B.imp C)).imp (B.imp C)).imp
       ((A.imp (B.imp C)).imp C)))).imp
      (A.imp ((B.imp ((A.imp (B.imp C)).imp (B.imp C))).imp
       (B.imp ((A.imp (B.imp C)).imp C))))) :=
    DerivationTree.modus_ponens [] _ _ k_a_outer a_k_b
  have step10 :
    DerivationTree fc [] (A.imp ((B.imp ((A.imp (B.imp C)).imp (B.imp C))).imp
      (B.imp ((A.imp (B.imp C)).imp C)))) :=
    DerivationTree.modus_ponens [] _ _ step10_a step9
  have k_a_final :
    DerivationTree fc [] ((A.imp ((B.imp ((A.imp (B.imp C)).imp (B.imp C))).imp
       (B.imp ((A.imp (B.imp C)).imp C)))).imp
      ((A.imp (B.imp ((A.imp (B.imp C)).imp (B.imp C)))).imp
       (A.imp (B.imp ((A.imp (B.imp C)).imp C))))) :=
    DerivationTree.axiom [] _
      (Axiom.imp_k A (B.imp ((A.imp (B.imp C)).imp (B.imp C)))
        (B.imp ((A.imp (B.imp C)).imp C))) (FrameClass.base_le fc)
  have step11 :
    DerivationTree fc [] ((A.imp (B.imp ((A.imp (B.imp C)).imp (B.imp C)))).imp
      (A.imp (B.imp ((A.imp (B.imp C)).imp C)))) :=
    DerivationTree.modus_ponens [] _ _ k_a_final step10
  exact DerivationTree.modus_ponens [] _ _ step11 a_b_abc_bc

/--
Pairing combinator: `⊢ A → B → A ∧ B`.
-/
def pairing {fc : FrameClass} (A B : Formula Atom) : DerivationTree fc [] (A.imp (B.imp (A.and B))) :=
  @theorem_app2 Atom fc A B Formula.bot

/--
Double negation introduction: `⊢ A → ¬¬A`.
-/
def dni {fc : FrameClass} (A : Formula Atom) : DerivationTree fc [] (A.imp A.neg.neg) :=
  @theorem_app1 Atom fc A Formula.bot

/--
Combine two implications into a conjunction implication.

Given `⊢ P → A` and `⊢ P → B`, derive `⊢ P → A ∧ B`.
-/
def combine_imp_conj {fc : FrameClass} {R A B : Formula Atom}
    (hA : DerivationTree fc [] (R.imp A))
    (hB : DerivationTree fc [] (R.imp B)) : DerivationTree fc [] (R.imp (A.and B)) := by
  have pair_ab : DerivationTree fc [] (A.imp (B.imp (A.and B))) :=
    (pairing A B).lift (FrameClass.base_le fc)
  have h1 := imp_trans hA pair_ab
  have s := DerivationTree.axiom (fc := fc) [] _ (Axiom.imp_k R B (A.and B)) (FrameClass.base_le fc)
  have h2 := DerivationTree.modus_ponens [] (R.imp (B.imp (A.and B))) ((R.imp B).imp (R.imp (A.and B))) s h1
  exact DerivationTree.modus_ponens [] (R.imp B) (R.imp (A.and B)) h2 hB

/--
Combine three implications into a nested conjunction implication.

Given `⊢ P → A`, `⊢ P → B`, and `⊢ P → C`, derive `⊢ P → A ∧ (B ∧ C)`.
-/
def combine_imp_conj_3 {fc : FrameClass} {R A B C : Formula Atom}
    (hA : DerivationTree fc [] (R.imp A))
    (hB : DerivationTree fc [] (R.imp B))
    (hC : DerivationTree fc [] (R.imp C)) : DerivationTree fc [] (R.imp (A.and (B.and C))) := by
  have hBC := combine_imp_conj hB hC
  exact combine_imp_conj hA hBC

/--
Derived TF theorem: `□φ → G(□φ)`.
-/
def temp_future_derived {fc : FrameClass} (φ : Formula Atom) :
    DerivationTree fc [] ((Formula.box φ).imp (Formula.all_future (Formula.box φ))) :=
  let mf_box := DerivationTree.axiom [] _ (Axiom.modal_future (Formula.box φ)) (FrameClass.base_le fc)
  let t_G_box := DerivationTree.axiom [] _ (Axiom.modal_t (Formula.all_future (Formula.box φ))) (FrameClass.base_le fc)
  let chain1 := imp_trans mf_box t_G_box
  let m4 := DerivationTree.axiom [] _ (Axiom.modal_4 φ) (FrameClass.base_le fc)
  imp_trans m4 chain1

end Cslib.Logic.Bimodal.Theorems.Combinators
