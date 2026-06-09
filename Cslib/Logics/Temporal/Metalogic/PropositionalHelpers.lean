/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/

import Cslib.Logics.Temporal.Metalogic.MCS

/-!
# Propositional Helpers for Temporal Logic

Propositional combinator derivations needed by Chronicle files.

## References

* Ported from Cslib/Logics/Bimodal/Theorems/Propositional/Core.lean
* Ported from Cslib/Logics/Bimodal/Theorems/Combinators.lean
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Cslib.Logic.Temporal.Metalogic

open Cslib.Logic.Temporal

variable {Atom : Type*}

noncomputable section

/-- Double negation elimination: ⊢ ¬¬φ → φ. -/
def double_negation (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] (φ.neg.neg.imp φ) := by
  -- Use deduction theorem approach: assume ¬¬φ, derive φ.
  let ctx := [Formula.neg (Formula.neg φ)]
  have d_peirce : DerivationTree FrameClass.Base ctx (((φ.imp Formula.bot).imp φ).imp φ) :=
    .weakening [] ctx _ (.axiom [] _ (.peirce φ Formula.bot) trivial) (fun _ h => nomatch h)
  let ctx2 := [φ.imp Formula.bot, Formula.neg (Formula.neg φ)]
  have d_bot : DerivationTree FrameClass.Base ctx2 Formula.bot :=
    .modus_ponens ctx2 (φ.imp Formula.bot) Formula.bot
      (.assumption ctx2 (Formula.neg (Formula.neg φ)) (by simp [List.mem_cons, ctx2]))
      (.assumption ctx2 (φ.imp Formula.bot) (by simp [List.mem_cons, ctx2]))
  have d_efq : DerivationTree FrameClass.Base ctx2 φ :=
    .modus_ponens ctx2 Formula.bot φ
      (.weakening [] ctx2 _ (.axiom [] _ (.efq φ) trivial) (fun _ h => nomatch h))
      d_bot
  have d_imp := deduction_theorem [Formula.neg (Formula.neg φ)] (φ.imp Formula.bot) φ d_efq
  exact deduction_theorem [] (Formula.neg (Formula.neg φ)) φ
    (DerivationTree.modus_ponens ctx _ _ d_peirce d_imp)

/-- Ex falso quodlibet: ⊢ ⊥ → φ. -/
def efq_axiom (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] (Formula.bot.imp φ) :=
  .axiom [] _ (.efq φ) trivial

/-- Implication transitivity: from ⊢ A → B and ⊢ B → C derive ⊢ A → C. -/
def imp_trans {A B C : Formula Atom}
    (h1 : DerivationTree FrameClass.Base [] (A.imp B))
    (h2 : DerivationTree FrameClass.Base [] (B.imp C)) :
    DerivationTree FrameClass.Base [] (A.imp C) := by
  have s_axiom := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.imp_s (B.imp C) A) trivial
  have h3 := DerivationTree.modus_ponens [] (B.imp C) (A.imp (B.imp C)) s_axiom h2
  have k_axiom := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.imp_k A B C) trivial
  have h4 := DerivationTree.modus_ponens [] (A.imp (B.imp C)) ((A.imp B).imp (A.imp C)) k_axiom h3
  exact DerivationTree.modus_ponens [] (A.imp B) (A.imp C) h4 h1

/-- Pairing: ⊢ φ → ψ → (φ ∧ ψ).
    Since φ ∧ ψ = ¬(φ → ¬ψ) = (φ → ψ → ⊥) → ⊥,
    we need ⊢ φ → ψ → ((φ → ψ → ⊥) → ⊥). -/
def pairing (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base [] (φ.imp (ψ.imp (Formula.and φ ψ))) := by
  -- Formula.and φ ψ = ((φ.imp (ψ.imp ⊥)).imp ⊥)
  -- Need: ⊢ φ → ψ → (φ → ψ → ⊥) → ⊥
  -- In context [φ → ψ → ⊥, ψ, φ]:
  let ctx := [φ.imp (ψ.imp Formula.bot), ψ, φ]
  have d_phi : DerivationTree FrameClass.Base ctx φ :=
    .assumption ctx φ (by simp [List.mem_cons, ctx])
  have d_psi : DerivationTree FrameClass.Base ctx ψ :=
    .assumption ctx ψ (by simp [List.mem_cons, ctx])
  have d_imp : DerivationTree FrameClass.Base ctx (φ.imp (ψ.imp Formula.bot)) :=
    .assumption ctx _ (by simp [List.mem_cons, ctx])
  have d_psi_bot : DerivationTree FrameClass.Base ctx (ψ.imp Formula.bot) :=
    .modus_ponens ctx φ _ d_imp d_phi
  have d_bot : DerivationTree FrameClass.Base ctx Formula.bot :=
    .modus_ponens ctx ψ _ d_psi_bot d_psi
  have d1 := deduction_theorem [ψ, φ] (φ.imp (ψ.imp Formula.bot)) Formula.bot d_bot
  have d2 := deduction_theorem [φ] ψ (Formula.and φ ψ) d1
  exact deduction_theorem [] φ (ψ.imp (Formula.and φ ψ)) d2

/-- Left conjunction elimination: ⊢ (φ ∧ ψ) → φ. -/
def lce_imp (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base [] ((Formula.and φ ψ).imp φ) := by
  -- (φ ∧ ψ) = ¬(φ → ¬ψ) = (φ → ψ → ⊥) → ⊥
  -- Need: ⊢ ((φ → ψ → ⊥) → ⊥) → φ
  -- By Peirce + EFQ: assume (φ → ψ → ⊥) → ⊥. Assume (φ → ⊥).
  -- Then φ → ψ → ⊥ follows from weakening of (φ → ⊥).
  -- So ⊥. So ¬(φ → ⊥), i.e., ¬¬φ. By DNE, φ.
  let ctx := [(φ.imp (ψ.imp Formula.bot)).imp Formula.bot]
  let ctx2 := [φ.imp Formula.bot, (φ.imp (ψ.imp Formula.bot)).imp Formula.bot]
  -- Build ⊢ (φ → ⊥) → (φ → ψ → ⊥)
  have d_phi_bot_to_phi_psi_bot : DerivationTree FrameClass.Base [φ.imp Formula.bot]
      (φ.imp (ψ.imp Formula.bot)) := by
    let ctx3 := [φ, φ.imp Formula.bot]
    have d_phi : DerivationTree FrameClass.Base ctx3 φ :=
      .assumption ctx3 φ (by simp [List.mem_cons, ctx3])
    have d_imp : DerivationTree FrameClass.Base ctx3 (φ.imp Formula.bot) :=
      .assumption ctx3 _ (by simp [List.mem_cons, ctx3])
    have d_bot : DerivationTree FrameClass.Base ctx3 Formula.bot :=
      .modus_ponens ctx3 φ _ d_imp d_phi
    have d_efq : DerivationTree FrameClass.Base ctx3 (ψ.imp Formula.bot) :=
      .modus_ponens ctx3 Formula.bot _
        (.weakening [] ctx3 _ (.axiom [] _ (.imp_s Formula.bot ψ) trivial) (fun _ h => nomatch h))
        d_bot
    exact deduction_theorem [φ.imp Formula.bot] φ (ψ.imp Formula.bot) d_efq
  -- In ctx2: derive (φ → ψ → ⊥), apply assumption to get ⊥
  have d_step : DerivationTree FrameClass.Base ctx2 (φ.imp (ψ.imp Formula.bot)) :=
    .weakening [φ.imp Formula.bot] ctx2 _ d_phi_bot_to_phi_psi_bot
      (by intro x hx; simp [List.mem_cons, ctx2] at hx ⊢; left; exact hx)
  have d_hyp : DerivationTree FrameClass.Base ctx2 ((φ.imp (ψ.imp Formula.bot)).imp Formula.bot) :=
    .assumption ctx2 _ (by simp [List.mem_cons, ctx2])
  have d_bot : DerivationTree FrameClass.Base ctx2 Formula.bot :=
    .modus_ponens ctx2 _ _ d_hyp d_step
  -- DT: ctx ⊢ (φ → ⊥) → ⊥ = ¬¬φ
  have d_nn : DerivationTree FrameClass.Base ctx (Formula.neg (Formula.neg φ)) :=
    deduction_theorem ctx (φ.imp Formula.bot) Formula.bot d_bot
  -- Apply DNE
  have d_dne : DerivationTree FrameClass.Base ctx (φ.neg.neg.imp φ) :=
    .weakening [] ctx _ (double_negation φ) (fun _ h => nomatch h)
  have d_phi : DerivationTree FrameClass.Base ctx φ :=
    .modus_ponens ctx _ _ d_dne d_nn
  exact deduction_theorem [] ((φ.imp (ψ.imp Formula.bot)).imp Formula.bot) φ d_phi

/-- Right conjunction elimination: ⊢ (φ ∧ ψ) → ψ. -/
def rce_imp (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base [] ((Formula.and φ ψ).imp ψ) := by
  -- Similar to lce_imp but extract ψ
  let ctx := [(φ.imp (ψ.imp Formula.bot)).imp Formula.bot]
  let ctx2 := [ψ.imp Formula.bot, (φ.imp (ψ.imp Formula.bot)).imp Formula.bot]
  -- Build ⊢ (ψ → ⊥) → (φ → ψ → ⊥)
  -- This is just weakening: from ψ → ⊥, we get φ → (ψ → ⊥) by imp_s
  have d_weak : DerivationTree FrameClass.Base ctx2 (φ.imp (ψ.imp Formula.bot)) := by
    have d_s : DerivationTree FrameClass.Base ctx2 ((ψ.imp Formula.bot).imp (φ.imp (ψ.imp Formula.bot))) :=
      .weakening [] ctx2 _ (.axiom [] _ (.imp_s (ψ.imp Formula.bot) φ) trivial) (fun _ h => nomatch h)
    have d_psi_bot : DerivationTree FrameClass.Base ctx2 (ψ.imp Formula.bot) :=
      .assumption ctx2 _ (by simp [List.mem_cons, ctx2])
    exact .modus_ponens ctx2 _ _ d_s d_psi_bot
  have d_hyp : DerivationTree FrameClass.Base ctx2 ((φ.imp (ψ.imp Formula.bot)).imp Formula.bot) :=
    .assumption ctx2 _ (by simp [List.mem_cons, ctx2])
  have d_bot : DerivationTree FrameClass.Base ctx2 Formula.bot :=
    .modus_ponens ctx2 _ _ d_hyp d_weak
  have d_nn : DerivationTree FrameClass.Base ctx (Formula.neg (Formula.neg ψ)) :=
    deduction_theorem ctx (ψ.imp Formula.bot) Formula.bot d_bot
  have d_dne : DerivationTree FrameClass.Base ctx (ψ.neg.neg.imp ψ) :=
    .weakening [] ctx _ (double_negation ψ) (fun _ h => nomatch h)
  have d_psi : DerivationTree FrameClass.Base ctx ψ :=
    .modus_ponens ctx _ _ d_dne d_nn
  exact deduction_theorem [] ((φ.imp (ψ.imp Formula.bot)).imp Formula.bot) ψ d_psi

/-- Double negation introduction: ⊢ φ → ¬¬φ. -/
def dni (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] (φ.imp φ.neg.neg) := by
  let ctx := [φ.neg, φ]
  have d_phi : DerivationTree FrameClass.Base ctx φ :=
    .assumption ctx φ (by simp [List.mem_cons, ctx])
  have d_neg : DerivationTree FrameClass.Base ctx φ.neg :=
    .assumption ctx φ.neg (by simp [List.mem_cons, ctx])
  have d_bot : DerivationTree FrameClass.Base ctx Formula.bot :=
    .modus_ponens ctx φ _ d_neg d_phi
  have d1 := deduction_theorem [φ] φ.neg Formula.bot d_bot
  exact deduction_theorem [] φ φ.neg.neg d1

end -- noncomputable section

end Cslib.Logic.Temporal.Metalogic
