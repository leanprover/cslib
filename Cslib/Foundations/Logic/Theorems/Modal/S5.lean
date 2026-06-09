/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/
import Cslib.Foundations.Logic.ProofSystem
import Cslib.Foundations.Logic.Theorems.Combinators
import Cslib.Foundations.Logic.Theorems.Propositional.Core
import Cslib.Foundations.Logic.Theorems.Propositional.Connectives
import Cslib.Foundations.Logic.Theorems.Modal.Basic

/-! # S5-Level Modal Theorems

This module defines modal theorems that are derivable in any proof system
satisfying `[ModalS5Hilbert S]`, i.e., using the K distribution axiom,
necessitation rule, plus axioms T (□φ → φ), 4 (□φ → □□φ), and B (φ → □◇φ).

All theorems are generic over `[ModalS5Hilbert S]` with formula type `F`
carrying `HasBot`, `HasImp`, and `HasBox` instances.

## Main Results

### Axiom 5 Derivation
- `diamond_4`: `⊢ ◇◇φ → ◇φ`
- `axiom5_derived`: `⊢ ◇φ → □◇φ`
- `axiom5_collapse_derived`: `⊢ ◇□φ → □φ`

### Core S5 Theorems
- `t_box_to_diamond`: `⊢ □φ → ◇φ`
- `t_box_consistency`: `⊢ ¬□(φ ∧ ¬φ)`
- `box_disj_intro`: `⊢ (□φ ∨ □ψ) → □(φ ∨ ψ)`
- `box_conj_iff`: `⊢ □(φ ∧ ψ) ↔ (□φ ∧ □ψ)`
- `diamond_disj_iff`: `⊢ ◇(φ ∨ ψ) ↔ (◇φ ∨ ◇ψ)`

### S5 Collapse and Diamond-Box Theorems
- `s5_diamond_box`: `⊢ ◇□φ ↔ □φ`
- `s5_diamond_box_to_truth`: `⊢ ◇□φ → φ`

### S4-Level Nested Modality Theorems
- `s4_diamond_box_conj`: `⊢ (◇A ∧ □B) → ◇(A ∧ □B)`
- `s4_box_diamond_box`: `⊢ □A → □(◇□A)`
- `s4_diamond_box_diamond`: `⊢ ◇(□(◇A)) ↔ ◇A`
- `s5_diamond_conj_diamond`: `⊢ ◇(A ∧ ◇B) ↔ (◇A ∧ ◇B)`

## Encoding
- `¬φ = φ → ⊥`; `◇φ = (□(φ → ⊥)) → ⊥`
- `φ ∧ ψ = (φ → (ψ → ⊥)) → ⊥`; `φ ∨ ψ = (φ → ⊥) → ψ`
- `φ ↔ ψ = ((φ → ψ) → ((ψ → φ) → ⊥)) → ⊥`
-/

namespace Cslib.Logic.Theorems.Modal.S5

set_option linter.style.longLine false
set_option linter.unreachableTactic false

open Cslib.Logic
open Cslib.Logic.Theorems.Combinators
open Cslib.Logic.Theorems.Propositional.Core
open Cslib.Logic.Theorems.Propositional.Connectives
open Cslib.Logic.Theorems.Modal.Basic

variable {F : Type*} [HasBot F] [HasImp F] [HasBox F]
variable {S : Type*} [InferenceSystem S F]
variable [ModalS5Hilbert S (F := F)]

-- Abbreviations for readability in comments:
-- neg φ     = HasImp.imp φ HasBot.bot
-- box φ     = HasBox.box φ
-- diamond φ = HasImp.imp (HasBox.box (HasImp.imp φ HasBot.bot)) HasBot.bot
-- and φ ψ   = HasImp.imp (HasImp.imp φ (HasImp.imp ψ HasBot.bot)) HasBot.bot
-- or φ ψ    = HasImp.imp (HasImp.imp φ HasBot.bot) ψ
-- iff φ ψ   = and (imp φ ψ) (imp ψ φ)

noncomputable section

/-! ## Axiom 5 Derivation Block -/

/-- Diamond 4: `⊢ ◇◇φ → ◇φ` (S4 characteristic for diamond).

Derived from axiom 4 via contraposition and duality. -/
theorem diamond_4 {φ : F} :
    InferenceSystem.DerivableIn S
      (HasImp.imp
        (HasImp.imp
          (HasBox.box (HasImp.imp
            (HasImp.imp (HasBox.box (HasImp.imp φ HasBot.bot)) HasBot.bot)
            HasBot.bot))
          HasBot.bot)
        (HasImp.imp (HasBox.box (HasImp.imp φ HasBot.bot)) HasBot.bot)) := by
  -- M4 for ¬φ: □¬φ → □□¬φ
  have m4_neg := HasAxiom4.four (S := S) (φ := HasImp.imp φ HasBot.bot)
  -- Contrapose: ¬□□¬φ → ¬□¬φ
  have m4_contraposed := contraposition m4_neg
  -- DNI on □¬φ: □¬φ → ¬¬□¬φ
  have dni_box := dni (S := S) (HasBox.box (HasImp.imp φ HasBot.bot))
  -- DNE on □¬φ: ¬¬□¬φ → □¬φ
  have dne_box := @double_negation F _ _ S _ _
    (φ := HasBox.box (HasImp.imp φ HasBot.bot))
  -- Compose DNE + M4: ¬¬□¬φ → □□¬φ
  have combined := imp_trans dne_box m4_neg
  -- Necessitate and distribute: □¬¬□¬φ → □□□¬φ
  have box_combined := Necessitation.nec combined
  have mk_dist := HasAxiomK.K (S := S)
    (φ := HasImp.imp (HasImp.imp (HasBox.box (HasImp.imp φ HasBot.bot)) HasBot.bot) HasBot.bot)
    (ψ := HasBox.box (HasBox.box (HasImp.imp φ HasBot.bot)))
  have distributed := ModusPonens.mp mk_dist box_combined
  -- DNI on □¬φ necessitated and distributed: □□¬φ → □¬¬□¬φ
  have box_dni := Necessitation.nec dni_box
  have mk_dni := HasAxiomK.K (S := S)
    (φ := HasBox.box (HasImp.imp φ HasBot.bot))
    (ψ := HasImp.imp (HasImp.imp (HasBox.box (HasImp.imp φ HasBot.bot)) HasBot.bot) HasBot.bot)
  have bridge := ModusPonens.mp mk_dni box_dni
  -- Contrapose bridge: ¬□¬¬□¬φ → ¬□□¬φ
  have bridge_neg := contraposition bridge
  -- Compose: ◇◇φ = ¬□¬¬□¬φ → ¬□□¬φ → ¬□¬φ = ◇φ
  exact imp_trans bridge_neg m4_contraposed

/-- Axiom 5 derived: `⊢ ◇φ → □◇φ` (from B + diamond_4 + box_mono).

1. B on ◇φ: ◇φ → □◇◇φ
2. box_mono(diamond_4): □◇◇φ → □◇φ
3. Compose: ◇φ → □◇φ -/
theorem axiom5_derived {φ : F} :
    InferenceSystem.DerivableIn S
      (HasImp.imp
        (HasImp.imp (HasBox.box (HasImp.imp φ HasBot.bot)) HasBot.bot)
        (HasBox.box (HasImp.imp (HasBox.box (HasImp.imp φ HasBot.bot)) HasBot.bot))) := by
  have mb_dia := HasAxiomB.B (S := S)
    (φ := HasImp.imp (HasBox.box (HasImp.imp φ HasBot.bot)) HasBot.bot)
  have d4 := @diamond_4 F _ _ _ S _ _ (φ := φ)
  have box_d4 := box_mono d4
  exact imp_trans mb_dia box_d4

/-- Axiom 5 collapse: `⊢ ◇□φ → □φ` (from axiom5 + duality + DNE).

Chain: ¬□φ →[duality_rev] ◇¬φ →[axiom5] □◇¬φ →[box_mono(duality)] □¬□φ
Contrapose: ◇□φ = ¬□¬□φ → ¬¬□φ
DNE: ¬¬□φ → □φ -/
theorem axiom5_collapse_derived {φ : F} :
    InferenceSystem.DerivableIn S
      (HasImp.imp
        (HasImp.imp
          (HasBox.box (HasImp.imp (HasBox.box φ) HasBot.bot))
          HasBot.bot)
        (HasBox.box φ)) := by
  -- modal_duality_neg_rev: ¬□φ → ◇¬φ
  have duality_rev := @modal_duality_neg_rev F _ _ _ S _ _ (φ := φ)
  -- axiom5 on ¬φ: ◇¬φ → □◇¬φ
  have ax5_negphi := @axiom5_derived F _ _ _ S _ _
    (φ := HasImp.imp φ HasBot.bot)
  -- modal_duality_neg: ◇¬φ → ¬□φ
  have duality_fwd := @modal_duality_neg F _ _ _ S _ _ (φ := φ)
  -- box_mono on duality_fwd: □◇¬φ → □¬□φ
  have box_duality_fwd := box_mono duality_fwd
  -- Chain: ¬□φ → ◇¬φ → □◇¬φ → □¬□φ
  have chain1 := imp_trans duality_rev ax5_negphi
  have chain2 := imp_trans chain1 box_duality_fwd
  -- chain2: (□φ→⊥) → □(□φ→⊥)
  -- Contrapose: ◇□φ → ¬¬□φ
  have contra_chain := contraposition chain2
  -- DNE on □φ
  have dne_boxphi := @double_negation F _ _ S _ _ (φ := HasBox.box φ)
  -- Compose: ◇□φ → ¬¬□φ → □φ
  exact imp_trans contra_chain dne_boxphi

/-! ## Core S5 Theorems -/

/-- T-Box-Diamond: `⊢ □φ → ◇φ` (necessary implies possible). -/
theorem t_box_to_diamond {φ : F} :
    InferenceSystem.DerivableIn S
      (HasImp.imp (HasBox.box φ)
        (HasImp.imp (HasBox.box (HasImp.imp φ HasBot.bot)) HasBot.bot)) := by
  -- T: □φ → φ
  have mt_a := HasAxiomT.T (S := S) (φ := φ)
  -- T on ¬φ: □¬φ → ¬φ
  have mt_neg_a := HasAxiomT.T (S := S) (φ := HasImp.imp φ HasBot.bot)
  -- RAA: φ → (¬φ → ⊥)
  have raa_inst := @raa F _ _ S _ _ (φ := φ) (ψ := HasBot.bot)
  -- Compose □φ → φ → (¬φ → ⊥)
  have comp1 := imp_trans mt_a raa_inst
  -- b_combinator: (¬φ→⊥) → (□¬φ→¬φ) → (□¬φ→⊥)
  have step1 : InferenceSystem.DerivableIn S
      (HasImp.imp
        (HasImp.imp (HasImp.imp φ HasBot.bot) HasBot.bot)
        (HasImp.imp
          (HasImp.imp (HasBox.box (HasImp.imp φ HasBot.bot)) (HasImp.imp φ HasBot.bot))
          (HasImp.imp (HasBox.box (HasImp.imp φ HasBot.bot)) HasBot.bot))) :=
    b_combinator
  -- flip and apply T on ¬φ
  have b_flipped := ModusPonens.mp
    (@theorem_flip F _ _ S _ _
      (HasImp.imp (HasImp.imp φ HasBot.bot) HasBot.bot)
      (HasImp.imp (HasBox.box (HasImp.imp φ HasBot.bot)) (HasImp.imp φ HasBot.bot))
      (HasImp.imp (HasBox.box (HasImp.imp φ HasBot.bot)) HasBot.bot))
    step1
  have step2 := ModusPonens.mp b_flipped mt_neg_a
  -- step2: (¬φ→⊥) → (□¬φ→⊥)
  -- b_combinator to compose
  have b_outer : InferenceSystem.DerivableIn S
      (HasImp.imp
        (HasImp.imp (HasImp.imp (HasImp.imp φ HasBot.bot) HasBot.bot) (HasImp.imp (HasBox.box (HasImp.imp φ HasBot.bot)) HasBot.bot))
        (HasImp.imp
          (HasImp.imp (HasBox.box φ) (HasImp.imp (HasImp.imp φ HasBot.bot) HasBot.bot))
          (HasImp.imp (HasBox.box φ) (HasImp.imp (HasBox.box (HasImp.imp φ HasBot.bot)) HasBot.bot)))) :=
    b_combinator
  have step3 := ModusPonens.mp b_outer step2
  exact ModusPonens.mp step3 comp1

/-- T-Box-Consistency: `⊢ ¬□(φ ∧ ¬φ)`. -/
theorem t_box_consistency {φ : F} :
    InferenceSystem.DerivableIn S
      (HasImp.imp
        (HasBox.box
          (HasImp.imp
            (HasImp.imp φ
              (HasImp.imp (HasImp.imp φ HasBot.bot) HasBot.bot))
            HasBot.bot))
        HasBot.bot) := by
  have mt := HasAxiomT.T (S := S)
    (φ := HasImp.imp
      (HasImp.imp φ (HasImp.imp (HasImp.imp φ HasBot.bot) HasBot.bot))
      HasBot.bot)
  have dni_phi := dni (S := S) φ
  have dni_impl := dni (S := S)
    (HasImp.imp φ (HasImp.imp (HasImp.imp φ HasBot.bot) HasBot.bot))
  have conj_to_bot := ModusPonens.mp dni_impl dni_phi
  exact imp_trans mt conj_to_bot

/-- Box-Disjunction Introduction: `⊢ (□φ ∨ □ψ) → □(φ ∨ ψ)`. -/
theorem box_disj_intro {φ ψ : F} :
    InferenceSystem.DerivableIn S
      (HasImp.imp
        (HasImp.imp (HasImp.imp (HasBox.box φ) HasBot.bot) (HasBox.box ψ))
        (HasBox.box (HasImp.imp (HasImp.imp φ HasBot.bot) ψ))) := by
  have raa_inst := @raa F _ _ S _ _ (φ := φ) (ψ := ψ)
  have box_a_case := box_mono raa_inst
  have weak_b := HasAxiomImplyK.implyK (S := S)
    (φ := ψ) (ψ := HasImp.imp φ HasBot.bot)
  have box_b_case := box_mono weak_b
  have cm := @classical_merge F _ _ S _ _
    (φ := HasBox.box φ)
    (ψ := HasBox.box (HasImp.imp (HasImp.imp φ HasBot.bot) ψ))
  have step1 := ModusPonens.mp cm box_a_case
  have bc : InferenceSystem.DerivableIn S
      (HasImp.imp
        (HasImp.imp (HasBox.box ψ) (HasBox.box (HasImp.imp (HasImp.imp φ HasBot.bot) ψ)))
        (HasImp.imp
          (HasImp.imp (HasImp.imp (HasBox.box φ) HasBot.bot) (HasBox.box ψ))
          (HasImp.imp (HasImp.imp (HasBox.box φ) HasBot.bot) (HasBox.box (HasImp.imp (HasImp.imp φ HasBot.bot) ψ))))) :=
    b_combinator
  have neg_box_case := ModusPonens.mp bc box_b_case
  exact imp_trans neg_box_case step1

/-- Box-Conjunction Biconditional: `⊢ □(φ ∧ ψ) ↔ (□φ ∧ □ψ)`. -/
theorem box_conj_iff {φ ψ : F} :
    InferenceSystem.DerivableIn S
      (HasImp.imp
        (HasImp.imp
          (HasImp.imp
            (HasBox.box (HasImp.imp (HasImp.imp φ (HasImp.imp ψ HasBot.bot)) HasBot.bot))
            (HasImp.imp
              (HasImp.imp (HasBox.box φ) (HasImp.imp (HasBox.box ψ) HasBot.bot))
              HasBot.bot))
          (HasImp.imp
            (HasImp.imp
              (HasImp.imp
                (HasImp.imp (HasBox.box φ) (HasImp.imp (HasBox.box ψ) HasBot.bot))
                HasBot.bot)
              (HasBox.box (HasImp.imp (HasImp.imp φ (HasImp.imp ψ HasBot.bot)) HasBot.bot)))
            HasBot.bot))
        HasBot.bot) := by
  -- Forward: □(φ ∧ ψ) → (□φ ∧ □ψ)
  have lce_a := @lce_imp F _ _ S _ _ (φ := φ) (ψ := ψ)
  have box_a := box_mono lce_a
  have rce_b := @rce_imp F _ _ S _ _ (φ := φ) (ψ := ψ)
  have box_b := box_mono rce_b
  have forward := combine_imp_conj box_a box_b
  -- Backward: (□φ ∧ □ψ) → □(φ ∧ ψ)
  have pair := pairing (S := S) φ ψ
  have step1 := box_mono pair
  have modal_k := HasAxiomK.K (S := S) (φ := ψ)
    (ψ := HasImp.imp (HasImp.imp φ (HasImp.imp ψ HasBot.bot)) HasBot.bot)
  have comp1 := imp_trans step1 modal_k
  have lce_box := @lce_imp F _ _ S _ _ (φ := HasBox.box φ) (ψ := HasBox.box ψ)
  have rce_box := @rce_imp F _ _ S _ _ (φ := HasBox.box φ) (ψ := HasBox.box ψ)
  have b1 : InferenceSystem.DerivableIn S
      (HasImp.imp
        (HasImp.imp (HasBox.box φ) (HasImp.imp (HasBox.box ψ) (HasBox.box (HasImp.imp (HasImp.imp φ (HasImp.imp ψ HasBot.bot)) HasBot.bot))))
        (HasImp.imp
          (HasImp.imp
            (HasImp.imp (HasImp.imp (HasBox.box φ) (HasImp.imp (HasBox.box ψ) HasBot.bot)) HasBot.bot)
            (HasBox.box φ))
          (HasImp.imp
            (HasImp.imp (HasImp.imp (HasBox.box φ) (HasImp.imp (HasBox.box ψ) HasBot.bot)) HasBot.bot)
            (HasImp.imp (HasBox.box ψ) (HasBox.box (HasImp.imp (HasImp.imp φ (HasImp.imp ψ HasBot.bot)) HasBot.bot)))))) :=
    b_combinator
  have step2 := ModusPonens.mp b1 comp1
  have step3 := ModusPonens.mp step2 lce_box
  have s_ax := HasAxiomImplyS.implyS (S := S)
    (φ := HasImp.imp (HasImp.imp (HasBox.box φ) (HasImp.imp (HasBox.box ψ) HasBot.bot)) HasBot.bot)
    (ψ := HasBox.box ψ)
    (χ := HasBox.box (HasImp.imp (HasImp.imp φ (HasImp.imp ψ HasBot.bot)) HasBot.bot))
  have step4 := ModusPonens.mp s_ax step3
  have backward := ModusPonens.mp step4 rce_box
  exact iff_intro forward backward

/-- Diamond-Disjunction Biconditional: `⊢ ◇(φ ∨ ψ) ↔ (◇φ ∨ ◇ψ)`. -/
theorem diamond_disj_iff {φ ψ : F} :
    InferenceSystem.DerivableIn S
      (HasImp.imp
        (HasImp.imp
          (HasImp.imp
            -- forward: ◇(φ∨ψ) → (◇φ ∨ ◇ψ)
            (HasImp.imp (HasBox.box (HasImp.imp (HasImp.imp (HasImp.imp φ HasBot.bot) ψ) HasBot.bot)) HasBot.bot)
            (HasImp.imp
              (HasImp.imp (HasImp.imp (HasBox.box (HasImp.imp φ HasBot.bot)) HasBot.bot) HasBot.bot)
              (HasImp.imp (HasBox.box (HasImp.imp ψ HasBot.bot)) HasBot.bot)))
          (HasImp.imp
            -- backward: (◇φ ∨ ◇ψ) → ◇(φ∨ψ)
            (HasImp.imp
              (HasImp.imp
                (HasImp.imp (HasImp.imp (HasBox.box (HasImp.imp φ HasBot.bot)) HasBot.bot) HasBot.bot)
                (HasImp.imp (HasBox.box (HasImp.imp ψ HasBot.bot)) HasBot.bot))
              (HasImp.imp (HasBox.box (HasImp.imp (HasImp.imp (HasImp.imp φ HasBot.bot) ψ) HasBot.bot)) HasBot.bot))
            HasBot.bot))
        HasBot.bot) := by
  -- Forward: ◇(φ∨ψ) → (◇φ ∨ ◇ψ)
  -- Get De Morgan biconditionals
  have demorgan_disj := @demorgan_disj_neg F _ _ S _ _ (φ := φ) (ψ := ψ)
  -- Extract backward: (¬φ ∧ ¬ψ) → ¬(φ ∨ ψ)
  have demorgan_back := ModusPonens.mp rce_imp demorgan_disj
  -- box_iff_intro on demorgan: □¬(φ∨ψ) ↔ □(¬φ∧¬ψ)
  have box_demorgan := box_iff_intro demorgan_disj
  -- Extract backward: □(¬φ∧¬ψ) → □¬(φ∨ψ)
  have box_demorgan_back := ModusPonens.mp rce_imp box_demorgan
  -- box_conj_iff for ¬φ, ¬ψ
  have box_conj_neg := @box_conj_iff F _ _ _ S _ _
    (φ := HasImp.imp φ HasBot.bot) (ψ := HasImp.imp ψ HasBot.bot)
  -- Extract backward: (□¬φ ∧ □¬ψ) → □(¬φ∧¬ψ)
  have conj_box_to_box_conj := ModusPonens.mp rce_imp box_conj_neg
  -- Compose: (□¬φ ∧ □¬ψ) → □¬(φ∨ψ)
  have conj_box_to_or_box := imp_trans conj_box_to_box_conj box_demorgan_back
  -- Contrapose: ◇(φ∨ψ) → ¬(□¬φ ∧ □¬ψ)
  have neg_box_or_to_neg_conj := contraposition conj_box_to_or_box
  -- De Morgan forward: ¬(□¬φ ∧ □¬ψ) → (◇φ ∨ ◇ψ)
  have demorgan_conj_fwd := @demorgan_conj_neg_forward F _ _ S _ _
    (φ := HasBox.box (HasImp.imp φ HasBot.bot))
    (ψ := HasBox.box (HasImp.imp ψ HasBot.bot))
  have forward := imp_trans neg_box_or_to_neg_conj demorgan_conj_fwd
  -- Backward: (◇φ ∨ ◇ψ) → ◇(φ∨ψ)
  have demorgan_conj_bwd := @demorgan_conj_neg_backward F _ _ S _ _
    (φ := HasBox.box (HasImp.imp φ HasBot.bot))
    (ψ := HasBox.box (HasImp.imp ψ HasBot.bot))
  have box_conj_to_conj_box := ModusPonens.mp lce_imp box_conj_neg
  have neg_conj_to_neg_box := contraposition box_conj_to_conj_box
  have box_demorgan_fwd := ModusPonens.mp lce_imp box_demorgan
  have neg_box_conj_to_neg_box_or := contraposition box_demorgan_fwd
  have step1 := imp_trans demorgan_conj_bwd neg_conj_to_neg_box
  have backward := imp_trans step1 neg_box_conj_to_neg_box_or
  exact iff_intro forward backward

/-! ## S5 Collapse and Diamond-Box Theorems -/

/-- S5-Diamond-Box Collapse: `⊢ ◇□φ ↔ □φ`. -/
theorem s5_diamond_box {φ : F} :
    InferenceSystem.DerivableIn S
      (HasImp.imp
        (HasImp.imp
          (HasImp.imp
            (HasImp.imp (HasBox.box (HasImp.imp (HasBox.box φ) HasBot.bot)) HasBot.bot)
            (HasBox.box φ))
          (HasImp.imp
            (HasImp.imp (HasBox.box φ)
              (HasImp.imp (HasBox.box (HasImp.imp (HasBox.box φ) HasBot.bot)) HasBot.bot))
            HasBot.bot))
        HasBot.bot) := by
  have forward := @axiom5_collapse_derived F _ _ _ S _ _ (φ := φ)
  have m4_a := HasAxiom4.four (S := S) (φ := φ)
  have box_box_to_diamond := @t_box_to_diamond F _ _ _ S _ _ (φ := HasBox.box φ)
  have backward := imp_trans m4_a box_box_to_diamond
  exact iff_intro forward backward

/-- S5-Diamond-Box-to-Truth: `⊢ ◇□φ → φ`. -/
theorem s5_diamond_box_to_truth {φ : F} :
    InferenceSystem.DerivableIn S
      (HasImp.imp
        (HasImp.imp (HasBox.box (HasImp.imp (HasBox.box φ) HasBot.bot)) HasBot.bot)
        φ) := by
  have h1 := @axiom5_collapse_derived F _ _ _ S _ _ (φ := φ)
  have h2 := HasAxiomT.T (S := S) (φ := φ)
  exact imp_trans h1 h2

/-! ## S4-Level Nested Modality Theorems -/

/-- S4-Diamond-Box-Conjunction: `⊢ (◇A ∧ □B) → ◇(A ∧ □B)`. -/
theorem s4_diamond_box_conj {A B : F} :
    let conjABoxB := HasImp.imp (HasImp.imp A (HasImp.imp (HasBox.box B) HasBot.bot)) HasBot.bot
    let diamondA := HasImp.imp (HasBox.box (HasImp.imp A HasBot.bot)) HasBot.bot
    let conjDiamondABoxB := HasImp.imp (HasImp.imp diamondA (HasImp.imp (HasBox.box B) HasBot.bot)) HasBot.bot
    let diamondConjABoxB := HasImp.imp (HasBox.box (HasImp.imp conjABoxB HasBot.bot)) HasBot.bot
    InferenceSystem.DerivableIn S
      (HasImp.imp conjDiamondABoxB diamondConjABoxB) := by
  -- pairing: A → □B → (A ∧ □B)
  have pair := pairing (S := S) A (HasBox.box B)
  -- flip: □B → (A → (A ∧ □B))
  have flipped := ModusPonens.mp
    (@theorem_flip F _ _ S _ _ A (HasBox.box B)
      (HasImp.imp (HasImp.imp A (HasImp.imp (HasBox.box B) HasBot.bot)) HasBot.bot))
    pair
  -- 4: □B → □□B
  have m4_b := HasAxiom4.four (S := S) (φ := B)
  -- box_mono: □□B → □(A → (A ∧ □B))
  have box_flipped := box_mono flipped
  -- Compose: □B → □(A → (A ∧ □B))
  have box_b_to_box_imp := imp_trans m4_b box_flipped
  -- k_dist_diamond: □(A → (A ∧ □B)) → (◇A → ◇(A ∧ □B))
  have k_dist := @k_dist_diamond F _ _ _ S _ _
    (φ := A)
    (ψ := HasImp.imp (HasImp.imp A (HasImp.imp (HasBox.box B) HasBot.bot)) HasBot.bot)
  -- Compose: □B → (◇A → ◇(A ∧ □B))
  have box_b_to_diamond_imp := imp_trans box_b_to_box_imp k_dist
  -- Extract □B: (◇A ∧ □B) → □B
  have rce_conj := @rce_imp F _ _ S _ _
    (φ := HasImp.imp (HasBox.box (HasImp.imp A HasBot.bot)) HasBot.bot)
    (ψ := HasBox.box B)
  -- Extract ◇A: (◇A ∧ □B) → ◇A
  have lce_conj := @lce_imp F _ _ S _ _
    (φ := HasImp.imp (HasBox.box (HasImp.imp A HasBot.bot)) HasBot.bot)
    (ψ := HasBox.box B)
  -- Compose: (◇A ∧ □B) → □B → (◇A → ◇(A ∧ □B))
  have conj_to_box_b := imp_trans rce_conj box_b_to_diamond_imp
  -- Use S axiom: (P → Q → R) → ((P → Q) → (P → R))
  -- Note: ◇(A∧□B) = (□(((A→(□B→⊥))→⊥)→⊥))→⊥ (diamond of conjunction has inner double negation)
  have s_ax := HasAxiomImplyS.implyS (S := S)
    (φ := HasImp.imp
      (HasImp.imp
        (HasImp.imp (HasBox.box (HasImp.imp A HasBot.bot)) HasBot.bot)
        (HasImp.imp (HasBox.box B) HasBot.bot))
      HasBot.bot)
    (ψ := HasImp.imp (HasBox.box (HasImp.imp A HasBot.bot)) HasBot.bot)
    (χ := HasImp.imp
      (HasBox.box
        (HasImp.imp
          (HasImp.imp (HasImp.imp A (HasImp.imp (HasBox.box B) HasBot.bot)) HasBot.bot)
          HasBot.bot))
      HasBot.bot)
  have step1 := ModusPonens.mp s_ax conj_to_box_b
  exact ModusPonens.mp step1 lce_conj

/-- S4-Box-Diamond-Box: `⊢ □A → □(◇□A)`.

Direct from axiom B applied to □A. -/
theorem s4_box_diamond_box {A : F} :
    InferenceSystem.DerivableIn S
      (HasImp.imp (HasBox.box A)
        (HasBox.box
          (HasImp.imp
            (HasBox.box (HasImp.imp (HasBox.box A) HasBot.bot))
            HasBot.bot))) :=
  HasAxiomB.B (S := S) (φ := HasBox.box A)

/-- S4-Diamond-Box-Diamond: `⊢ ◇(□(◇A)) ↔ ◇A`. -/
theorem s4_diamond_box_diamond {A : F} :
    let diamondA := HasImp.imp (HasBox.box (HasImp.imp A HasBot.bot)) HasBot.bot
    let boxDiamondA := HasBox.box diamondA
    let diamondBoxDiamondA := HasImp.imp (HasBox.box (HasImp.imp boxDiamondA HasBot.bot)) HasBot.bot
    InferenceSystem.DerivableIn S
      (HasImp.imp
        (HasImp.imp
          (HasImp.imp diamondBoxDiamondA diamondA)
          (HasImp.imp (HasImp.imp diamondA diamondBoxDiamondA) HasBot.bot))
        HasBot.bot) := by
  -- Forward: ◇□◇A → ◇A
  -- axiom5_collapse on ◇A: ◇□◇A → □◇A
  have m5c := @axiom5_collapse_derived F _ _ _ S _ _
    (φ := HasImp.imp (HasBox.box (HasImp.imp A HasBot.bot)) HasBot.bot)
  -- T on ◇A: □◇A → ◇A
  have t_dia := HasAxiomT.T (S := S)
    (φ := HasImp.imp (HasBox.box (HasImp.imp A HasBot.bot)) HasBot.bot)
  have forward := imp_trans m5c t_dia
  -- Backward: ◇A → ◇□◇A
  -- axiom5 on A: ◇A → □◇A
  have ax5_a := @axiom5_derived F _ _ _ S _ _ (φ := A)
  -- 4 on ◇A: □◇A → □□◇A
  have m4_dia := HasAxiom4.four (S := S)
    (φ := HasImp.imp (HasBox.box (HasImp.imp A HasBot.bot)) HasBot.bot)
  -- t_box_to_diamond on □◇A: □□◇A → ◇□◇A
  have box_box_to_dia := @t_box_to_diamond F _ _ _ S _ _
    (φ := HasBox.box (HasImp.imp (HasBox.box (HasImp.imp A HasBot.bot)) HasBot.bot))
  have step1 := imp_trans ax5_a m4_dia
  have backward := imp_trans step1 box_box_to_dia
  exact iff_intro forward backward

/-- S5-Diamond-Conjunction-Diamond: `⊢ ◇(A ∧ ◇B) ↔ (◇A ∧ ◇B)`. -/
theorem s5_diamond_conj_diamond {A B : F} :
    let diamondB := HasImp.imp (HasBox.box (HasImp.imp B HasBot.bot)) HasBot.bot
    let conjADiaB := HasImp.imp (HasImp.imp A (HasImp.imp diamondB HasBot.bot)) HasBot.bot
    let diamondConjADiaB := HasImp.imp (HasBox.box (HasImp.imp conjADiaB HasBot.bot)) HasBot.bot
    let diamondA := HasImp.imp (HasBox.box (HasImp.imp A HasBot.bot)) HasBot.bot
    let conjDiaADiaB := HasImp.imp (HasImp.imp diamondA (HasImp.imp diamondB HasBot.bot)) HasBot.bot
    InferenceSystem.DerivableIn S
      (HasImp.imp
        (HasImp.imp
          (HasImp.imp diamondConjADiaB conjDiaADiaB)
          (HasImp.imp (HasImp.imp conjDiaADiaB diamondConjADiaB) HasBot.bot))
        HasBot.bot) := by
  -- Forward: ◇(A ∧ ◇B) → (◇A ∧ ◇B)
  -- lce: (A ∧ ◇B) → A
  have lce := @lce_imp F _ _ S _ _
    (φ := A)
    (ψ := HasImp.imp (HasBox.box (HasImp.imp B HasBot.bot)) HasBot.bot)
  have dia_lce := diamond_mono lce
  -- rce: (A ∧ ◇B) → ◇B
  have rce := @rce_imp F _ _ S _ _
    (φ := A)
    (ψ := HasImp.imp (HasBox.box (HasImp.imp B HasBot.bot)) HasBot.bot)
  have dia_rce := diamond_mono rce
  -- diamond_4: ◇◇B → ◇B
  have dia_dia_to_dia := @diamond_4 F _ _ _ S _ _ (φ := B)
  -- Compose: ◇(A ∧ ◇B) → ◇B
  have dia_conj_to_dia_b := imp_trans dia_rce dia_dia_to_dia
  -- combine: ◇(A ∧ ◇B) → (◇A ∧ ◇B)
  have forward := combine_imp_conj dia_lce dia_conj_to_dia_b
  -- Backward: (◇A ∧ ◇B) → ◇(A ∧ ◇B)
  -- axiom5 on B: ◇B → □◇B
  have ax5_b := @axiom5_derived F _ _ _ S _ _ (φ := B)
  -- pairing: A → ◇B → (A ∧ ◇B)
  have pair := pairing (S := S) A
    (HasImp.imp (HasBox.box (HasImp.imp B HasBot.bot)) HasBot.bot)
  -- flip: ◇B → (A → (A ∧ ◇B))
  have flipped := ModusPonens.mp
    (@theorem_flip F _ _ S _ _ A
      (HasImp.imp (HasBox.box (HasImp.imp B HasBot.bot)) HasBot.bot)
      (HasImp.imp
        (HasImp.imp A
          (HasImp.imp (HasImp.imp (HasBox.box (HasImp.imp B HasBot.bot)) HasBot.bot) HasBot.bot))
        HasBot.bot))
    pair
  -- box_mono: □◇B → □(A → (A ∧ ◇B))
  have box_flipped := box_mono flipped
  -- Compose: ◇B → □(A → (A ∧ ◇B))
  have dia_b_to_box_imp := imp_trans ax5_b box_flipped
  -- k_dist_diamond: □(A → (A ∧ ◇B)) → (◇A → ◇(A ∧ ◇B))
  have k_dist := @k_dist_diamond F _ _ _ S _ _
    (φ := A)
    (ψ := HasImp.imp
      (HasImp.imp A
        (HasImp.imp (HasImp.imp (HasBox.box (HasImp.imp B HasBot.bot)) HasBot.bot) HasBot.bot))
      HasBot.bot)
  -- Compose: ◇B → (◇A → ◇(A ∧ ◇B))
  have dia_b_to_imp := imp_trans dia_b_to_box_imp k_dist
  -- Extract ◇B: (◇A ∧ ◇B) → ◇B
  have rce_conj := @rce_imp F _ _ S _ _
    (φ := HasImp.imp (HasBox.box (HasImp.imp A HasBot.bot)) HasBot.bot)
    (ψ := HasImp.imp (HasBox.box (HasImp.imp B HasBot.bot)) HasBot.bot)
  -- Extract ◇A: (◇A ∧ ◇B) → ◇A
  have lce_conj := @lce_imp F _ _ S _ _
    (φ := HasImp.imp (HasBox.box (HasImp.imp A HasBot.bot)) HasBot.bot)
    (ψ := HasImp.imp (HasBox.box (HasImp.imp B HasBot.bot)) HasBot.bot)
  -- Compose: (◇A ∧ ◇B) → ◇B → (◇A → ◇(A ∧ ◇B))
  have conj_to_dia_b := imp_trans rce_conj dia_b_to_imp
  -- Use S axiom
  have s_ax := HasAxiomImplyS.implyS (S := S)
    (φ := HasImp.imp
      (HasImp.imp
        (HasImp.imp (HasBox.box (HasImp.imp A HasBot.bot)) HasBot.bot)
        (HasImp.imp (HasImp.imp (HasBox.box (HasImp.imp B HasBot.bot)) HasBot.bot) HasBot.bot))
      HasBot.bot)
    (ψ := HasImp.imp (HasBox.box (HasImp.imp A HasBot.bot)) HasBot.bot)
    (χ := HasImp.imp
      (HasBox.box
        (HasImp.imp
          (HasImp.imp
            (HasImp.imp A
              (HasImp.imp (HasImp.imp (HasBox.box (HasImp.imp B HasBot.bot)) HasBot.bot) HasBot.bot))
            HasBot.bot)
          HasBot.bot))
      HasBot.bot)
  have step1 := ModusPonens.mp s_ax conj_to_dia_b
  have backward := ModusPonens.mp step1 lce_conj
  exact iff_intro forward backward

end -- noncomputable section

end Cslib.Logic.Theorems.Modal.S5
