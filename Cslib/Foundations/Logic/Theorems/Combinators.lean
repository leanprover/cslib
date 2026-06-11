/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Foundations.Logic.ProofSystem

/-! # Propositional Reasoning Combinators

This module defines fundamental propositional reasoning combinators derived from
the ImplyK and ImplyS axioms. These combinators provide the foundation for all
propositional theorems in the Hilbert-style proof system.

All theorems are generic over `[MinimalHilbert S]`.

## Main Combinators

- `imp_trans`: Transitivity of implication (hypothetical syllogism)
- `identity`: Identity combinator (SKK construction)
- `b_combinator`: B combinator (function composition)
- `flip`: C combinator (argument flip)
- `app1`: Single application lemma
- `app2`: Double application lemma (Vireo combinator)
- `pairing`: Conjunction introduction combinator
- `dni`: Double negation introduction
- `combine_imp_conj`: Combine implications into conjunction
- `combine_imp_conj_3`: Combine three implications into conjunction

## Naming Convention

BimodalLogic's `Axiom.prop_s` (weakening: φ → (ψ → φ)) maps to cslib's
`ImplyK`. BimodalLogic's `Axiom.prop_k` (distribution) maps to cslib's
`ImplyS`.
-/

@[expose] public section

namespace Cslib.Logic.Theorems.Combinators

open Cslib.Logic

variable {F : Type*} [HasBot F] [HasImp F]
variable {S : Type*} [InferenceSystem S F]
variable [MinimalHilbert S (F := F)]

section Combinators

/-- Transitivity of implication: from `⊢ φ → ψ` and `⊢ ψ → χ`,
    derive `⊢ φ → χ`. -/
theorem imp_trans {φ ψ χ : F}
    (h1 : InferenceSystem.DerivableIn S (HasImp.imp φ ψ))
    (h2 : InferenceSystem.DerivableIn S (HasImp.imp ψ χ)) :
    InferenceSystem.DerivableIn S (HasImp.imp φ χ) := by
  have h3 := ModusPonens.mp
    (HasAxiomImplyK.implyK
      (S := S) (φ := HasImp.imp ψ χ) (ψ := φ)) h2
  have h4 := ModusPonens.mp
    (HasAxiomImplyS.implyS
      (S := S) (φ := φ) (ψ := ψ) (χ := χ)) h3
  exact ModusPonens.mp h4 h1

/-- Identity combinator: `⊢ φ → φ` (SKK construction). -/
theorem identity (φ : F) :
    InferenceSystem.DerivableIn S (HasImp.imp φ φ) := by
  have k1 : InferenceSystem.DerivableIn S
      (HasImp.imp φ (HasImp.imp (HasImp.imp φ φ) φ)) :=
    HasAxiomImplyK.implyK
  have k2 : InferenceSystem.DerivableIn S
      (HasImp.imp φ (HasImp.imp φ φ)) :=
    HasAxiomImplyK.implyK
  have s1 := HasAxiomImplyS.implyS
    (S := S) (φ := φ) (ψ := HasImp.imp φ φ) (χ := φ)
  exact ModusPonens.mp (ModusPonens.mp s1 k1) k2

/-- B combinator (composition):
    `⊢ (ψ → χ) → (φ → ψ) → (φ → χ)`. -/
theorem b_combinator {φ ψ χ : F} :
    InferenceSystem.DerivableIn S
      (HasImp.imp (HasImp.imp ψ χ)
        (HasImp.imp (HasImp.imp φ ψ)
          (HasImp.imp φ χ))) :=
  imp_trans HasAxiomImplyK.implyK HasAxiomImplyS.implyS

/-- C combinator (flip):
    `⊢ (φ → ψ → χ) → (ψ → φ → χ)`. -/
theorem flip {φ ψ χ : F} :
    InferenceSystem.DerivableIn S
      (HasImp.imp (HasImp.imp φ (HasImp.imp ψ χ))
        (HasImp.imp ψ (HasImp.imp φ χ))) := by
  have step1 := HasAxiomImplyK.implyK (S := S)
    (φ := HasImp.imp φ (HasImp.imp ψ χ)) (ψ := ψ)
  have k_abc := HasAxiomImplyS.implyS (S := S)
    (φ := φ) (ψ := ψ) (χ := χ)
  have step2 := ModusPonens.mp
    (HasAxiomImplyK.implyK (S := S)
      (φ := HasImp.imp
        (HasImp.imp φ (HasImp.imp ψ χ))
        (HasImp.imp (HasImp.imp φ ψ) (HasImp.imp φ χ)))
      (ψ := ψ))
    k_abc
  have step3 := ModusPonens.mp
    (HasAxiomImplyS.implyS (S := S) (φ := ψ)
      (ψ := HasImp.imp φ (HasImp.imp ψ χ))
      (χ := HasImp.imp (HasImp.imp φ ψ) (HasImp.imp φ χ)))
    step2
  have step4 := imp_trans step1 step3
  have s_ab := HasAxiomImplyK.implyK (S := S)
    (φ := ψ) (ψ := φ)
  have k_final := HasAxiomImplyS.implyS (S := S) (φ := ψ)
    (ψ := HasImp.imp φ ψ) (χ := HasImp.imp φ χ)
  have step5 := imp_trans step4 k_final
  have step6 := ModusPonens.mp
    (HasAxiomImplyK.implyK (S := S)
      (φ := HasImp.imp ψ (HasImp.imp φ ψ))
      (ψ := HasImp.imp φ (HasImp.imp ψ χ)))
    s_ab
  have k_combine := HasAxiomImplyS.implyS (S := S)
    (φ := HasImp.imp φ (HasImp.imp ψ χ))
    (ψ := HasImp.imp ψ (HasImp.imp φ ψ))
    (χ := HasImp.imp ψ (HasImp.imp φ χ))
  exact ModusPonens.mp
    (ModusPonens.mp k_combine step5) step6

/-- Single application lemma: `⊢ φ → (φ → ψ) → ψ`. -/
theorem app1 {φ ψ : F} :
    InferenceSystem.DerivableIn S
      (HasImp.imp φ
        (HasImp.imp (HasImp.imp φ ψ) ψ)) := by
  have id_ab := identity (S := S) (HasImp.imp φ ψ)
  exact ModusPonens.mp
    (@flip F _ _ S _ _
      (HasImp.imp φ ψ) φ ψ) id_ab

/-- Double application (Vireo):
    `⊢ φ → ψ → (φ → ψ → χ) → χ`. -/
theorem app2 {φ ψ χ : F} :
    InferenceSystem.DerivableIn S
      (HasImp.imp φ (HasImp.imp ψ
        (HasImp.imp (HasImp.imp φ (HasImp.imp ψ χ))
          χ))) := by
  -- Stage 1: Build the two app1 base lemmas
  have step_a : InferenceSystem.DerivableIn S
      (HasImp.imp φ (HasImp.imp
        (HasImp.imp φ (HasImp.imp ψ χ))
        (HasImp.imp ψ χ))) :=
    app1
  have step_b : InferenceSystem.DerivableIn S
      (HasImp.imp ψ (HasImp.imp (HasImp.imp ψ χ) χ)) :=
    app1
  -- Stage 2: Weaken and flip to get both under ψ scope
  have a_b_bc_c := ModusPonens.mp
    (HasAxiomImplyK.implyK (S := S)
      (φ := HasImp.imp ψ (HasImp.imp (HasImp.imp ψ χ) χ))
      (ψ := φ))
    step_b
  have b_a := ModusPonens.mp
    (HasAxiomImplyK.implyK (S := S)
      (φ := HasImp.imp φ (HasImp.imp
        (HasImp.imp φ (HasImp.imp ψ χ))
        (HasImp.imp ψ χ)))
      (ψ := ψ))
    step_a
  have a_b_abc_bc := ModusPonens.mp
    (@flip F _ _ S _ _
      ψ φ (HasImp.imp
        (HasImp.imp φ (HasImp.imp ψ χ))
        (HasImp.imp ψ χ)))
    b_a
  -- Stage 3: B-combinator composition for (ψ→χ)→χ chain
  have b_comp : InferenceSystem.DerivableIn S
      (HasImp.imp (HasImp.imp (HasImp.imp ψ χ) χ)
        (HasImp.imp
          (HasImp.imp (HasImp.imp φ (HasImp.imp ψ χ))
            (HasImp.imp ψ χ))
          (HasImp.imp
            (HasImp.imp φ (HasImp.imp ψ χ)) χ))) :=
    b_combinator
  have b_b_comp := ModusPonens.mp
    (HasAxiomImplyK.implyK (S := S)
      (φ := HasImp.imp
        (HasImp.imp (HasImp.imp ψ χ) χ)
        (HasImp.imp
          (HasImp.imp (HasImp.imp φ (HasImp.imp ψ χ))
            (HasImp.imp ψ χ))
          (HasImp.imp
            (HasImp.imp φ (HasImp.imp ψ χ)) χ)))
      (ψ := ψ))
    b_comp
  have k_b := HasAxiomImplyS.implyS (S := S) (φ := ψ)
    (ψ := HasImp.imp (HasImp.imp ψ χ) χ)
    (χ := HasImp.imp
      (HasImp.imp (HasImp.imp φ (HasImp.imp ψ χ))
        (HasImp.imp ψ χ))
      (HasImp.imp (HasImp.imp φ (HasImp.imp ψ χ)) χ))
  have step7_b := ModusPonens.mp k_b b_b_comp
  -- Stage 4: Lift composition under φ scope via S and K
  have weak_step7 := ModusPonens.mp
    (HasAxiomImplyK.implyK (S := S)
      (φ := HasImp.imp
        (HasImp.imp ψ (HasImp.imp (HasImp.imp ψ χ) χ))
        (HasImp.imp ψ
          (HasImp.imp
            (HasImp.imp (HasImp.imp φ (HasImp.imp ψ χ))
              (HasImp.imp ψ χ))
            (HasImp.imp
              (HasImp.imp φ (HasImp.imp ψ χ)) χ))))
      (ψ := φ))
    step7_b
  have k_a := HasAxiomImplyS.implyS (S := S) (φ := φ)
    (ψ := HasImp.imp ψ (HasImp.imp (HasImp.imp ψ χ) χ))
    (χ := HasImp.imp ψ
      (HasImp.imp
        (HasImp.imp (HasImp.imp φ (HasImp.imp ψ χ))
          (HasImp.imp ψ χ))
        (HasImp.imp (HasImp.imp φ (HasImp.imp ψ χ)) χ)))
  have step8 := ModusPonens.mp k_a weak_step7
  have step9 := ModusPonens.mp step8 a_b_bc_c
  -- Stage 5: Final composition — collapse to φ → ψ → (φ→ψ→χ) → χ
  have k_b_final := HasAxiomImplyS.implyS (S := S)
    (φ := ψ)
    (ψ := HasImp.imp
      (HasImp.imp φ (HasImp.imp ψ χ))
      (HasImp.imp ψ χ))
    (χ := HasImp.imp
      (HasImp.imp φ (HasImp.imp ψ χ)) χ)
  have weak_k_b := ModusPonens.mp
    (HasAxiomImplyK.implyK (S := S)
      (φ := HasImp.imp
        (HasImp.imp ψ
          (HasImp.imp
            (HasImp.imp (HasImp.imp φ (HasImp.imp ψ χ))
              (HasImp.imp ψ χ))
            (HasImp.imp
              (HasImp.imp φ (HasImp.imp ψ χ)) χ)))
        (HasImp.imp
          (HasImp.imp ψ (HasImp.imp
            (HasImp.imp φ (HasImp.imp ψ χ))
            (HasImp.imp ψ χ)))
          (HasImp.imp ψ
            (HasImp.imp
              (HasImp.imp φ (HasImp.imp ψ χ)) χ))))
      (ψ := φ))
    k_b_final
  have k_a_outer := HasAxiomImplyS.implyS (S := S)
    (φ := φ)
    (ψ := HasImp.imp ψ
      (HasImp.imp
        (HasImp.imp (HasImp.imp φ (HasImp.imp ψ χ))
          (HasImp.imp ψ χ))
        (HasImp.imp (HasImp.imp φ (HasImp.imp ψ χ)) χ)))
    (χ := HasImp.imp
      (HasImp.imp ψ (HasImp.imp
        (HasImp.imp φ (HasImp.imp ψ χ))
        (HasImp.imp ψ χ)))
      (HasImp.imp ψ
        (HasImp.imp (HasImp.imp φ (HasImp.imp ψ χ)) χ)))
  have step10_a := ModusPonens.mp k_a_outer weak_k_b
  have step10 := ModusPonens.mp step10_a step9
  have k_a_final := HasAxiomImplyS.implyS (S := S)
    (φ := φ)
    (ψ := HasImp.imp ψ (HasImp.imp
      (HasImp.imp φ (HasImp.imp ψ χ))
      (HasImp.imp ψ χ)))
    (χ := HasImp.imp ψ
      (HasImp.imp (HasImp.imp φ (HasImp.imp ψ χ)) χ))
  have step11 := ModusPonens.mp k_a_final step10
  exact ModusPonens.mp step11 a_b_abc_bc

/-- Pairing combinator: `⊢ φ → ψ → ¬(φ → ¬ψ)`.
    This is conjunction introduction where
    `φ ∧ ψ := (φ → (ψ → ⊥)) → ⊥`. -/
theorem pairing (φ ψ : F) :
    InferenceSystem.DerivableIn S
      (HasImp.imp φ (HasImp.imp ψ
        (HasImp.imp
          (HasImp.imp φ (HasImp.imp ψ HasBot.bot))
          HasBot.bot))) :=
  @app2 F _ _ S _ _ φ ψ HasBot.bot

/-- Double negation introduction: `⊢ φ → ¬¬φ`
    where `¬φ := φ → ⊥`. -/
theorem dni (φ : F) :
    InferenceSystem.DerivableIn S
      (HasImp.imp φ
        (HasImp.imp (HasImp.imp φ HasBot.bot)
          HasBot.bot)) :=
  @app1 F _ _ S _ _ (φ := φ) (ψ := HasBot.bot)

/-- Combine two implications into conjunction:
    from `⊢ P → A` and `⊢ P → B`,
    derive `⊢ P → ¬(A → ¬B)`. -/
theorem combine_imp_conj {P A₁ B₁ : F}
    (hA : InferenceSystem.DerivableIn S
      (HasImp.imp P A₁))
    (hB : InferenceSystem.DerivableIn S
      (HasImp.imp P B₁)) :
    InferenceSystem.DerivableIn S
      (HasImp.imp P
        (HasImp.imp
          (HasImp.imp A₁ (HasImp.imp B₁ HasBot.bot))
          HasBot.bot)) := by
  have h1 := imp_trans hA (pairing A₁ B₁)
  have s1 := HasAxiomImplyS.implyS (S := S)
    (φ := P) (ψ := B₁)
    (χ := HasImp.imp
      (HasImp.imp A₁ (HasImp.imp B₁ HasBot.bot))
      HasBot.bot)
  exact ModusPonens.mp (ModusPonens.mp s1 h1) hB

/-- Combine three implications into nested conjunction:
    from `⊢ P → A`, `⊢ P → B`, `⊢ P → C`,
    derive `⊢ P → ¬(A → ¬(¬(B → ¬C)))`. -/
theorem combine_imp_conj_3 {P A₁ B₁ C₁ : F}
    (hA : InferenceSystem.DerivableIn S
      (HasImp.imp P A₁))
    (hB : InferenceSystem.DerivableIn S
      (HasImp.imp P B₁))
    (hC : InferenceSystem.DerivableIn S
      (HasImp.imp P C₁)) :
    InferenceSystem.DerivableIn S
      (HasImp.imp P
        (HasImp.imp
          (HasImp.imp A₁
            (HasImp.imp
              (HasImp.imp
                (HasImp.imp B₁
                  (HasImp.imp C₁ HasBot.bot))
                HasBot.bot)
              HasBot.bot))
          HasBot.bot)) :=
  combine_imp_conj hA (combine_imp_conj hB hC)

end Combinators

end Cslib.Logic.Theorems.Combinators
