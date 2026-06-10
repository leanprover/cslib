/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Foundations.Logic.Theorems.Propositional.Core

/-! # Derived Connective Theorems

Classical merge, iff introduction, contraposition, and De Morgan laws
for the Hilbert-style proof system.

All theorems are generic over `[PropositionalHilbert S]`.

## Main Results

- `classical_merge`: `(P → Q) → ((¬P → Q) → Q)` (DT-free)
- `iff_intro`: From `⊢ A → B` and `⊢ B → A`, derive `⊢ A ↔ B`
- `contrapose_imp`: `(A → B) → (¬B → ¬A)`
- `contraposition`: From `⊢ A → B`, derive `⊢ ¬B → ¬A`
- `contrapose_iff`: From `⊢ A ↔ B`, derive `⊢ ¬A ↔ ¬B`
- `demorgan_conj_neg_forward`: `¬(A ∧ B) → (¬A ∨ ¬B)`
- `demorgan_conj_neg_backward`: `(¬A ∨ ¬B) → ¬(A ∧ B)`
- `demorgan_disj_neg_forward`: `¬(A ∨ B) → (¬A ∧ ¬B)`
- `demorgan_disj_neg_backward`: `(¬A ∧ ¬B) → ¬(A ∨ B)`

## Encoding

- `¬φ = φ → ⊥`
- `φ ∧ ψ = (φ → (ψ → ⊥)) → ⊥`
- `φ ∨ ψ = (φ → ⊥) → ψ`
- `φ ↔ ψ = (φ → ψ) ∧ (ψ → φ)`
-/

@[expose] public section

namespace Cslib.Logic.Theorems.Propositional.Connectives

open Cslib.Logic
open Cslib.Logic.Theorems.Combinators
open Cslib.Logic.Theorems.Propositional.Core

variable {F : Type*} [HasBot F] [HasImp F]
variable {S : Type*} [InferenceSystem S F]
variable [PropositionalHilbert S (F := F)]

section Connectives

/-- Contraposition (implication form):
    `⊢ (φ → ψ) → (¬ψ → ¬φ)`. -/
theorem contrapose_imp {φ ψ : F} :
    InferenceSystem.DerivableIn S
      (HasImp.imp (HasImp.imp φ ψ)
        (HasImp.imp (HasImp.imp ψ HasBot.bot)
          (HasImp.imp φ HasBot.bot))) := by
  -- b: (ψ→⊥) → (φ→ψ) → (φ→⊥)
  have bc : InferenceSystem.DerivableIn S
      (HasImp.imp (HasImp.imp ψ HasBot.bot)
        (HasImp.imp (HasImp.imp φ ψ)
          (HasImp.imp φ HasBot.bot))) :=
    b_combinator
  -- flip: (φ→ψ) → (ψ→⊥) → (φ→⊥)
  exact ModusPonens.mp
    (@flip F _ _ S _ _
      (HasImp.imp ψ HasBot.bot)
      (HasImp.imp φ ψ)
      (HasImp.imp φ HasBot.bot))
    bc

/-- Contraposition (meta): from `⊢ φ → ψ`,
    derive `⊢ ¬ψ → ¬φ`. -/
theorem contraposition {φ ψ : F}
    (h : InferenceSystem.DerivableIn S
      (HasImp.imp φ ψ)) :
    InferenceSystem.DerivableIn S
      (HasImp.imp (HasImp.imp ψ HasBot.bot)
        (HasImp.imp φ HasBot.bot)) :=
  ModusPonens.mp contrapose_imp h

/-- Classical merge (DT-free):
    `⊢ (P → Q) → ((¬P → Q) → Q)`.

    Proof: Contrapose both premises to get
    (¬Q → ¬P) and (¬Q → ¬¬P), derive ¬¬Q via
    contradiction, then apply DNE. -/
theorem classical_merge {φ ψ : F} :
    InferenceSystem.DerivableIn S
      (HasImp.imp (HasImp.imp φ ψ)
        (HasImp.imp
          (HasImp.imp (HasImp.imp φ HasBot.bot) ψ)
          ψ)) := by
  -- Strategy: use Peirce(ψ,⊥): ((ψ→⊥)→ψ)→ψ
  -- We need: (φ→ψ) → ((¬φ→ψ) → ((ψ→⊥)→ψ))
  -- From (φ→ψ), contrapose: (¬ψ→¬φ)
  -- From (¬φ→ψ) and (¬ψ→¬φ), compose: (¬ψ→ψ)
  -- This is: ((ψ→⊥)→ψ), which feeds Peirce.
  have peirce_inst := HasAxiomPeirce.peirce (S := S)
    (φ := ψ) (ψ := HasBot.bot)
  -- Build: (φ→ψ) → ((¬φ→ψ) → ((ψ→⊥)→ψ))
  -- Step 1: (φ→ψ) gives (¬ψ→¬φ) by contrapose_imp
  -- Step 2: (¬ψ→¬φ) and (¬φ→ψ) give (¬ψ→ψ) by imp_trans
  -- So we need: (¬ψ→¬φ) → ((¬φ→ψ) → ((ψ→⊥)→ψ))

  -- b: (¬φ→ψ) → ((ψ→⊥)→¬φ) → ((ψ→⊥)→ψ)
  -- flip b: ((ψ→⊥)→¬φ) → ((¬φ→ψ) → ((ψ→⊥)→ψ))
  -- Then compose with contrapose_imp(φ,ψ)

  -- Actually, simpler route using imp_trans:
  -- b: (¬φ→ψ) → ((ψ→⊥)→¬φ) → ((ψ→⊥)→ψ)
  have bc : InferenceSystem.DerivableIn S
      (HasImp.imp
        (HasImp.imp (HasImp.imp φ HasBot.bot) ψ)
        (HasImp.imp
          (HasImp.imp (HasImp.imp ψ HasBot.bot)
            (HasImp.imp φ HasBot.bot))
          (HasImp.imp (HasImp.imp ψ HasBot.bot) ψ))) :=
    b_combinator
  -- flip: (¬ψ→¬φ) → ((¬φ→ψ) → ((ψ→⊥)→ψ))
  have flip_bc := ModusPonens.mp
    (@flip F _ _ S _ _
      (HasImp.imp (HasImp.imp φ HasBot.bot) ψ)
      (HasImp.imp (HasImp.imp ψ HasBot.bot)
        (HasImp.imp φ HasBot.bot))
      (HasImp.imp (HasImp.imp ψ HasBot.bot) ψ))
    bc
  -- Compose: (φ→ψ) → contrapose → (¬ψ→¬φ) →
  --   flip_bc → ((¬φ→ψ) → ((ψ→⊥)→ψ))
  have step1 := imp_trans
    (@contrapose_imp F _ _ S _ _ (φ := φ) (ψ := ψ))
    flip_bc
  -- step1: (φ→ψ) → ((¬φ→ψ) → ((ψ→⊥)→ψ))

  -- Now compose inner part with Peirce:
  -- b: (((ψ→⊥)→ψ)→ψ) → ((¬φ→ψ)→((ψ→⊥)→ψ)) →
  --    ((¬φ→ψ)→ψ)
  have bc2 : InferenceSystem.DerivableIn S
      (HasImp.imp
        (HasImp.imp
          (HasImp.imp (HasImp.imp ψ HasBot.bot) ψ) ψ)
        (HasImp.imp
          (HasImp.imp
            (HasImp.imp (HasImp.imp φ HasBot.bot) ψ)
            (HasImp.imp (HasImp.imp ψ HasBot.bot) ψ))
          (HasImp.imp
            (HasImp.imp (HasImp.imp φ HasBot.bot) ψ)
            ψ))) :=
    b_combinator
  have step2 := ModusPonens.mp bc2 peirce_inst
  -- step2: ((¬φ→ψ)→((ψ→⊥)→ψ)) → ((¬φ→ψ)→ψ)

  -- Compose step1 with step2 at (φ→ψ) level:
  -- b: ((¬φ→ψ)→((ψ→⊥)→ψ)) → X → ((¬φ→ψ)→ψ)
  -- But we need to compose step1 and step2 differently:
  -- step1: (φ→ψ) → ((¬φ→ψ) → ((ψ→⊥)→ψ))
  -- step2: ((¬φ→ψ) → ((ψ→⊥)→ψ)) → ((¬φ→ψ)→ψ)
  -- Compose: (φ→ψ) → ((¬φ→ψ)→ψ)
  exact imp_trans step1 step2

/-- Iff introduction: from `⊢ φ → ψ` and `⊢ ψ → φ`,
    derive `⊢ (φ → ψ) ∧ (ψ → φ)`.
    Uses pairing to build the conjunction. -/
theorem iff_intro {φ ψ : F}
    (h1 : InferenceSystem.DerivableIn S
      (HasImp.imp φ ψ))
    (h2 : InferenceSystem.DerivableIn S
      (HasImp.imp ψ φ)) :
    InferenceSystem.DerivableIn S
      (HasImp.imp
        (HasImp.imp (HasImp.imp φ ψ)
          (HasImp.imp (HasImp.imp ψ φ) HasBot.bot))
        HasBot.bot) := by
  have pair_inst := pairing (S := S) (HasImp.imp φ ψ) (HasImp.imp ψ φ)
  have step1 := ModusPonens.mp pair_inst h1
  exact ModusPonens.mp step1 h2

/-- Contrapose iff: from `⊢ φ ↔ ψ`, derive `⊢ ¬φ ↔ ¬ψ`.
    Uses lce_imp/rce_imp to extract directions. -/
theorem contrapose_iff {φ ψ : F}
    (h : InferenceSystem.DerivableIn S
      (HasImp.imp
        (HasImp.imp (HasImp.imp φ ψ)
          (HasImp.imp (HasImp.imp ψ φ) HasBot.bot))
        HasBot.bot)) :
    InferenceSystem.DerivableIn S
      (HasImp.imp
        (HasImp.imp
          (HasImp.imp (HasImp.imp φ HasBot.bot)
            (HasImp.imp ψ HasBot.bot))
          (HasImp.imp
            (HasImp.imp (HasImp.imp ψ HasBot.bot)
              (HasImp.imp φ HasBot.bot))
            HasBot.bot))
        HasBot.bot) := by
  -- Extract φ → ψ
  have ab := ModusPonens.mp lce_imp h
  -- Extract ψ → φ
  have ba := ModusPonens.mp rce_imp h
  -- Contrapose both
  have nb_na := contraposition ab
  have na_nb := contraposition ba
  -- Combine into biconditional
  exact iff_intro na_nb nb_na

/-- Iff neg intro: from `⊢ ¬φ → ¬ψ` and `⊢ ¬ψ → ¬φ`,
    derive `⊢ ¬φ ↔ ¬ψ`. -/
theorem iff_neg_intro {φ ψ : F}
    (h1 : InferenceSystem.DerivableIn S
      (HasImp.imp (HasImp.imp φ HasBot.bot)
        (HasImp.imp ψ HasBot.bot)))
    (h2 : InferenceSystem.DerivableIn S
      (HasImp.imp (HasImp.imp ψ HasBot.bot)
        (HasImp.imp φ HasBot.bot))) :
    InferenceSystem.DerivableIn S
      (HasImp.imp
        (HasImp.imp
          (HasImp.imp (HasImp.imp φ HasBot.bot)
            (HasImp.imp ψ HasBot.bot))
          (HasImp.imp
            (HasImp.imp (HasImp.imp ψ HasBot.bot)
              (HasImp.imp φ HasBot.bot))
            HasBot.bot))
        HasBot.bot) :=
  iff_intro h1 h2

/-- De Morgan 1 forward: `⊢ ¬(φ ∧ ψ) → (¬φ ∨ ¬ψ)`.
    i.e., `¬¬(φ → ¬ψ) → (¬¬φ → ¬ψ)`.
    Use DNE on (φ→¬ψ) then compose with DNE on φ. -/
theorem demorgan_conj_neg_forward {φ ψ : F} :
    InferenceSystem.DerivableIn S
      (HasImp.imp
        (HasImp.imp
          (HasImp.imp
            (HasImp.imp φ (HasImp.imp ψ HasBot.bot))
            HasBot.bot)
          HasBot.bot)
        (HasImp.imp
          (HasImp.imp (HasImp.imp φ HasBot.bot) HasBot.bot)
          (HasImp.imp ψ HasBot.bot))) := by
  -- DNE on (φ→¬ψ): ¬¬(φ→¬ψ) → (φ→¬ψ)
  have dne_inner := @double_negation F _ _ S _ _
    (φ := HasImp.imp φ (HasImp.imp ψ HasBot.bot))
  -- DNE on φ: ¬¬φ → φ
  have dne_a := @double_negation F _ _ S _ _ (φ := φ)
  -- (φ→¬ψ) → (¬¬φ → ¬ψ) by composing with DNE:
  -- b: (φ→¬ψ) → ((¬¬φ→φ) → (¬¬φ→¬ψ))
  -- flip: (¬¬φ→φ) → ((φ→¬ψ) → (¬¬φ→¬ψ))
  -- Apply dne_a: (φ→¬ψ) → (¬¬φ→¬ψ)
  have bc : InferenceSystem.DerivableIn S
      (HasImp.imp
        (HasImp.imp φ (HasImp.imp ψ HasBot.bot))
        (HasImp.imp
          (HasImp.imp
            (HasImp.imp (HasImp.imp φ HasBot.bot)
              HasBot.bot)
            φ)
          (HasImp.imp
            (HasImp.imp (HasImp.imp φ HasBot.bot)
              HasBot.bot)
            (HasImp.imp ψ HasBot.bot)))) :=
    b_combinator
  have flip_bc := ModusPonens.mp
    (@flip F _ _ S _ _
      (HasImp.imp φ (HasImp.imp ψ HasBot.bot))
      (HasImp.imp
        (HasImp.imp (HasImp.imp φ HasBot.bot) HasBot.bot)
        φ)
      (HasImp.imp
        (HasImp.imp (HasImp.imp φ HasBot.bot) HasBot.bot)
        (HasImp.imp ψ HasBot.bot)))
    bc
  have step1 := ModusPonens.mp flip_bc dne_a
  -- step1: (φ→¬ψ) → (¬¬φ → ¬ψ)
  -- Compose with dne_inner: ¬¬(φ→¬ψ) → (¬¬φ→¬ψ)
  exact imp_trans dne_inner step1

/-- De Morgan 1 backward: `⊢ (¬φ ∨ ¬ψ) → ¬(φ ∧ ψ)`. -/
theorem demorgan_conj_neg_backward {φ ψ : F} :
    InferenceSystem.DerivableIn S
      (HasImp.imp
        (HasImp.imp
          (HasImp.imp (HasImp.imp φ HasBot.bot)
            HasBot.bot)
          (HasImp.imp ψ HasBot.bot))
        (HasImp.imp
          (HasImp.imp
            (HasImp.imp φ (HasImp.imp ψ HasBot.bot))
            HasBot.bot)
          HasBot.bot)) := by
  -- Strategy: (¬¬φ→¬ψ) → ¬(φ∧ψ)
  -- We need: (¬¬φ→¬ψ) → ((φ∧ψ) → ⊥)
  -- i.e.: (¬¬φ→¬ψ) → ((φ→(ψ→⊥))→⊥) → ⊥

  -- From (φ∧ψ), extract φ by lce_imp, get ¬¬φ by dni
  -- Then from (¬¬φ→¬ψ), get ¬ψ
  -- From (φ∧ψ), extract ψ by rce_imp
  -- From ψ and ¬ψ, get ⊥

  -- Build: (φ∧ψ) → ¬¬φ  [lce_imp then dni]
  have lce := @lce_imp F _ _ S _ _ (φ := φ) (ψ := ψ)
  have dni_φ := @dni F _ _ S _ _ φ
  have conj_to_nnφ := imp_trans lce dni_φ
  -- conj_to_nnφ: (φ∧ψ) → ¬¬φ

  -- Build: (¬¬φ→¬ψ) → ((φ∧ψ)→¬¬φ) → ((φ∧ψ)→¬ψ)
  have bc1 : InferenceSystem.DerivableIn S
      (HasImp.imp
        (HasImp.imp
          (HasImp.imp (HasImp.imp φ HasBot.bot)
            HasBot.bot)
          (HasImp.imp ψ HasBot.bot))
        (HasImp.imp
          (HasImp.imp
            (HasImp.imp
              (HasImp.imp φ (HasImp.imp ψ HasBot.bot))
              HasBot.bot)
            (HasImp.imp (HasImp.imp φ HasBot.bot)
              HasBot.bot))
          (HasImp.imp
            (HasImp.imp
              (HasImp.imp φ (HasImp.imp ψ HasBot.bot))
              HasBot.bot)
            (HasImp.imp ψ HasBot.bot)))) :=
    b_combinator
  have step1 := ModusPonens.mp
    (@flip F _ _ S _ _
      (HasImp.imp
        (HasImp.imp (HasImp.imp φ HasBot.bot) HasBot.bot)
        (HasImp.imp ψ HasBot.bot))
      (HasImp.imp
        (HasImp.imp
          (HasImp.imp φ (HasImp.imp ψ HasBot.bot))
          HasBot.bot)
        (HasImp.imp (HasImp.imp φ HasBot.bot) HasBot.bot))
      (HasImp.imp
        (HasImp.imp
          (HasImp.imp φ (HasImp.imp ψ HasBot.bot))
          HasBot.bot)
        (HasImp.imp ψ HasBot.bot)))
    bc1
  -- step1: ((φ∧ψ)→¬¬φ) → ((¬¬φ→¬ψ) → ((φ∧ψ)→¬ψ))
  have step2 := ModusPonens.mp step1 conj_to_nnφ
  -- step2: (¬¬φ→¬ψ) → ((φ∧ψ)→¬ψ)

  -- Also: (φ∧ψ) → ψ  [rce_imp]
  have rce := @rce_imp F _ _ S _ _ (φ := φ) (ψ := ψ)
  -- Now: from ((φ∧ψ)→¬ψ) and ((φ∧ψ)→ψ), get ((φ∧ψ)→⊥)
  -- i.e., ¬(φ∧ψ)
  -- app1: ψ → (ψ→⊥) → ⊥  [app1]
  -- b: ((ψ→⊥)→⊥) → ((φ∧ψ)→(ψ→⊥)) → ((φ∧ψ)→⊥)
  -- Hmm, the composition is complex. Let me use combine_imp_conj
  -- pattern:
  -- ImplyS: ((φ∧ψ)→(¬ψ)) → (((φ∧ψ)→ψ)→((φ∧ψ)→⊥))
  -- Wait: ¬ψ = ψ→⊥, so we need:
  -- ((φ∧ψ)→(ψ→⊥)) → (((φ∧ψ)→ψ) → ((φ∧ψ)→⊥))
  -- This is exactly ImplyS!
  have s1 := HasAxiomImplyS.implyS (S := S)
    (φ := HasImp.imp
      (HasImp.imp φ (HasImp.imp ψ HasBot.bot))
      HasBot.bot)
    (ψ := ψ) (χ := HasBot.bot)
  -- s1: ((φ∧ψ)→(ψ→⊥)) → (((φ∧ψ)→ψ)→((φ∧ψ)→⊥))

  -- Compose: (¬¬φ→¬ψ) → step2 → ((φ∧ψ)→¬ψ) →
  --   s1 → (((φ∧ψ)→ψ)→((φ∧ψ)→⊥))
  -- Then apply rce to get ((φ∧ψ)→⊥)
  have step3 := imp_trans step2 s1
  -- step3: (¬¬φ→¬ψ) → ((φ∧ψ)→ψ) → ((φ∧ψ)→⊥)

  -- Weaken rce into scope, then apply
  -- ImplyK: ((φ∧ψ)→ψ) → ((¬¬φ→¬ψ) → ((φ∧ψ)→ψ))
  have k_rce := ModusPonens.mp
    (HasAxiomImplyK.implyK (S := S)
      (φ := HasImp.imp
        (HasImp.imp
          (HasImp.imp φ (HasImp.imp ψ HasBot.bot))
          HasBot.bot)
        ψ)
      (ψ := HasImp.imp
        (HasImp.imp (HasImp.imp φ HasBot.bot) HasBot.bot)
        (HasImp.imp ψ HasBot.bot)))
    rce
  -- k_rce: (¬¬φ→¬ψ) → ((φ∧ψ)→ψ)

  -- ImplyS: ((¬¬φ→¬ψ) → (X→Y)) → (((¬¬φ→¬ψ)→X) → ((¬¬φ→¬ψ)→Y))
  have s2 := HasAxiomImplyS.implyS (S := S)
    (φ := HasImp.imp
      (HasImp.imp (HasImp.imp φ HasBot.bot) HasBot.bot)
      (HasImp.imp ψ HasBot.bot))
    (ψ := HasImp.imp
      (HasImp.imp
        (HasImp.imp φ (HasImp.imp ψ HasBot.bot))
        HasBot.bot)
      ψ)
    (χ := HasImp.imp
      (HasImp.imp
        (HasImp.imp φ (HasImp.imp ψ HasBot.bot))
        HasBot.bot)
      HasBot.bot)
  have step4 := ModusPonens.mp s2 step3
  exact ModusPonens.mp step4 k_rce

/-- De Morgan 1 biconditional:
    `⊢ ¬(φ ∧ ψ) ↔ (¬φ ∨ ¬ψ)`. -/
theorem demorgan_conj_neg {φ ψ : F} :
    InferenceSystem.DerivableIn S
      (HasImp.imp
        (HasImp.imp
          (HasImp.imp
            (HasImp.imp
              (HasImp.imp
                (HasImp.imp φ (HasImp.imp ψ HasBot.bot))
                HasBot.bot)
              HasBot.bot)
            (HasImp.imp
              (HasImp.imp (HasImp.imp φ HasBot.bot)
                HasBot.bot)
              (HasImp.imp ψ HasBot.bot)))
          (HasImp.imp
            (HasImp.imp
              (HasImp.imp
                (HasImp.imp (HasImp.imp φ HasBot.bot)
                  HasBot.bot)
                (HasImp.imp ψ HasBot.bot))
              (HasImp.imp
                (HasImp.imp
                  (HasImp.imp φ (HasImp.imp ψ HasBot.bot))
                  HasBot.bot)
                HasBot.bot))
            HasBot.bot))
        HasBot.bot) :=
  iff_intro demorgan_conj_neg_forward
    demorgan_conj_neg_backward

/-- De Morgan 2 forward: `⊢ ¬(φ ∨ ψ) → (¬φ ∧ ¬ψ)`.
    i.e., `¬((φ→⊥)→ψ) → ¬((φ→⊥)→((ψ→⊥)→⊥)→⊥)`.
    Use DNE on B and contraposition. -/
theorem demorgan_disj_neg_forward {φ ψ : F} :
    InferenceSystem.DerivableIn S
      (HasImp.imp
        (HasImp.imp
          (HasImp.imp (HasImp.imp φ HasBot.bot) ψ)
          HasBot.bot)
        (HasImp.imp
          (HasImp.imp (HasImp.imp φ HasBot.bot)
            (HasImp.imp
              (HasImp.imp ψ HasBot.bot) HasBot.bot))
          HasBot.bot)) := by
  -- (¬φ→¬¬ψ) → (¬φ→ψ) by composing with DNE
  -- Contrapose: ¬(¬φ→ψ) → ¬(¬φ→¬¬ψ)
  have dne_ψ := @double_negation F _ _ S _ _ (φ := ψ)
  -- b: (¬¬ψ→ψ) → ((¬φ→¬¬ψ) → (¬φ→ψ))
  have bc : InferenceSystem.DerivableIn S
      (HasImp.imp
        (HasImp.imp
          (HasImp.imp (HasImp.imp ψ HasBot.bot) HasBot.bot)
          ψ)
        (HasImp.imp
          (HasImp.imp (HasImp.imp φ HasBot.bot)
            (HasImp.imp (HasImp.imp ψ HasBot.bot)
              HasBot.bot))
          (HasImp.imp (HasImp.imp φ HasBot.bot) ψ))) :=
    b_combinator
  have impl := ModusPonens.mp bc dne_ψ
  -- contrapose: ¬(¬φ→ψ) → ¬(¬φ→¬¬ψ)
  exact contraposition impl

/-- De Morgan 2 backward: `⊢ (¬φ ∧ ¬ψ) → ¬(φ ∨ ψ)`.
    i.e., `¬((φ→⊥)→((ψ→⊥)→⊥)→⊥) → ¬((φ→⊥)→ψ)`.
    Use DNI on B and contraposition. -/
theorem demorgan_disj_neg_backward {φ ψ : F} :
    InferenceSystem.DerivableIn S
      (HasImp.imp
        (HasImp.imp
          (HasImp.imp (HasImp.imp φ HasBot.bot)
            (HasImp.imp
              (HasImp.imp ψ HasBot.bot) HasBot.bot))
          HasBot.bot)
        (HasImp.imp
          (HasImp.imp (HasImp.imp φ HasBot.bot) ψ)
          HasBot.bot)) := by
  -- (¬φ→ψ) → (¬φ→¬¬ψ) by composing with DNI
  -- Contrapose: ¬(¬φ→¬¬ψ) → ¬(¬φ→ψ)
  have dni_ψ := @dni F _ _ S _ _ ψ
  -- b: (ψ→¬¬ψ) → ((¬φ→ψ) → (¬φ→¬¬ψ))
  have bc : InferenceSystem.DerivableIn S
      (HasImp.imp
        (HasImp.imp ψ
          (HasImp.imp (HasImp.imp ψ HasBot.bot)
            HasBot.bot))
        (HasImp.imp
          (HasImp.imp (HasImp.imp φ HasBot.bot) ψ)
          (HasImp.imp (HasImp.imp φ HasBot.bot)
            (HasImp.imp (HasImp.imp ψ HasBot.bot)
              HasBot.bot)))) :=
    b_combinator
  have impl := ModusPonens.mp bc dni_ψ
  -- contrapose: ¬(¬φ→¬¬ψ) → ¬(¬φ→ψ)
  exact contraposition impl

/-- De Morgan 2 biconditional:
    `⊢ ¬(φ ∨ ψ) ↔ (¬φ ∧ ¬ψ)`. -/
theorem demorgan_disj_neg {φ ψ : F} :
    InferenceSystem.DerivableIn S
      (HasImp.imp
        (HasImp.imp
          (HasImp.imp
            (HasImp.imp
              (HasImp.imp (HasImp.imp φ HasBot.bot) ψ)
              HasBot.bot)
            (HasImp.imp
              (HasImp.imp (HasImp.imp φ HasBot.bot)
                (HasImp.imp
                  (HasImp.imp ψ HasBot.bot) HasBot.bot))
              HasBot.bot))
          (HasImp.imp
            (HasImp.imp
              (HasImp.imp
                (HasImp.imp (HasImp.imp φ HasBot.bot)
                  (HasImp.imp
                    (HasImp.imp ψ HasBot.bot) HasBot.bot))
                HasBot.bot)
              (HasImp.imp
                (HasImp.imp (HasImp.imp φ HasBot.bot) ψ)
                HasBot.bot))
            HasBot.bot))
        HasBot.bot) :=
  iff_intro demorgan_disj_neg_forward
    demorgan_disj_neg_backward

end Connectives

end Cslib.Logic.Theorems.Propositional.Connectives
