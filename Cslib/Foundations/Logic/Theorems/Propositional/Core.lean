/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/
import Cslib.Foundations.Logic.Theorems.Combinators

/-! # Core Propositional Theorems

Core propositional theorems for the Hilbert-style proof system, including
LEM, double negation elimination, reductio ad absurdum, efq for negation,
reverse contraposition, and conjunction elimination (DT-free proofs).

All theorems are generic over `[PropositionalHilbert S]`.

## Main Results

- `lem`: Law of Excluded Middle (identity on ¬φ)
- `efq_axiom`: EFQ wrapper (⊥ → φ)
- `peirce_axiom`: Peirce's law wrapper
- `double_negation`: DNE derived from EFQ + Peirce + B-combinator
- `raa`: Reductio ad absurdum (φ → (¬φ → ψ))
- `efq_neg`: Ex falso for negation (¬φ → (φ → ψ))
- `rcp`: Reverse contraposition ((¬φ → ¬ψ) → (ψ → φ))
- `lce_imp`: Left conjunction elimination ((φ ∧ ψ) → φ) -- DT-free
- `rce_imp`: Right conjunction elimination ((φ ∧ ψ) → ψ) -- DT-free

## Naming Convention

All negation, conjunction, disjunction use raw `HasImp.imp`/`HasBot.bot`
encoding (Lukasiewicz style):
- `¬φ := φ → ⊥`
- `φ ∧ ψ := (φ → (ψ → ⊥)) → ⊥`
- `φ ∨ ψ := (φ → ⊥) → ψ`
-/

namespace Cslib.Logic.Theorems.Propositional.Core

set_option linter.unreachableTactic false

open Cslib.Logic
open Cslib.Logic.Theorems.Combinators

variable {F : Type*} [HasBot F] [HasImp F]
variable {S : Type*} [InferenceSystem S F]
variable [PropositionalHilbert S (F := F)]

section

-- Abbreviations for readability
-- neg φ = imp φ bot
-- and φ ψ = imp (imp φ (imp ψ bot)) bot
-- or φ ψ = imp (imp φ bot) ψ

/-- EFQ wrapper: `⊢ ⊥ → φ`. -/
theorem efq_axiom {φ : F} :
    InferenceSystem.DerivableIn S
      (HasImp.imp HasBot.bot φ) :=
  HasAxiomEFQ.efq

/-- Peirce's law wrapper: `⊢ ((φ → ψ) → φ) → φ`. -/
theorem peirce_axiom {φ ψ : F} :
    InferenceSystem.DerivableIn S
      (HasImp.imp
        (HasImp.imp (HasImp.imp φ ψ) φ) φ) :=
  HasAxiomPeirce.peirce

/-- Double negation elimination (derived):
    `⊢ ¬¬φ → φ` where `¬φ = φ → ⊥`.

    Proof: Peirce(φ,⊥) gives ((φ→⊥)→φ)→φ.
    EFQ gives ⊥→φ. B-combinator composes
    (⊥→φ) with ((φ→⊥)→⊥) to get ((φ→⊥)→φ).
    Then Peirce gives φ. -/
theorem double_negation {φ : F} :
    InferenceSystem.DerivableIn S
      (HasImp.imp
        (HasImp.imp (HasImp.imp φ HasBot.bot) HasBot.bot)
        φ) := by
  -- Peirce with ψ = ⊥: ((φ→⊥)→φ) → φ
  have peirce_inst := HasAxiomPeirce.peirce (S := S)
    (φ := φ) (ψ := HasBot.bot)
  -- EFQ: ⊥ → φ
  have efq_inst := HasAxiomEFQ.efq (S := S) (φ := φ)
  -- B-combinator: (⊥→φ) → ((φ→⊥)→⊥) → ((φ→⊥)→φ)
  have b_inst : InferenceSystem.DerivableIn S
      (HasImp.imp (HasImp.imp HasBot.bot φ)
        (HasImp.imp
          (HasImp.imp (HasImp.imp φ HasBot.bot) HasBot.bot)
          (HasImp.imp (HasImp.imp φ HasBot.bot) φ))) :=
    b_combinator
  -- MP: ((φ→⊥)→⊥) → ((φ→⊥)→φ)
  have step1 := ModusPonens.mp b_inst efq_inst
  -- B-combinator to compose with Peirce
  have b_final : InferenceSystem.DerivableIn S
      (HasImp.imp
        (HasImp.imp (HasImp.imp (HasImp.imp φ HasBot.bot) φ) φ)
        (HasImp.imp
          (HasImp.imp
            (HasImp.imp (HasImp.imp φ HasBot.bot) HasBot.bot)
            (HasImp.imp (HasImp.imp φ HasBot.bot) φ))
          (HasImp.imp
            (HasImp.imp (HasImp.imp φ HasBot.bot) HasBot.bot)
            φ))) :=
    b_combinator
  have step2 := ModusPonens.mp b_final peirce_inst
  exact ModusPonens.mp step2 step1

/-- Reductio ad absurdum: `⊢ φ → (¬φ → ψ)`
    where `¬φ = φ → ⊥`. -/
theorem raa {φ ψ : F} :
    InferenceSystem.DerivableIn S
      (HasImp.imp φ
        (HasImp.imp (HasImp.imp φ HasBot.bot) ψ)) := by
  -- EFQ: ⊥ → ψ
  have efq_inst := HasAxiomEFQ.efq (S := S) (φ := ψ)
  -- DNI: φ → ¬¬φ = φ → (φ→⊥) → ⊥
  have dni_inst := dni (S := S) φ
  -- B: (⊥→ψ) → ((φ→⊥)→⊥) → ((φ→⊥)→ψ)
  have b_inner : InferenceSystem.DerivableIn S
      (HasImp.imp (HasImp.imp HasBot.bot ψ)
        (HasImp.imp
          (HasImp.imp (HasImp.imp φ HasBot.bot) HasBot.bot)
          (HasImp.imp (HasImp.imp φ HasBot.bot) ψ))) :=
    b_combinator
  have step1 := ModusPonens.mp b_inner efq_inst
  -- B: (¬¬φ→(¬φ→ψ)) → (φ→¬¬φ) → (φ→(¬φ→ψ))
  have b_outer : InferenceSystem.DerivableIn S
      (HasImp.imp
        (HasImp.imp
          (HasImp.imp (HasImp.imp φ HasBot.bot) HasBot.bot)
          (HasImp.imp (HasImp.imp φ HasBot.bot) ψ))
        (HasImp.imp
          (HasImp.imp φ
            (HasImp.imp (HasImp.imp φ HasBot.bot) HasBot.bot))
          (HasImp.imp φ
            (HasImp.imp (HasImp.imp φ HasBot.bot) ψ)))) :=
    b_combinator
  have step2 := ModusPonens.mp b_outer step1
  exact ModusPonens.mp step2 dni_inst

/-- Ex falso for negation: `⊢ ¬φ → (φ → ψ)`.
    Flip of RAA. -/
theorem efq_neg {φ ψ : F} :
    InferenceSystem.DerivableIn S
      (HasImp.imp (HasImp.imp φ HasBot.bot)
        (HasImp.imp φ ψ)) := by
  have raa_inst := @raa F _ _ S _ _ (φ := φ) (ψ := ψ)
  have flip_inst : InferenceSystem.DerivableIn S
      (HasImp.imp
        (HasImp.imp φ
          (HasImp.imp (HasImp.imp φ HasBot.bot) ψ))
        (HasImp.imp (HasImp.imp φ HasBot.bot)
          (HasImp.imp φ ψ))) :=
    @theorem_flip F _ _ S _ _
      φ (HasImp.imp φ HasBot.bot) ψ
  exact ModusPonens.mp flip_inst raa_inst

/-- Reverse contraposition: from `⊢ ¬φ → ¬ψ`,
    derive `⊢ ψ → φ`.
    Chain: ψ → ¬¬ψ → ¬¬φ → φ. -/
theorem rcp {φ ψ : F}
    (h : InferenceSystem.DerivableIn S
      (HasImp.imp (HasImp.imp φ HasBot.bot)
        (HasImp.imp ψ HasBot.bot))) :
    InferenceSystem.DerivableIn S
      (HasImp.imp ψ φ) := by
  -- DNI for ψ: ψ → ¬¬ψ
  have dni_b := dni (S := S) ψ
  -- Contrapose h to get ¬¬ψ → ¬¬φ
  -- b: (¬ψ→⊥) → ((¬φ→¬ψ) → (¬φ→⊥))
  have bc : InferenceSystem.DerivableIn S
      (HasImp.imp
        (HasImp.imp (HasImp.imp ψ HasBot.bot)
          HasBot.bot)
        (HasImp.imp
          (HasImp.imp (HasImp.imp φ HasBot.bot)
            (HasImp.imp ψ HasBot.bot))
          (HasImp.imp (HasImp.imp φ HasBot.bot)
            HasBot.bot))) :=
    b_combinator
  -- Flip: (¬φ→¬ψ) → (¬¬ψ → ¬¬φ)
  have flip_bc := ModusPonens.mp
    (@theorem_flip F _ _ S _ _
      (HasImp.imp (HasImp.imp ψ HasBot.bot) HasBot.bot)
      (HasImp.imp (HasImp.imp φ HasBot.bot)
        (HasImp.imp ψ HasBot.bot))
      (HasImp.imp (HasImp.imp φ HasBot.bot) HasBot.bot))
    bc
  -- ¬¬ψ → ¬¬φ
  have contraposed := ModusPonens.mp flip_bc h
  -- ψ → ¬¬ψ → ¬¬φ
  have b_to_nna := imp_trans dni_b contraposed
  -- DNE for φ: ¬¬φ → φ
  have dne_a := @double_negation F _ _ S _ _ (φ := φ)
  -- ψ → ¬¬φ → φ
  exact imp_trans b_to_nna dne_a

/-- Left conjunction elimination (DT-free):
    `⊢ (φ ∧ ψ) → φ` where `φ ∧ ψ = (φ→(ψ→⊥))→⊥`.

    Proof: By Peirce with ψ₀ = ψ→⊥:
    ((φ→(ψ→⊥))→φ)→φ.
    From efq_neg: ¬(φ→(ψ→⊥)) → ((φ→(ψ→⊥)) → φ).
    Compose with Peirce to get ¬(φ→(ψ→⊥)) → φ. -/
theorem lce_imp {φ ψ : F} :
    InferenceSystem.DerivableIn S
      (HasImp.imp
        (HasImp.imp
          (HasImp.imp φ (HasImp.imp ψ HasBot.bot))
          HasBot.bot)
        φ) := by
  -- Peirce with ψ₀ = (ψ→⊥): ((φ→(ψ→⊥))→φ)→φ
  have peirce_inst := HasAxiomPeirce.peirce (S := S)
    (φ := φ) (ψ := HasImp.imp ψ HasBot.bot)
  -- efq_neg at (φ→(ψ→⊥)): ¬(φ→(ψ→⊥)) → ((φ→(ψ→⊥)) → φ)
  -- i.e., ((φ→(ψ→⊥))→⊥) → ((φ→(ψ→⊥)) → φ)
  have efq_inst := @efq_neg F _ _ S _ _
    (φ := HasImp.imp φ (HasImp.imp ψ HasBot.bot))
    (ψ := φ)
  -- Compose with Peirce via imp_trans
  exact imp_trans efq_inst peirce_inst

/-- Right conjunction elimination (DT-free):
    `⊢ (φ ∧ ψ) → ψ` where `φ ∧ ψ = (φ→(ψ→⊥))→⊥`.

    Proof: By Peirce with ψ₀ = ⊥: ((ψ→⊥)→ψ)→ψ.
    We need ¬(φ→(ψ→⊥)) → ((ψ→⊥)→ψ).
    From ¬(φ→(ψ→⊥)) and (ψ→⊥), derive ⊥ and then ψ.
    Use ImplyK to weaken: (ψ→⊥) → (φ→(ψ→⊥)).
    Then compose. -/
theorem rce_imp {φ ψ : F} :
    InferenceSystem.DerivableIn S
      (HasImp.imp
        (HasImp.imp
          (HasImp.imp φ (HasImp.imp ψ HasBot.bot))
          HasBot.bot)
        ψ) := by
  -- Peirce(ψ,⊥): ((ψ→⊥)→ψ)→ψ
  have peirce_inst := HasAxiomPeirce.peirce (S := S)
    (φ := ψ) (ψ := HasBot.bot)
  -- efq_neg: ¬(φ→(ψ→⊥)) → ((φ→(ψ→⊥)) → ψ)
  have efq_inst := @efq_neg F _ _ S _ _
    (φ := HasImp.imp φ (HasImp.imp ψ HasBot.bot))
    (ψ := ψ)
  -- ImplyK: (ψ→⊥) → (φ→(ψ→⊥))
  have k_inst := HasAxiomImplyK.implyK (S := S)
    (φ := HasImp.imp ψ HasBot.bot) (ψ := φ)
  -- b: ((φ→(ψ→⊥))→ψ) → ((ψ→⊥)→(φ→(ψ→⊥))) → ((ψ→⊥)→ψ)
  have bc2 : InferenceSystem.DerivableIn S
      (HasImp.imp
        (HasImp.imp
          (HasImp.imp φ (HasImp.imp ψ HasBot.bot)) ψ)
        (HasImp.imp
          (HasImp.imp (HasImp.imp ψ HasBot.bot)
            (HasImp.imp φ (HasImp.imp ψ HasBot.bot)))
          (HasImp.imp (HasImp.imp ψ HasBot.bot) ψ))) :=
    b_combinator
  -- flip: K → ((φ→(ψ→⊥))→ψ) → ((ψ→⊥)→ψ)
  have flip_bc2 := ModusPonens.mp
    (@theorem_flip F _ _ S _ _
      (HasImp.imp
        (HasImp.imp φ (HasImp.imp ψ HasBot.bot)) ψ)
      (HasImp.imp (HasImp.imp ψ HasBot.bot)
        (HasImp.imp φ (HasImp.imp ψ HasBot.bot)))
      (HasImp.imp (HasImp.imp ψ HasBot.bot) ψ))
    bc2
  -- ((φ→(ψ→⊥))→ψ) → ((ψ→⊥)→ψ)
  have step1 := ModusPonens.mp flip_bc2 k_inst
  -- ¬(φ→(ψ→⊥)) → ((ψ→⊥)→ψ)
  have step2 := imp_trans efq_inst step1
  -- ¬(φ→(ψ→⊥)) → ψ
  exact imp_trans step2 peirce_inst

/-- Law of Excluded Middle: `⊢ φ ∨ ¬φ`
    where `φ ∨ ¬φ = (φ → ⊥) → (φ → ⊥)`. -/
theorem lem {φ : F} :
    InferenceSystem.DerivableIn S
      (HasImp.imp (HasImp.imp φ HasBot.bot)
        (HasImp.imp φ HasBot.bot)) :=
  identity (HasImp.imp φ HasBot.bot)

end -- section

end Cslib.Logic.Theorems.Propositional.Core
