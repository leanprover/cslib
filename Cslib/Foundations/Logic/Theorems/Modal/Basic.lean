/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Foundations.Logic.ProofSystem
public import Cslib.Foundations.Logic.Theorems.Combinators
public import Cslib.Foundations.Logic.Theorems.Propositional.Core
public import Cslib.Foundations.Logic.Theorems.Propositional.Connectives

/-! # K-Level Modal Theorems

This module defines modal theorems that are derivable in any proof system
satisfying `[ModalHilbert S]`, i.e., using only the K distribution axiom
and necessitation rule (plus propositional axioms).

All theorems are generic over `[ModalHilbert S]` with formula type `F`
carrying `HasBot`, `HasImp`, and `HasBox` instances.

## Main Results

- `box_mono`: Box monotonicity (meta-rule): from `⊢ φ → ψ`, derive `⊢ □φ → □ψ`
- `diamond_mono`: Diamond monotonicity (meta-rule): from `⊢ φ → ψ`, derive `⊢ ◇φ → ◇ψ`
- `box_contrapose`: `⊢ □(φ → ψ) → □(¬ψ → ¬φ)` (box preserves contraposition)
- `k_dist_diamond`: `⊢ □(φ → ψ) → (◇φ → ◇ψ)` (K distribution for diamond)
- `modal_duality_neg`: `⊢ ◇¬φ → ¬□φ` (modal duality forward)
- `modal_duality_neg_rev`: `⊢ ¬□φ → ◇¬φ` (modal duality reverse)
- `box_iff_intro`: From `⊢ φ ↔ ψ`, derive `⊢ □φ ↔ □ψ`

## Encoding

- `¬φ = φ → ⊥`
- `◇φ = ¬□¬φ = (□(φ → ⊥)) → ⊥`
- `φ ∧ ψ = (φ → (ψ → ⊥)) → ⊥`
- `φ ↔ ψ = (φ → ψ) ∧ (ψ → φ)`
-/

@[expose] public section

namespace Cslib.Logic.Theorems.Modal.Basic

set_option linter.unreachableTactic false

open Cslib.Logic
open Cslib.Logic.Theorems.Combinators
open Cslib.Logic.Theorems.Propositional.Core
open Cslib.Logic.Theorems.Propositional.Connectives

variable {F : Type*} [HasBot F] [HasImp F] [HasBox F]
variable {S : Type*} [InferenceSystem S F]
variable [ModalHilbert S (F := F)]

section

/-- Box monotonicity (meta-rule): from `⊢ φ → ψ`, derive `⊢ □φ → □ψ`.

Uses necessitation to box the implication, then K axiom to distribute. -/
theorem box_mono {φ ψ : F}
    (h : InferenceSystem.DerivableIn S (HasImp.imp φ ψ)) :
    InferenceSystem.DerivableIn S (HasImp.imp (HasBox.box φ) (HasBox.box ψ)) := by
  have box_h := Necessitation.nec h
  have mk := HasAxiomK.K (S := S) (φ := φ) (ψ := ψ)
  exact ModusPonens.mp mk box_h

/-- Diamond monotonicity (meta-rule): from `⊢ φ → ψ`, derive `⊢ ◇φ → ◇ψ`.

Derived via contraposition of box_mono applied to the negated implication.
Since ◇φ = ¬□¬φ, from φ → ψ we get ¬ψ → ¬φ (contraposition),
then □¬ψ → □¬φ (box_mono), then ¬□¬φ → ¬□¬ψ (contraposition again). -/
theorem diamond_mono {φ ψ : F}
    (h : InferenceSystem.DerivableIn S (HasImp.imp φ ψ)) :
    InferenceSystem.DerivableIn S
      (HasImp.imp
        (HasImp.imp (HasBox.box (HasImp.imp φ HasBot.bot)) HasBot.bot)
        (HasImp.imp (HasBox.box (HasImp.imp ψ HasBot.bot)) HasBot.bot)) := by
  have contra : InferenceSystem.DerivableIn S
      (HasImp.imp (HasImp.imp ψ HasBot.bot) (HasImp.imp φ HasBot.bot)) :=
    contraposition h
  have box_contra : InferenceSystem.DerivableIn S
      (HasImp.imp (HasBox.box (HasImp.imp ψ HasBot.bot)) (HasBox.box (HasImp.imp φ HasBot.bot))) :=
    box_mono contra
  exact contraposition box_contra

/-- Box preserves contraposition: `⊢ □(φ → ψ) → □(¬ψ → ¬φ)`.

Uses box_mono on the contrapose_imp theorem. -/
theorem box_contrapose {φ ψ : F} :
    InferenceSystem.DerivableIn S
      (HasImp.imp
        (HasBox.box (HasImp.imp φ ψ))
        (HasBox.box (HasImp.imp (HasImp.imp ψ HasBot.bot) (HasImp.imp φ HasBot.bot)))) := by
  -- contrapose_imp: (φ → ψ) → (¬ψ → ¬φ)
  have contra_thm : InferenceSystem.DerivableIn S
      (HasImp.imp (HasImp.imp φ ψ)
        (HasImp.imp (HasImp.imp ψ HasBot.bot)
          (HasImp.imp φ HasBot.bot))) :=
    contrapose_imp
  exact box_mono contra_thm

/-- K distribution for diamond: `⊢ □(φ → ψ) → (◇φ → ◇ψ)`.

This is the valid form of "diamond monotonicity as implication".
Note: `(φ → ψ) → (◇φ → ◇ψ)` is NOT valid; the implication must be boxed.

Proof:
1. box_contrapose: □(φ → ψ) → □(¬ψ → ¬φ)
2. K axiom: □(¬ψ → ¬φ) → (□¬ψ → □¬φ)
3. Compose: □(φ → ψ) → (□¬ψ → □¬φ)
4. contrapose_imp on consequent: (□¬ψ → □¬φ) → (¬□¬φ → ¬□¬ψ)
5. Compose: □(φ → ψ) → (◇φ → ◇ψ) -/
theorem k_dist_diamond {φ ψ : F} :
    InferenceSystem.DerivableIn S
      (HasImp.imp
        (HasBox.box (HasImp.imp φ ψ))
        (HasImp.imp
          (HasImp.imp (HasBox.box (HasImp.imp φ HasBot.bot)) HasBot.bot)
          (HasImp.imp (HasBox.box (HasImp.imp ψ HasBot.bot)) HasBot.bot))) := by
  -- Step 1: box_contrapose: □(φ → ψ) → □(¬ψ → ¬φ)
  have box_contra := @box_contrapose F _ _ _ S _ _ (φ := φ) (ψ := ψ)
  -- K axiom: □(¬ψ → ¬φ) → (□¬ψ → □¬φ)
  have k_inst := HasAxiomK.K (S := S)
    (φ := HasImp.imp ψ HasBot.bot)
    (ψ := HasImp.imp φ HasBot.bot)
  -- Compose: □(φ → ψ) → (□¬ψ → □¬φ)
  have step1 := imp_trans box_contra k_inst
  -- contrapose_imp: (□¬ψ → □¬φ) → (¬□¬φ → ¬□¬ψ)
  have contra_cons : InferenceSystem.DerivableIn S
      (HasImp.imp
        (HasImp.imp (HasBox.box (HasImp.imp ψ HasBot.bot)) (HasBox.box (HasImp.imp φ HasBot.bot)))
        (HasImp.imp
          (HasImp.imp (HasBox.box (HasImp.imp φ HasBot.bot)) HasBot.bot)
          (HasImp.imp (HasBox.box (HasImp.imp ψ HasBot.bot)) HasBot.bot))) :=
    contrapose_imp
  -- Compose: □(φ → ψ) → (◇φ → ◇ψ)
  exact imp_trans step1 contra_cons

/-- Modal duality (forward): `⊢ ◇¬φ → ¬□φ`.

Since ◇¬φ = ¬□¬¬φ, we need ¬□¬¬φ → ¬□φ.
From DNI (φ → ¬¬φ), apply box_mono (□φ → □¬¬φ),
then contrapose (¬□¬¬φ → ¬□φ). -/
theorem modal_duality_neg {φ : F} :
    InferenceSystem.DerivableIn S
      (HasImp.imp
        (HasImp.imp
          (HasBox.box (HasImp.imp (HasImp.imp φ HasBot.bot) HasBot.bot))
          HasBot.bot)
        (HasImp.imp (HasBox.box φ) HasBot.bot)) := by
  -- DNI: φ → ¬¬φ
  have dni_phi := dni (S := S) φ
  -- box_mono: □φ → □¬¬φ
  have forward := box_mono dni_phi
  -- contrapose: ¬□¬¬φ → ¬□φ
  exact contraposition forward

/-- Modal duality (reverse): `⊢ ¬□φ → ◇¬φ`.

Since ◇¬φ = ¬□¬¬φ, we need ¬□φ → ¬□¬¬φ.
From DNE (¬¬φ → φ), apply box_mono (□¬¬φ → □φ),
then contrapose (¬□φ → ¬□¬¬φ). -/
theorem modal_duality_neg_rev {φ : F} :
    InferenceSystem.DerivableIn S
      (HasImp.imp
        (HasImp.imp (HasBox.box φ) HasBot.bot)
        (HasImp.imp
          (HasBox.box (HasImp.imp (HasImp.imp φ HasBot.bot) HasBot.bot))
          HasBot.bot)) := by
  -- DNE: ¬¬φ → φ
  have dne_phi := @double_negation F _ _ S _ _ (φ := φ)
  -- box_mono: □¬¬φ → □φ
  have forward := box_mono dne_phi
  -- contrapose: ¬□φ → ¬□¬¬φ
  exact contraposition forward

/-- Box preserves biconditionals: from `⊢ φ ↔ ψ`, derive `⊢ □φ ↔ □ψ`.

Extracts both directions using lce_imp and rce_imp, applies box_mono
to each, then combines with iff_intro. -/
theorem box_iff_intro {φ ψ : F}
    (h : InferenceSystem.DerivableIn S
      (HasImp.imp
        (HasImp.imp (HasImp.imp φ ψ)
          (HasImp.imp (HasImp.imp ψ φ) HasBot.bot))
        HasBot.bot)) :
    InferenceSystem.DerivableIn S
      (HasImp.imp
        (HasImp.imp (HasImp.imp (HasBox.box φ) (HasBox.box ψ))
          (HasImp.imp (HasImp.imp (HasBox.box ψ) (HasBox.box φ)) HasBot.bot))
        HasBot.bot) := by
  -- Extract φ → ψ from biconditional
  have ab := ModusPonens.mp lce_imp h
  -- Extract ψ → φ from biconditional
  have ba := ModusPonens.mp rce_imp h
  -- Apply box_mono to both directions
  have box_ab := box_mono ab
  have box_ba := box_mono ba
  -- Combine into biconditional
  exact iff_intro box_ab box_ba

end -- section

end Cslib.Logic.Theorems.Modal.Basic
