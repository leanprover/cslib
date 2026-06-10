/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/
import Cslib.Foundations.Logic.Theorems.Propositional.Connectives

/-! # Reasoning Theorems

Biconditional introduction in implication form.

## Main Results

- `bi_imp`: `⊢ (φ → ψ) → ((ψ → φ) → (φ ↔ ψ))`
-/

namespace Cslib.Logic.Theorems.Propositional.Reasoning

open Cslib.Logic
open Cslib.Logic.Theorems.Combinators

variable {F : Type*} [HasBot F] [HasImp F]
variable {S : Type*} [InferenceSystem S F]
variable [PropositionalHilbert S (F := F)]

section

/-- Biconditional introduction (implication form):
    `⊢ (φ → ψ) → ((ψ → φ) → (φ ↔ ψ))`
    where `φ ↔ ψ = (φ → ψ) ∧ (ψ → φ)`. -/
theorem bi_imp {φ ψ : F} :
    InferenceSystem.DerivableIn S
      (HasImp.imp (HasImp.imp φ ψ)
        (HasImp.imp (HasImp.imp ψ φ)
          (HasImp.imp
            (HasImp.imp (HasImp.imp φ ψ)
              (HasImp.imp (HasImp.imp ψ φ) HasBot.bot))
            HasBot.bot))) :=
  pairing (S := S) (HasImp.imp φ ψ) (HasImp.imp ψ φ)

end -- section

end Cslib.Logic.Theorems.Propositional.Reasoning
