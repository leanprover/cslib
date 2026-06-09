/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/
import Cslib.Foundations.Logic.Theorems.Propositional.Connectives

/-! # Reasoning Theorems

Biconditional introduction in implication form.

## Main Results

- `bi_imp`: `⊢ (φ → ψ) → ((ψ → φ) → (φ ↔ ψ))`
-/

namespace Cslib.Logic.Theorems.Propositional.Reasoning

set_option linter.style.longLine false

open Cslib.Logic
open Cslib.Logic.Theorems.Combinators

variable {F : Type*} [HasBot F] [HasImp F]
variable {S : Type*} [InferenceSystem S F]
variable [PropositionalHilbert S (F := F)]

noncomputable section

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

end -- noncomputable section

end Cslib.Logic.Theorems.Propositional.Reasoning
