/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/
import Cslib.Logics.Bimodal.ProofSystem.Instances
import Cslib.Foundations.Logic.Theorems.Propositional.Connectives

/-! # Perpetuity Helper Lemmas

This module contains helper lemmas for proving the perpetuity principles (P1-P6).
These helpers derive each temporal component of the always operator from box:
- `box_to_future`: `⊢ □φ → Gφ` (MF + MT)
- `box_to_past`: `⊢ □φ → Hφ` (temporal duality on MF)
- `box_to_present`: `⊢ □φ → φ` (MT axiom)
- `temp_future_derived`: `⊢ □φ → G(□φ)` (M4 + MF + MT)

## References

* Ported from BimodalLogic/Theories/Bimodal/Theorems/Perpetuity/Helpers.lean
-/

set_option linter.style.longLine false

-- Do not open Cslib.Logic.Bimodal to avoid scoped notation conflicts
-- (F, G, H, P are prefix notation for temporal operators)

namespace Cslib.Logic.Bimodal.Theorems.Perpetuity

open Cslib.Logic

variable {Atom : Type u}

-- Local notation for derivability at Base frame class
local notation:50 "⊢ " phi =>
  Bimodal.DerivationTree Bimodal.FrameClass.Base ([] : List (Bimodal.Formula Atom)) phi

-- Context derivability notation
local notation:50 Gamma " ⊢ " phi =>
  Bimodal.DerivationTree Bimodal.FrameClass.Base Gamma phi

/-! ## Typeclass Bridge

The InferenceSystem instance maps `HilbertTM=>φ` to `DerivationTree .Base [] φ`.
Since `InferenceSystem.DerivableIn HilbertTM φ = Nonempty (DerivationTree .Base [] φ)`,
we can convert freely between the two representations.
-/

noncomputable section

/-- Convert a derivation tree to a Nonempty (for typeclass functions). -/
def wrap {φ : Bimodal.Formula Atom}
    (d : ⊢ φ) : InferenceSystem.DerivableIn Bimodal.HilbertTM φ := ⟨d⟩

/-- Extract a derivation tree from Nonempty (from typeclass functions). -/
def unwrap {φ : Bimodal.Formula Atom}
    (h : InferenceSystem.DerivableIn Bimodal.HilbertTM φ) : ⊢ φ := h.some

/-- Transitivity: from `⊢ φ → ψ` and `⊢ ψ → χ`, derive `⊢ φ → χ`. -/
def imp_trans {φ ψ χ : Bimodal.Formula Atom}
    (h1 : ⊢ φ.imp ψ) (h2 : ⊢ ψ.imp χ) : ⊢ φ.imp χ :=
  unwrap (Theorems.Combinators.imp_trans (wrap h1) (wrap h2))

/-- Identity: `⊢ φ → φ`. -/
def identity (φ : Bimodal.Formula Atom) : ⊢ φ.imp φ :=
  unwrap (@Theorems.Combinators.identity _ _ _ Bimodal.HilbertTM _ _ φ)

/-- Combine three implications into conjunction. -/
def combine_imp_conj_3 {φ₀ φ₁ φ₂ φ₃ : Bimodal.Formula Atom}
    (h1 : ⊢ φ₀.imp φ₁) (h2 : ⊢ φ₀.imp φ₂) (h3 : ⊢ φ₀.imp φ₃) :
    ⊢ φ₀.imp (φ₁.and (φ₂.and φ₃)) :=
  unwrap (Theorems.Combinators.combine_imp_conj_3 (wrap h1) (wrap h2) (wrap h3))

/-- Combine two implications into conjunction. -/
def combine_imp_conj {φ₀ φ₁ φ₂ : Bimodal.Formula Atom}
    (h1 : ⊢ φ₀.imp φ₁) (h2 : ⊢ φ₀.imp φ₂) :
    ⊢ φ₀.imp (φ₁.and φ₂) :=
  unwrap (Theorems.Combinators.combine_imp_conj (wrap h1) (wrap h2))

/-- DNI: `⊢ φ → ¬¬φ`. -/
def dni (φ : Bimodal.Formula Atom) : ⊢ φ.imp φ.neg.neg :=
  unwrap (@Theorems.Combinators.dni _ _ _ Bimodal.HilbertTM _ _ φ)

/-- Contraposition: from `⊢ φ → ψ`, derive `⊢ ¬ψ → ¬φ`. -/
def contraposition {φ ψ : Bimodal.Formula Atom}
    (h : ⊢ φ.imp ψ) : ⊢ ψ.neg.imp φ.neg :=
  unwrap (Theorems.Propositional.Connectives.contraposition (wrap h))

/-- Double negation elimination: `⊢ ¬¬φ → φ`. -/
def double_negation (φ : Bimodal.Formula Atom) : ⊢ φ.neg.neg.imp φ :=
  unwrap (@Theorems.Propositional.Core.double_negation _ _ _ Bimodal.HilbertTM _ _ (φ := φ))

/-- Left conjunction elimination: `⊢ (φ₁ ∧ φ₂) → φ₁`. -/
def lce_imp (φ₁ φ₂ : Bimodal.Formula Atom) : ⊢ (φ₁.and φ₂).imp φ₁ :=
  unwrap (@Theorems.Propositional.Core.lce_imp _ _ _ Bimodal.HilbertTM _ _ (φ := φ₁) (ψ := φ₂))

/-- Right conjunction elimination: `⊢ (φ₁ ∧ φ₂) → φ₂`. -/
def rce_imp (φ₁ φ₂ : Bimodal.Formula Atom) : ⊢ (φ₁.and φ₂).imp φ₂ :=
  unwrap (@Theorems.Propositional.Core.rce_imp _ _ _ Bimodal.HilbertTM _ _ (φ := φ₁) (ψ := φ₂))

/-! ## Helper Lemmas: Temporal Components -/

/-- Box implies future: `⊢ □φ → Gφ`. MF + MT composed. -/
def box_to_future (φ : Bimodal.Formula Atom) : ⊢ φ.box.imp φ.allFuture :=
  imp_trans
    (Bimodal.DerivationTree.axiom [] _ (Bimodal.Axiom.modal_future φ) trivial)
    (Bimodal.DerivationTree.axiom [] _ (Bimodal.Axiom.modal_t φ.allFuture) trivial)

/-- Box implies past: `⊢ □φ → Hφ`. Via temporal duality on box_to_future. -/
def box_to_past (φ : Bimodal.Formula Atom) : ⊢ φ.box.imp φ.allPast := by
  have h1 := box_to_future φ.swapTemporal
  have h2 := Bimodal.DerivationTree.temporal_duality _ h1
  simp only [Bimodal.Formula.swapTemporal, Bimodal.Formula.swapTemporal_involution] at h2
  exact h2

/-- Box implies present: `⊢ □φ → φ` (MT axiom). -/
def box_to_present (φ : Bimodal.Formula Atom) : ⊢ φ.box.imp φ :=
  Bimodal.DerivationTree.axiom [] _ (Bimodal.Axiom.modal_t φ) trivial

/-- `temp_future_derived`: `⊢ □φ → G(□φ)`. M4 + MF + MT composed. -/
def temp_future_derived (φ : Bimodal.Formula Atom) : ⊢ φ.box.imp φ.box.allFuture :=
  imp_trans
    (imp_trans
      (Bimodal.DerivationTree.axiom [] _ (Bimodal.Axiom.modal_4 φ) trivial)
      (Bimodal.DerivationTree.axiom [] _ (Bimodal.Axiom.modal_future φ.box) trivial))
    (Bimodal.DerivationTree.axiom [] _ (Bimodal.Axiom.modal_t φ.box.allFuture) trivial)

end -- noncomputable section

end Cslib.Logic.Bimodal.Theorems.Perpetuity
