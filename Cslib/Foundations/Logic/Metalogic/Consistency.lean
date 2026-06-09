/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/

import Mathlib.Order.Zorn
import Cslib.Foundations.Logic.Connectives

/-! # Generic Maximal Consistent Set (MCS) Foundations

This module provides a generic framework for maximal consistent set (MCS) theory,
parameterized over an abstract derivation relation. The key components are:

- `DerivationSystem`: A structure bundling a context-based derivability predicate with
  weakening, assumption, and modus ponens properties.
- `SetConsistent`, `SetMaximalConsistent`: Set-based consistency predicates.
- `consistent_chain_union`: Chain unions preserve set-consistency (input to Zorn's lemma).
- `set_lindenbaum`: Lindenbaum's lemma -- every consistent set extends to a maximally
  consistent set (via Zorn's lemma).
- `HasDeductionTheorem`: A separate hypothesis type for the deduction theorem.
- Closure properties (`closed_under_derivation`, `implication_property`,
  `negation_complete`) conditional on the deduction theorem.

Downstream modal (task 30) and temporal (task 31) metalogic tasks instantiate
`DerivationSystem` from their concrete `DerivationTree` types and supply deduction
theorem proofs.
-/

open Cslib.Logic

namespace Cslib.Logic.Metalogic

variable {F : Type*} [HasBot F] [HasImp F]

/-- A derivation system abstracts over logic-specific proof systems.

`F` is the formula type with bottom and implication.
`Deriv` maps a context (list of assumptions) and a conclusion to a `Prop`.

Required properties:
- `weakening`: derivations can be extended with additional assumptions
- `assumption`: any formula in the context is derivable from it
- `mp`: modus ponens is admissible -/
structure DerivationSystem (F : Type*) [HasBot F] [HasImp F] where
  /-- Context-based derivability: `Deriv Γ φ` means `φ` is derivable from `Γ`. -/
  Deriv : List F → F → Prop
  /-- Weakening: if `Γ ⊢ φ` and `Γ ⊆ Δ`, then `Δ ⊢ φ`. -/
  weakening : ∀ {Γ Δ : List F} {φ : F}, Deriv Γ φ → (∀ x ∈ Γ, x ∈ Δ) → Deriv Δ φ
  /-- Assumption: if `φ ∈ Γ`, then `Γ ⊢ φ`. -/
  assumption : ∀ {Γ : List F} {φ : F}, φ ∈ Γ → Deriv Γ φ
  /-- Modus ponens: from `Γ ⊢ φ → ψ` and `Γ ⊢ φ`, derive `Γ ⊢ ψ`. -/
  mp : ∀ {Γ : List F} {φ ψ : F}, Deriv Γ (HasImp.imp φ ψ) → Deriv Γ φ → Deriv Γ ψ

end Cslib.Logic.Metalogic
