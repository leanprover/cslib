/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/

import Cslib.Logics.Bimodal.ProofSystem.Derivation
import Cslib.Foundations.Logic.Metalogic.Consistency

/-! # DerivationTree — Deriv and DerivationSystem for Bimodal Logic

This module provides:

- `Bimodal.Deriv`: A `Prop`-level wrapper (`Nonempty (DerivationTree ...)`).
- `Bimodal.ThDerivable`: Derivability from the empty context at `FrameClass.Base`.
- Helper combinators: `mp_deriv`, `weakening_deriv`, `assumption_deriv`.
- `bimodalDerivationSystem`: A `DerivationSystem (Formula Atom)` instance connecting
  to the generic MCS framework from `Consistency.lean`.

## Design

The existing `DerivationTree` in `ProofSystem/Derivation.lean` is a `Type` (not `Prop`),
enabling pattern matching. This module adds the `Prop` wrappers needed by the generic MCS
framework. Height lemmas are already in `Derivation.lean`.

## References

* Cslib/Logics/Temporal/Metalogic/DerivationTree.lean — direct template
* Cslib/Foundations/Logic/Metalogic/Consistency.lean — generic MCS API
-/

namespace Cslib.Logic.Bimodal

open Cslib.Logic

variable {Atom : Type*}

/-! ## Derivability (Prop wrapper) -/

set_option linter.dupNamespace false in
/-- `Bimodal.Deriv Γ φ` holds iff there exists a derivation tree deriving `φ`
from `Γ` at `FrameClass.Base`. This is the `Prop`-level wrapper used by the
generic `DerivationSystem`. -/
def Bimodal.Deriv (Γ : List (Formula Atom)) (φ : Formula Atom) : Prop :=
  Nonempty (DerivationTree FrameClass.Base Γ φ)

set_option linter.dupNamespace false in
/-- `Bimodal.ThDerivable φ` means `φ` is derivable from the empty context
at `FrameClass.Base`. -/
def Bimodal.ThDerivable (φ : Formula Atom) : Prop :=
  Bimodal.Deriv (Atom := Atom) [] φ

/-! ## Basic Combinators -/

theorem mp_deriv {Γ : List (Formula Atom)} {φ ψ : Formula Atom}
    (h₁ : Bimodal.Deriv Γ (φ.imp ψ)) (h₂ : Bimodal.Deriv Γ φ) :
    Bimodal.Deriv Γ ψ := by
  obtain ⟨d₁⟩ := h₁; obtain ⟨d₂⟩ := h₂
  exact ⟨.modus_ponens Γ φ ψ d₁ d₂⟩

theorem weakening_deriv {Γ Δ : List (Formula Atom)} {φ : Formula Atom}
    (h : Bimodal.Deriv Γ φ) (hsub : ∀ x ∈ Γ, x ∈ Δ) :
    Bimodal.Deriv Δ φ := by
  obtain ⟨d⟩ := h
  exact ⟨.weakening Γ Δ φ d hsub⟩

theorem assumption_deriv {Γ : List (Formula Atom)} {φ : Formula Atom}
    (h : φ ∈ Γ) : Bimodal.Deriv Γ φ :=
  ⟨.assumption Γ φ h⟩

/-! ## DerivationSystem Instance -/

/-- The bimodal derivation system, connecting the bimodal proof system to the generic
MCS framework from `Consistency.lean`.

This provides `Deriv`, `weakening`, `assumption`, and `mp` as required by
`DerivationSystem (Formula Atom)`. -/
def bimodalDerivationSystem : Metalogic.DerivationSystem (Formula Atom) where
  Deriv := Bimodal.Deriv
  weakening := fun hd hsub => weakening_deriv hd hsub
  assumption := fun hmem => assumption_deriv hmem
  mp := fun h₁ h₂ => mp_deriv h₁ h₂

end Cslib.Logic.Bimodal
