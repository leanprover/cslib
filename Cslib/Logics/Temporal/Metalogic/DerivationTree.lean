/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Temporal.ProofSystem.Derivation
public import Cslib.Foundations.Logic.Metalogic.Consistency

/-! # DerivationTree — Height, Deriv, and DerivationSystem for Temporal Logic

This module extends the existing `DerivationTree` for temporal logic BX with:

- `DerivationTree.height`: A computable height function for all 6 constructors.
- Height ordering lemmas for termination proofs.
- `Temporal.Deriv`: A `Prop`-level wrapper (`Nonempty (DerivationTree ...)`).
- `Temporal.Derivable`: Derivability from the empty context at `FrameClass.Base`.
- `temporalDerivationSystem`: A `DerivationSystem (Formula Atom)` instance connecting
  to the generic MCS framework from `Consistency.lean`.

## Design

The existing `DerivationTree` in `ProofSystem/Derivation.lean` is a `Type` (not `Prop`),
enabling pattern matching. This module adds the height measure needed for well-founded
recursion in the deduction theorem, and the `Prop` wrappers needed by the generic MCS
framework.

## References

* Cslib/Logics/Modal/Metalogic/DerivationTree.lean — direct template
* Cslib/Foundations/Logic/Metalogic/Consistency.lean — generic MCS API
-/

@[expose] public section

namespace Cslib.Logic.Temporal

open Cslib.Logic

variable {Atom : Type*}

namespace DerivationTree

/-! ## Height Measure -/

/-- Computable height function for temporal derivation trees.

Used for well-founded recursion in the deduction theorem proof. -/
def height : DerivationTree fc Γ φ → Nat
  | .axiom _ _ _ _ => 0
  | .assumption _ _ _ => 0
  | .modus_ponens _ _ _ d₁ d₂ => 1 + max d₁.height d₂.height
  | .temporal_necessitation _ d => 1 + d.height
  | .temporal_duality _ d => 1 + d.height
  | .weakening _ _ _ d _ => 1 + d.height

/-! ## Height Properties -/

theorem height_modus_ponens_left {Γ : Context Atom} {φ ψ : Formula Atom}
    (d₁ : DerivationTree fc Γ (φ → ψ)) (d₂ : DerivationTree fc Γ φ) :
    d₁.height < (modus_ponens Γ φ ψ d₁ d₂).height := by
  simp [height]; omega

theorem height_modus_ponens_right {Γ : Context Atom} {φ ψ : Formula Atom}
    (d₁ : DerivationTree fc Γ (φ → ψ)) (d₂ : DerivationTree fc Γ φ) :
    d₂.height < (modus_ponens Γ φ ψ d₁ d₂).height := by
  simp [height]; omega

theorem height_temporal_necessitation {φ : Formula Atom}
    (d : DerivationTree fc [] φ) :
    d.height < (temporal_necessitation φ d).height := by
  simp [height]

theorem height_temporal_duality {φ : Formula Atom}
    (d : DerivationTree fc [] φ) :
    d.height < (temporal_duality φ d).height := by
  simp [height]

theorem height_weakening {Γ Δ : Context Atom} {φ : Formula Atom}
    (d : DerivationTree fc Γ φ) (h : Γ ⊆ Δ) :
    d.height < (weakening Γ Δ φ d h).height := by
  simp [height]

end DerivationTree

/-! ## Derivability (Prop wrapper) -/

set_option linter.dupNamespace false in
/-- `Temporal.Deriv Γ φ` holds iff there exists a derivation tree deriving `φ`
from `Γ` at `FrameClass.Base`. This is the `Prop`-level wrapper used by the
generic `DerivationSystem`. -/
def Temporal.Deriv (Γ : List (Formula Atom)) (φ : Formula Atom) : Prop :=
  Nonempty (DerivationTree FrameClass.Base Γ φ)

set_option linter.dupNamespace false in
/-- `Temporal.ThDerivable φ` means `φ` is derivable from the empty context
at `FrameClass.Base`. -/
def Temporal.ThDerivable (φ : Formula Atom) : Prop :=
  Temporal.Deriv (Atom := Atom) [] φ

/-! ## Basic Combinators -/

theorem mp_deriv {Γ : List (Formula Atom)} {φ ψ : Formula Atom}
    (h₁ : Temporal.Deriv Γ (φ → ψ)) (h₂ : Temporal.Deriv Γ φ) :
    Temporal.Deriv Γ ψ := by
  obtain ⟨d₁⟩ := h₁; obtain ⟨d₂⟩ := h₂
  exact ⟨.modus_ponens Γ φ ψ d₁ d₂⟩

theorem weakening_deriv {Γ Δ : List (Formula Atom)} {φ : Formula Atom}
    (h : Temporal.Deriv Γ φ) (hsub : ∀ x ∈ Γ, x ∈ Δ) :
    Temporal.Deriv Δ φ := by
  obtain ⟨d⟩ := h
  exact ⟨.weakening Γ Δ φ d hsub⟩

theorem assumption_deriv {Γ : List (Formula Atom)} {φ : Formula Atom}
    (h : φ ∈ Γ) : Temporal.Deriv Γ φ :=
  ⟨.assumption Γ φ h⟩

/-! ## DerivationSystem Instance -/

/-- The temporal derivation system, connecting the temporal proof system to the generic
MCS framework from `Consistency.lean`.

This provides `Deriv`, `weakening`, `assumption`, and `mp` as required by
`DerivationSystem (Formula Atom)`. -/
def temporalDerivationSystem : Metalogic.DerivationSystem (Formula Atom) where
  Deriv := Temporal.Deriv
  weakening := fun hd hsub => weakening_deriv hd hsub
  assumption := fun hmem => assumption_deriv hmem
  mp := fun h₁ h₂ => mp_deriv h₁ h₂

end Cslib.Logic.Temporal
