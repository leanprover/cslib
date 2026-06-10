/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import Cslib.Logics.Modal.Basic
import Cslib.Foundations.Logic.Metalogic.Consistency

/-! # DerivationTree — Syntactic Proof System for S5 Modal Logic

This module defines a Hilbert-style syntactic proof system for S5 modal logic,
parameterized over an atom type. The key components are:

- `ModalAxiom`: An inductive type enumerating the axiom schemata of S5 (4 propositional + 4 modal).
- `DerivationTree`: An inductive type with 5 constructors representing proof trees.
- `Deriv`: A `Prop`-level wrapper (`Nonempty (DerivationTree Γ φ)`).
- `Derivable`: Derivability from the empty context.
- `modalDerivationSystem`: A `DerivationSystem (Proposition Atom)` instance connecting
  to the generic MCS framework from `Consistency.lean`.

## Design

`DerivationTree` is a `Type` (not a `Prop`) to enable pattern matching and computable
height functions. The `Deriv` wrapper provides the `Prop` version for the generic
`DerivationSystem`.

## References

* BimodalLogic/Theories/Bimodal/ProofSystem/Derivation.lean — reference pattern
* Cslib/Foundations/Logic/Metalogic/Consistency.lean — generic MCS API
-/

namespace Cslib.Logic.Modal

open Cslib.Logic

variable {Atom : Type*}

/-! ## Axiom Schemata -/

/-- Axiom schemata for S5 modal logic.

The 8 axiom constructors cover:
- **Propositional** (4): `implyK` (weakening), `implyS` (distribution), `efq` (ex falso),
  `peirce` (double negation elimination / Peirce's law)
- **Modal** (4): `modalK` (K distribution), `modalT` (reflexivity), `modalFour` (transitivity),
  `modalB` (symmetry)

Together with modus ponens and necessitation, these axioms characterize S5. -/
inductive ModalAxiom : Proposition Atom → Prop where
  /-- Weakening: `φ → (ψ → φ)` -/
  | implyK (φ ψ : Proposition Atom) :
      ModalAxiom (φ.imp (ψ.imp φ))
  /-- Distribution: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))` -/
  | implyS (φ ψ χ : Proposition Atom) :
      ModalAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))
  /-- Ex falso quodlibet: `⊥ → φ` -/
  | efq (φ : Proposition Atom) :
      ModalAxiom (Proposition.bot.imp φ)
  /-- Peirce's law / DNE: `((φ → ψ) → φ) → φ` -/
  | peirce (φ ψ : Proposition Atom) :
      ModalAxiom (((φ.imp ψ).imp φ).imp φ)
  /-- K distribution: `□(φ → ψ) → (□φ → □ψ)` -/
  | modalK (φ ψ : Proposition Atom) :
      ModalAxiom ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ)))
  /-- T / reflexivity: `□φ → φ` -/
  | modalT (φ : Proposition Atom) :
      ModalAxiom ((Proposition.box φ).imp φ)
  /-- 4 / transitivity: `□φ → □□φ` -/
  | modalFour (φ : Proposition Atom) :
      ModalAxiom ((Proposition.box φ).imp (Proposition.box (Proposition.box φ)))
  /-- B / symmetry: `φ → □◇φ` -/
  | modalB (φ : Proposition Atom) :
      ModalAxiom (φ.imp (Proposition.box (Proposition.diamond φ)))

/-! ## Derivation Trees -/

/-- Derivation tree for S5 modal logic.

`DerivationTree Γ φ` represents a proof tree showing that formula `φ` is derivable
from context `Γ`. Since it is a `Type` (not `Prop`), we can pattern match on it
for computable functions like `height`.

The 5 constructors are:
1. **axiom**: Any axiom instance is derivable from any context.
2. **assumption**: Any formula in the context is derivable.
3. **modus_ponens**: From `Γ ⊢ φ → ψ` and `Γ ⊢ φ`, derive `Γ ⊢ ψ`.
4. **necessitation**: From `⊢ φ` (empty context), derive `⊢ □φ`.
5. **weakening**: From `Γ ⊢ φ` and `Γ ⊆ Δ`, derive `Δ ⊢ φ`. -/
inductive DerivationTree : List (Proposition Atom) → Proposition Atom → Type _ where
  /-- Axiom rule: axiom schema instances are derivable from any context. -/
  | ax (Γ : List (Proposition Atom)) (φ : Proposition Atom)
      (h : ModalAxiom φ) : DerivationTree Γ φ
  /-- Assumption rule: formulas in the context are derivable. -/
  | assumption (Γ : List (Proposition Atom)) (φ : Proposition Atom)
      (h : φ ∈ Γ) : DerivationTree Γ φ
  /-- Modus ponens: from `Γ ⊢ φ → ψ` and `Γ ⊢ φ`, derive `Γ ⊢ ψ`. -/
  | modus_ponens (Γ : List (Proposition Atom)) (φ ψ : Proposition Atom)
      (d₁ : DerivationTree Γ (φ.imp ψ))
      (d₂ : DerivationTree Γ φ) : DerivationTree Γ ψ
  /-- Necessitation: from `⊢ φ` (empty context), derive `⊢ □φ`. -/
  | necessitation (φ : Proposition Atom)
      (d : DerivationTree [] φ) : DerivationTree [] (Proposition.box φ)
  /-- Weakening: from `Γ ⊢ φ` and `Γ ⊆ Δ`, derive `Δ ⊢ φ`. -/
  | weakening (Γ Δ : List (Proposition Atom)) (φ : Proposition Atom)
      (d : DerivationTree Γ φ)
      (h : ∀ x ∈ Γ, x ∈ Δ) : DerivationTree Δ φ

namespace DerivationTree

/-! ## Height Measure -/

/-- Computable height function for derivation trees.

Used for well-founded recursion in the deduction theorem proof. -/
def height : DerivationTree Γ φ → Nat
  | .ax _ _ _ => 0
  | .assumption _ _ _ => 0
  | .modus_ponens _ _ _ d₁ d₂ => 1 + max d₁.height d₂.height
  | .necessitation _ d => 1 + d.height
  | .weakening _ _ _ d _ => 1 + d.height

/-! ## Height Properties -/

theorem height_modus_ponens_left {Γ : List (Proposition Atom)} {φ ψ : Proposition Atom}
    (d₁ : DerivationTree Γ (φ.imp ψ)) (d₂ : DerivationTree Γ φ) :
    d₁.height < (modus_ponens Γ φ ψ d₁ d₂).height := by
  simp [height]; omega

theorem height_modus_ponens_right {Γ : List (Proposition Atom)} {φ ψ : Proposition Atom}
    (d₁ : DerivationTree Γ (φ.imp ψ)) (d₂ : DerivationTree Γ φ) :
    d₂.height < (modus_ponens Γ φ ψ d₁ d₂).height := by
  simp [height]; omega

theorem height_weakening {Γ Δ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree Γ φ) (h : ∀ x ∈ Γ, x ∈ Δ) :
    d.height < (weakening Γ Δ φ d h).height := by
  simp [height]

end DerivationTree

/-! ## Derivability (Prop wrapper) -/

/-- `Deriv Γ φ` holds iff there exists a derivation tree deriving `φ` from `Γ`.
This is the `Prop`-level wrapper used by the generic `DerivationSystem`. -/
def Deriv (Γ : List (Proposition Atom)) (φ : Proposition Atom) : Prop :=
  Nonempty (DerivationTree Γ φ)

/-- `Derivable φ` means `φ` is derivable from the empty context. -/
def Derivable (φ : Proposition Atom) : Prop :=
  Deriv [] φ

/-! ## Basic Combinators -/

theorem mp_deriv {Γ : List (Proposition Atom)} {φ ψ : Proposition Atom}
    (h₁ : Deriv Γ (φ.imp ψ)) (h₂ : Deriv Γ φ) : Deriv Γ ψ := by
  obtain ⟨d₁⟩ := h₁; obtain ⟨d₂⟩ := h₂
  exact ⟨.modus_ponens Γ φ ψ d₁ d₂⟩

theorem weakening_deriv {Γ Δ : List (Proposition Atom)} {φ : Proposition Atom}
    (h : Deriv Γ φ) (hsub : ∀ x ∈ Γ, x ∈ Δ) : Deriv Δ φ := by
  obtain ⟨d⟩ := h
  exact ⟨.weakening Γ Δ φ d hsub⟩

theorem assumption_deriv {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (h : φ ∈ Γ) : Deriv Γ φ :=
  ⟨.assumption Γ φ h⟩

/-! ## DerivationSystem Instance -/

/-- The modal derivation system, connecting the modal proof system to the generic
MCS framework from `Consistency.lean`.

This provides `Deriv`, `weakening`, `assumption`, and `mp` as required by
`DerivationSystem (Proposition Atom)`. -/
def modalDerivationSystem : Metalogic.DerivationSystem (Proposition Atom) where
  Deriv := Deriv
  weakening := fun hd hsub => weakening_deriv hd hsub
  assumption := fun hmem => assumption_deriv hmem
  mp := fun h₁ h₂ => mp_deriv h₁ h₂

end Cslib.Logic.Modal
