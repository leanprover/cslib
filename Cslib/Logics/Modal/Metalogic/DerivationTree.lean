/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Basic
public import Cslib.Foundations.Logic.Metalogic.Consistency

/-! # DerivationTree -- Parameterized Syntactic Proof System for Normal Modal Logics

This module defines a Hilbert-style syntactic proof system parameterized over an axiom
predicate `Axioms : Proposition Atom -> Prop`, enabling use for any normal modal logic
(K, T, D, S4, S5, etc.).

## Key Components

- `ModalAxiom`: An inductive type enumerating the axiom schemata of S5 (4 propositional + 4 modal).
- `DerivationTree Axioms`: A parameterized inductive type with 5 constructors
  representing proof trees.
- `Deriv Axioms`: A `Prop`-level wrapper (`Nonempty (DerivationTree Axioms Gamma phi)`).
- `Derivable Axioms`: Derivability from the empty context.
- `modalDerivationSystem Axioms`: A `DerivationSystem (Proposition Atom)` instance.

## Backward Compatibility

Type aliases `S5DerivationTree`, `S5Deriv`, `S5Derivable`, and `s5DerivationSystem`
instantiate the parameterized types at `ModalAxiom` for backward compatibility.

## Design

`DerivationTree` is a `Type` (not a `Prop`) to enable pattern matching and computable
height functions. The `Deriv` wrapper provides the `Prop` version for the generic
`DerivationSystem`.

## References

* BimodalLogic/Theories/Bimodal/ProofSystem/Derivation.lean -- reference pattern
* Cslib/Foundations/Logic/Metalogic/Consistency.lean -- generic MCS API
-/

@[expose] public section

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

/-- Derivation tree for normal modal logics, parameterized over an axiom predicate.

`DerivationTree Axioms Gamma phi` represents a proof tree showing that formula `phi` is derivable
from context `Gamma` using axioms satisfying `Axioms`. Since it is a `Type` (not `Prop`), we can
pattern match on it for computable functions like `height`.

The 5 constructors are:
1. **axiom**: Any axiom instance (satisfying `Axioms`) is derivable from any context.
2. **assumption**: Any formula in the context is derivable.
3. **modus_ponens**: From `Gamma |- phi -> psi` and `Gamma |- phi`, derive `Gamma |- psi`.
4. **necessitation**: From `|- phi` (empty context), derive `|- box phi`.
5. **weakening**: From `Gamma |- phi` and `Gamma <= Delta`, derive `Delta |- phi`. -/
inductive DerivationTree (Axioms : Proposition Atom → Prop) :
    List (Proposition Atom) → Proposition Atom → Type _ where
  /-- Axiom rule: axiom schema instances are derivable from any context. -/
  | ax (Γ : List (Proposition Atom)) (φ : Proposition Atom)
      (h : Axioms φ) : DerivationTree Axioms Γ φ
  /-- Assumption rule: formulas in the context are derivable. -/
  | assumption (Γ : List (Proposition Atom)) (φ : Proposition Atom)
      (h : φ ∈ Γ) : DerivationTree Axioms Γ φ
  /-- Modus ponens: from `Γ ⊢ φ → ψ` and `Γ ⊢ φ`, derive `Γ ⊢ ψ`. -/
  | modus_ponens (Γ : List (Proposition Atom)) (φ ψ : Proposition Atom)
      (d₁ : DerivationTree Axioms Γ (φ.imp ψ))
      (d₂ : DerivationTree Axioms Γ φ) : DerivationTree Axioms Γ ψ
  /-- Necessitation: from `⊢ φ` (empty context), derive `⊢ □φ`. -/
  | necessitation (φ : Proposition Atom)
      (d : DerivationTree Axioms [] φ) : DerivationTree Axioms [] (Proposition.box φ)
  /-- Weakening: from `Γ ⊢ φ` and `Γ ⊆ Δ`, derive `Δ ⊢ φ`. -/
  | weakening (Γ Δ : List (Proposition Atom)) (φ : Proposition Atom)
      (d : DerivationTree Axioms Γ φ)
      (h : ∀ x ∈ Γ, x ∈ Δ) : DerivationTree Axioms Δ φ

namespace DerivationTree

/-! ## Height Measure -/

/-- Computable height function for derivation trees.

Used for well-founded recursion in the deduction theorem proof. -/
def height : DerivationTree Axioms Γ φ → Nat
  | .ax _ _ _ => 0
  | .assumption _ _ _ => 0
  | .modus_ponens _ _ _ d₁ d₂ => 1 + max d₁.height d₂.height
  | .necessitation _ d => 1 + d.height
  | .weakening _ _ _ d _ => 1 + d.height

/-! ## Height Properties -/

theorem height_modus_ponens_left {Γ : List (Proposition Atom)} {φ ψ : Proposition Atom}
    (d₁ : DerivationTree Axioms Γ (φ → ψ)) (d₂ : DerivationTree Axioms Γ φ) :
    d₁.height < (modus_ponens Γ φ ψ d₁ d₂).height := by
  simp [height]; omega

theorem height_modus_ponens_right {Γ : List (Proposition Atom)} {φ ψ : Proposition Atom}
    (d₁ : DerivationTree Axioms Γ (φ → ψ)) (d₂ : DerivationTree Axioms Γ φ) :
    d₂.height < (modus_ponens Γ φ ψ d₁ d₂).height := by
  simp [height]; omega

theorem height_weakening {Γ Δ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree Axioms Γ φ) (h : ∀ x ∈ Γ, x ∈ Δ) :
    d.height < (weakening Γ Δ φ d h).height := by
  simp [height]

end DerivationTree

/-! ## Derivability (Prop wrapper) -/

/-- `Deriv Axioms Gamma phi` holds iff there exists a derivation tree deriving `phi` from `Gamma`
using axioms satisfying `Axioms`. This is the `Prop`-level wrapper used by the generic
`DerivationSystem`. -/
def Deriv (Axioms : Proposition Atom → Prop) (Γ : List (Proposition Atom))
    (φ : Proposition Atom) : Prop :=
  Nonempty (DerivationTree Axioms Γ φ)

/-- `Derivable Axioms phi` means `phi` is derivable from the empty context using axioms
satisfying `Axioms`. -/
def Derivable (Axioms : Proposition Atom → Prop) (φ : Proposition Atom) : Prop :=
  Deriv Axioms [] φ

/-! ## Basic Combinators -/

theorem mp_deriv {Axioms : Proposition Atom → Prop}
    {Γ : List (Proposition Atom)} {φ ψ : Proposition Atom}
    (h₁ : Deriv Axioms Γ (φ → ψ)) (h₂ : Deriv Axioms Γ φ) : Deriv Axioms Γ ψ := by
  obtain ⟨d₁⟩ := h₁; obtain ⟨d₂⟩ := h₂
  exact ⟨.modus_ponens Γ φ ψ d₁ d₂⟩

theorem weakening_deriv {Axioms : Proposition Atom → Prop}
    {Γ Δ : List (Proposition Atom)} {φ : Proposition Atom}
    (h : Deriv Axioms Γ φ) (hsub : ∀ x ∈ Γ, x ∈ Δ) : Deriv Axioms Δ φ := by
  obtain ⟨d⟩ := h
  exact ⟨.weakening Γ Δ φ d hsub⟩

theorem assumption_deriv {Axioms : Proposition Atom → Prop}
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (h : φ ∈ Γ) : Deriv Axioms Γ φ :=
  ⟨.assumption Γ φ h⟩

/-! ## DerivationSystem Instance -/

/-- The modal derivation system parameterized over an axiom predicate, connecting the
modal proof system to the generic MCS framework from `Consistency.lean`.

This provides `Deriv`, `weakening`, `assumption`, and `mp` as required by
`DerivationSystem (Proposition Atom)`. -/
def modalDerivationSystem (Axioms : Proposition Atom → Prop) :
    Metalogic.DerivationSystem (Proposition Atom) where
  Deriv := Deriv Axioms
  weakening := fun hd hsub => weakening_deriv hd hsub
  assumption := fun hmem => assumption_deriv hmem
  mp := fun h₁ h₂ => mp_deriv h₁ h₂

/-! ## Backward-Compatible Aliases -/

/-- S5 derivation tree: `DerivationTree` instantiated at `ModalAxiom`. -/
abbrev S5DerivationTree := @DerivationTree Atom ModalAxiom

/-- S5 derivability from context: `Deriv` instantiated at `ModalAxiom`. -/
abbrev S5Deriv := @Deriv Atom ModalAxiom

/-- S5 derivability from empty context: `Derivable` instantiated at `ModalAxiom`. -/
abbrev S5Derivable := @Derivable Atom ModalAxiom

/-- S5 derivation system: `modalDerivationSystem` instantiated at `ModalAxiom`. -/
def s5DerivationSystem : Metalogic.DerivationSystem (Proposition Atom) :=
  modalDerivationSystem (@ModalAxiom Atom)

end Cslib.Logic.Modal
