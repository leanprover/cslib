/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.ProofSystem.Axioms
public import Cslib.Foundations.Logic.Metalogic.Consistency

/-! # DerivationTree -- Syntactic Proof System for Propositional Logic

This module defines a Hilbert-style syntactic proof system for classical propositional
logic, parameterized over an atom type. The key components are:

- `DerivationTree`: An inductive type with 4 constructors representing proof trees.
- `Deriv`: A `Prop`-level wrapper (`Nonempty (DerivationTree Γ φ)`).
- `Derivable`: Derivability from the empty context.
- `propDerivationSystem`: A `DerivationSystem (PL.Proposition Atom)` instance connecting
  to the generic MCS framework from `Consistency.lean`.

## Design

`DerivationTree` is a `Type` (not a `Prop`) to enable pattern matching and computable
height functions. The `Deriv` wrapper provides the `Prop` version for the generic
`DerivationSystem`.

Unlike the modal `DerivationTree`, the propositional version has only 4 constructors
(no necessitation rule), since propositional logic has no modal operators.

## References

* Cslib/Logics/Modal/Metalogic/DerivationTree.lean -- modal derivation tree pattern
* Cslib/Foundations/Logic/Metalogic/Consistency.lean -- generic MCS API
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic

variable {Atom : Type*}

/-! ## Derivation Trees -/

/-- Derivation tree for classical propositional logic.

`DerivationTree Γ φ` represents a proof tree showing that formula `φ` is derivable
from context `Γ`. Since it is a `Type` (not `Prop`), we can pattern match on it
for computable functions like `height`.

The 4 constructors are:
1. **ax**: Any axiom instance is derivable from any context.
2. **assumption**: Any formula in the context is derivable.
3. **modus_ponens**: From `Γ ⊢ φ → ψ` and `Γ ⊢ φ`, derive `Γ ⊢ ψ`.
4. **weakening**: From `Γ ⊢ φ` and `Γ ⊆ Δ`, derive `Δ ⊢ φ`. -/
inductive DerivationTree : List (PL.Proposition Atom) → PL.Proposition Atom → Type _ where
  /-- Axiom rule: axiom schema instances are derivable from any context. -/
  | ax (Γ : List (PL.Proposition Atom)) (φ : PL.Proposition Atom)
      (h : PropositionalAxiom φ) : DerivationTree Γ φ
  /-- Assumption rule: formulas in the context are derivable. -/
  | assumption (Γ : List (PL.Proposition Atom)) (φ : PL.Proposition Atom)
      (h : φ ∈ Γ) : DerivationTree Γ φ
  /-- Modus ponens: from `Γ ⊢ φ → ψ` and `Γ ⊢ φ`, derive `Γ ⊢ ψ`. -/
  | modus_ponens (Γ : List (PL.Proposition Atom)) (φ ψ : PL.Proposition Atom)
      (d₁ : DerivationTree Γ (φ.imp ψ))
      (d₂ : DerivationTree Γ φ) : DerivationTree Γ ψ
  /-- Weakening: from `Γ ⊢ φ` and `Γ ⊆ Δ`, derive `Δ ⊢ φ`. -/
  | weakening (Γ Δ : List (PL.Proposition Atom)) (φ : PL.Proposition Atom)
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
  | .weakening _ _ _ d _ => 1 + d.height

/-! ## Height Properties -/

theorem height_modus_ponens_left {Γ : List (PL.Proposition Atom)} {φ ψ : PL.Proposition Atom}
    (d₁ : DerivationTree Γ (φ.imp ψ)) (d₂ : DerivationTree Γ φ) :
    d₁.height < (modus_ponens Γ φ ψ d₁ d₂).height := by
  simp [height]; omega

theorem height_modus_ponens_right {Γ : List (PL.Proposition Atom)} {φ ψ : PL.Proposition Atom}
    (d₁ : DerivationTree Γ (φ.imp ψ)) (d₂ : DerivationTree Γ φ) :
    d₂.height < (modus_ponens Γ φ ψ d₁ d₂).height := by
  simp [height]; omega

theorem height_weakening {Γ Δ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (d : DerivationTree Γ φ) (h : ∀ x ∈ Γ, x ∈ Δ) :
    d.height < (weakening Γ Δ φ d h).height := by
  simp [height]

end DerivationTree

/-! ## Derivability (Prop wrapper) -/

/-- `Deriv Γ φ` holds iff there exists a derivation tree deriving `φ` from `Γ`.
This is the `Prop`-level wrapper used by the generic `DerivationSystem`. -/
def Deriv (Γ : List (PL.Proposition Atom)) (φ : PL.Proposition Atom) : Prop :=
  Nonempty (DerivationTree Γ φ)

/-- `Derivable φ` means `φ` is derivable from the empty context. -/
def Derivable (φ : PL.Proposition Atom) : Prop :=
  Deriv [] φ

/-! ## Basic Combinators -/

theorem mp_deriv {Γ : List (PL.Proposition Atom)} {φ ψ : PL.Proposition Atom}
    (h₁ : Deriv Γ (φ.imp ψ)) (h₂ : Deriv Γ φ) : Deriv Γ ψ := by
  obtain ⟨d₁⟩ := h₁; obtain ⟨d₂⟩ := h₂
  exact ⟨.modus_ponens Γ φ ψ d₁ d₂⟩

theorem weakening_deriv {Γ Δ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (h : Deriv Γ φ) (hsub : ∀ x ∈ Γ, x ∈ Δ) : Deriv Δ φ := by
  obtain ⟨d⟩ := h
  exact ⟨.weakening Γ Δ φ d hsub⟩

theorem assumption_deriv {Γ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (h : φ ∈ Γ) : Deriv Γ φ :=
  ⟨.assumption Γ φ h⟩

/-! ## DerivationSystem Instance -/

/-- The propositional derivation system, connecting the propositional proof system to the
generic MCS framework from `Consistency.lean`.

This provides `Deriv`, `weakening`, `assumption`, and `mp` as required by
`DerivationSystem (PL.Proposition Atom)`. -/
def propDerivationSystem : Metalogic.DerivationSystem (PL.Proposition Atom) where
  Deriv := Deriv
  weakening := fun hd hsub => weakening_deriv hd hsub
  assumption := fun hmem => assumption_deriv hmem
  mp := fun h₁ h₂ => mp_deriv h₁ h₂

end Cslib.Logic.PL
