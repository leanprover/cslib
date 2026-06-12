/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Defs
public import Cslib.Foundations.Logic.Metalogic.Consistency

/-! # DerivationTree -- Parameterized Syntactic Proof System for Propositional Logic

This module defines a Hilbert-style syntactic proof system parameterized over an axiom
predicate `Axioms : PL.Proposition Atom -> Prop`, enabling use for classical, intuitionistic,
and minimal propositional logics.

## Key Components

- `DerivationTree Axioms`: A parameterized inductive type with 4 constructors
  representing proof trees.
- `Deriv Axioms`: A `Prop`-level wrapper (`Nonempty (DerivationTree Axioms Γ φ)`).
- `Derivable Axioms`: Derivability from the empty context.
- `propDerivationSystem Axioms`: A `DerivationSystem (PL.Proposition Atom)` instance.

## Parameterization

The `Deriv`, `Derivable`, and `propDerivationSystem` definitions are parameterized over
an arbitrary axiom predicate `Axioms`.

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

/-- Derivation tree for propositional logic, parameterized over an axiom predicate.

`DerivationTree Axioms Γ φ` represents a proof tree showing that formula `φ` is derivable
from context `Γ` using axioms satisfying `Axioms`. Since it is a `Type` (not `Prop`), we can
pattern match on it for computable functions like `height`.

The 4 constructors are:
1. **ax**: Any axiom instance (satisfying `Axioms`) is derivable from any context.
2. **assumption**: Any formula in the context is derivable.
3. **modus_ponens**: From `Γ ⊢ φ → ψ` and `Γ ⊢ φ`, derive `Γ ⊢ ψ`.
4. **weakening**: From `Γ ⊢ φ` and `Γ ⊆ Δ`, derive `Δ ⊢ φ`. -/
inductive DerivationTree (Axioms : PL.Proposition Atom → Prop) :
    List (PL.Proposition Atom) → PL.Proposition Atom → Type _ where
  /-- Axiom rule: axiom schema instances are derivable from any context. -/
  | ax (Γ : List (PL.Proposition Atom)) (φ : PL.Proposition Atom)
      (h : Axioms φ) : DerivationTree Axioms Γ φ
  /-- Assumption rule: formulas in the context are derivable. -/
  | assumption (Γ : List (PL.Proposition Atom)) (φ : PL.Proposition Atom)
      (h : φ ∈ Γ) : DerivationTree Axioms Γ φ
  /-- Modus ponens: from `Γ ⊢ φ → ψ` and `Γ ⊢ φ`, derive `Γ ⊢ ψ`. -/
  | modus_ponens (Γ : List (PL.Proposition Atom)) (φ ψ : PL.Proposition Atom)
      (d₁ : DerivationTree Axioms Γ (φ → ψ))
      (d₂ : DerivationTree Axioms Γ φ) : DerivationTree Axioms Γ ψ
  /-- Weakening: from `Γ ⊢ φ` and `Γ ⊆ Δ`, derive `Δ ⊢ φ`. -/
  | weakening (Γ Δ : List (PL.Proposition Atom)) (φ : PL.Proposition Atom)
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
  | .weakening _ _ _ d _ => 1 + d.height

/-! ## Height Properties -/

theorem height_modus_ponens_left {Γ : List (PL.Proposition Atom)} {φ ψ : PL.Proposition Atom}
    (d₁ : DerivationTree Axioms Γ (φ → ψ)) (d₂ : DerivationTree Axioms Γ φ) :
    d₁.height < (modus_ponens Γ φ ψ d₁ d₂).height := by
  simp [height]; omega

theorem height_modus_ponens_right {Γ : List (PL.Proposition Atom)} {φ ψ : PL.Proposition Atom}
    (d₁ : DerivationTree Axioms Γ (φ → ψ)) (d₂ : DerivationTree Axioms Γ φ) :
    d₂.height < (modus_ponens Γ φ ψ d₁ d₂).height := by
  simp [height]; omega

theorem height_weakening {Γ Δ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (d : DerivationTree Axioms Γ φ) (h : ∀ x ∈ Γ, x ∈ Δ) :
    d.height < (weakening Γ Δ φ d h).height := by
  simp [height]

end DerivationTree

/-! ## Derivability (Prop wrapper) -/

/-- `Deriv Axioms Γ φ` holds iff there exists a derivation tree deriving `φ` from `Γ`
using axioms satisfying `Axioms`. This is the `Prop`-level wrapper used by the generic
`DerivationSystem`. -/
def Deriv (Axioms : PL.Proposition Atom → Prop) (Γ : List (PL.Proposition Atom))
    (φ : PL.Proposition Atom) : Prop :=
  Nonempty (DerivationTree Axioms Γ φ)

/-- `Derivable Axioms φ` means `φ` is derivable from the empty context using axioms
satisfying `Axioms`. -/
def Derivable (Axioms : PL.Proposition Atom → Prop) (φ : PL.Proposition Atom) : Prop :=
  Deriv Axioms [] φ

/-! ## Basic Combinators -/

theorem mp_deriv {Axioms : PL.Proposition Atom → Prop}
    {Γ : List (PL.Proposition Atom)} {φ ψ : PL.Proposition Atom}
    (h₁ : Deriv Axioms Γ (φ → ψ)) (h₂ : Deriv Axioms Γ φ) : Deriv Axioms Γ ψ := by
  obtain ⟨d₁⟩ := h₁; obtain ⟨d₂⟩ := h₂
  exact ⟨.modus_ponens Γ φ ψ d₁ d₂⟩

theorem weakening_deriv {Axioms : PL.Proposition Atom → Prop}
    {Γ Δ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (h : Deriv Axioms Γ φ) (hsub : ∀ x ∈ Γ, x ∈ Δ) : Deriv Axioms Δ φ := by
  obtain ⟨d⟩ := h
  exact ⟨.weakening Γ Δ φ d hsub⟩

theorem assumption_deriv {Axioms : PL.Proposition Atom → Prop}
    {Γ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (h : φ ∈ Γ) : Deriv Axioms Γ φ :=
  ⟨.assumption Γ φ h⟩

/-! ## DerivationSystem Instance -/

/-- The propositional derivation system parameterized over an axiom predicate, connecting
the propositional proof system to the generic MCS framework from `Consistency.lean`.

This provides `Deriv`, `weakening`, `assumption`, and `mp` as required by
`DerivationSystem (PL.Proposition Atom)`. -/
def propDerivationSystem (Axioms : PL.Proposition Atom → Prop) :
    Metalogic.DerivationSystem (PL.Proposition Atom) where
  Deriv := Deriv Axioms
  weakening := fun hd hsub => weakening_deriv hd hsub
  assumption := fun hmem => assumption_deriv hmem
  mp := fun h₁ h₂ => mp_deriv h₁ h₂

end Cslib.Logic.PL
