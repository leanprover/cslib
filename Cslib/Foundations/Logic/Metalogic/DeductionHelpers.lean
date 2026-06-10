/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Foundations.Logic.Connectives

/-! # Generic Deduction Theorem Helpers

This module defines a `HasHilbertTree` typeclass abstracting the common structure
needed by the 4 deduction theorem helper lemmas across PL, Modal, Temporal, and
Bimodal logics. Each logic instantiates this typeclass, and the 4 generic helpers
(`deduction_axiom`, `deduction_imp_self`, `deduction_assumption_other`,
`deduction_mp_under_imp`) are proven once here.

The per-logic `deduction_with_mem` and `deduction_theorem` remain concrete in each
logic because they require pattern matching on concrete `DerivationTree` constructors
and use `termination_by` on concrete height functions.

## Design

The typeclass provides 6 fields:
- `Tree`: The derivation tree type `List F → F → Type*`
- `implyK`: Produces `[] ⊢ φ → (ψ → φ)` (K/weakening axiom)
- `implyS`: Produces `[] ⊢ (φ→(ψ→χ)) → ((φ→ψ) → (φ→χ))` (S/distribution axiom)
- `assumption`: From `φ ∈ Γ`, produces `Γ ⊢ φ`
- `mp`: From `Γ ⊢ φ → ψ` and `Γ ⊢ φ`, produces `Γ ⊢ ψ`
- `weakening`: From `Γ ⊢ φ` and `∀ x ∈ Γ, x ∈ Δ`, produces `Δ ⊢ φ`

The `implyK`/`implyS` fields produce trees from the empty context, already
incorporating any axiom-type or frame-class proofs. This allows the generic
helpers to work uniformly across logics with different axiom systems.

## References

* Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean
* Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean
* Cslib/Logics/Temporal/Metalogic/DeductionTheorem.lean
* Cslib/Logics/Bimodal/Metalogic/Core/DeductionTheorem.lean
-/

@[expose] public section

namespace Cslib.Logic

open Cslib.Logic

variable {F : Type*} [HasImp F]

/-- Typeclass abstracting the Hilbert-style derivation tree operations needed
by the deduction theorem helper lemmas.

Each logic (PL, Modal, Temporal, Bimodal) instantiates this with its own
`DerivationTree` type and axiom constructors. The `implyK` and `implyS` fields
produce trees from the empty context, encapsulating logic-specific axiom
constructors and frame-class proofs. -/
class HasHilbertTree (F : Type*) [HasImp F] where
  /-- The derivation tree type, parameterized by context and conclusion. -/
  Tree : List F → F → Type*
  /-- K axiom (weakening): `[] ⊢ φ → (ψ → φ)` -/
  implyK : (φ ψ : F) → Tree [] (HasImp.imp φ (HasImp.imp ψ φ))
  /-- S axiom (distribution): `[] ⊢ (φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))` -/
  implyS : (φ ψ χ : F) → Tree []
    (HasImp.imp (HasImp.imp φ (HasImp.imp ψ χ))
      (HasImp.imp (HasImp.imp φ ψ) (HasImp.imp φ χ)))
  /-- Assumption rule: from `φ ∈ Γ`, derive `Γ ⊢ φ`. -/
  assumption : {Γ : List F} → {φ : F} → φ ∈ Γ → Tree Γ φ
  /-- Modus ponens: from `Γ ⊢ φ → ψ` and `Γ ⊢ φ`, derive `Γ ⊢ ψ`. -/
  mp : {Γ : List F} → {φ ψ : F} → Tree Γ (HasImp.imp φ ψ) → Tree Γ φ → Tree Γ ψ
  /-- Weakening: from `Γ ⊢ φ` and `∀ x ∈ Γ, x ∈ Δ`, derive `Δ ⊢ φ`. -/
  weakening : {Γ Δ : List F} → {φ : F} → Tree Γ φ → (∀ x ∈ Γ, x ∈ Δ) → Tree Δ φ

variable [HasHilbertTree F]

/-! ## Generic Deduction Helpers -/

/-- If `d` is a derivation of `φ` from empty context, then `Γ ⊢ A → φ`.
This is the axiom case of the deduction theorem. -/
noncomputable def deduction_axiom (Γ : List F) (A : F)
    (d_empty : HasHilbertTree.Tree (F := F) [] φ) :
    HasHilbertTree.Tree Γ (HasImp.imp A φ) :=
  let k := HasHilbertTree.implyK (F := F) φ A
  let step := HasHilbertTree.mp k d_empty
  HasHilbertTree.weakening step (fun _ h => nomatch h)

/-- `Γ ⊢ A → A` (identity / self-implication).
Built from S, K, K axioms. -/
noncomputable def deduction_imp_self (Γ : List F) (A : F) :
    HasHilbertTree.Tree Γ (HasImp.imp A A) :=
  let s := HasHilbertTree.implyS (F := F) A (HasImp.imp A A) A
  let k1 := HasHilbertTree.implyK (F := F) A (HasImp.imp A A)
  let k2 := HasHilbertTree.implyK (F := F) A A
  let step1 := HasHilbertTree.mp s k1
  let result := HasHilbertTree.mp step1 k2
  HasHilbertTree.weakening result (fun _ h => nomatch h)

/-- If `B ∈ Γ`, then `Γ ⊢ A → B`. Uses the K axiom. -/
noncomputable def deduction_assumption_other (Γ : List F) (A B : F)
    (h_mem : B ∈ Γ) : HasHilbertTree.Tree Γ (HasImp.imp A B) :=
  let b_deriv := HasHilbertTree.assumption (F := F) h_mem
  let k := HasHilbertTree.implyK (F := F) B A
  let k_weak := HasHilbertTree.weakening k (fun _ h => nomatch h)
  HasHilbertTree.mp k_weak b_deriv

/-- Modus ponens under implication: from `Γ ⊢ A → (C → D)` and `Γ ⊢ A → C`,
derive `Γ ⊢ A → D`. Uses the S axiom. -/
noncomputable def deduction_mp_under_imp (Γ : List F) (A C D : F)
    (h₁ : HasHilbertTree.Tree Γ (HasImp.imp A (HasImp.imp C D)))
    (h₂ : HasHilbertTree.Tree Γ (HasImp.imp A C)) :
    HasHilbertTree.Tree Γ (HasImp.imp A D) :=
  let s := HasHilbertTree.implyS (F := F) A C D
  let s_weak := HasHilbertTree.weakening s (fun _ h => nomatch h)
  let step1 := HasHilbertTree.mp s_weak h₁
  HasHilbertTree.mp step1 h₂

end Cslib.Logic
