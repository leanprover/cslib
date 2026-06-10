/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import Cslib.Logics.Propositional.Metalogic.DeductionTheorem

/-! # Natural Deduction Rules as Hilbert Wrappers

This module provides ND-flavored lemma names as thin wrappers around the
Hilbert `DerivationTree` infrastructure, giving the familiar `impI`/`impE`/`botE`
interface. It also derives cut, weakening, and substitution within the
Hilbert framework.

## Main Definitions

### Core ND Rules (Type-level)
- `impI`: Implication introduction (deduction theorem wrapper)
- `impE`: Implication elimination (modus ponens wrapper)
- `botE`: Ex falso quodlibet (EFQ axiom + modus ponens)
- `assume`: Assumption (context membership wrapper)
- `axiom_rule`: Theory axiom (axiom schema wrapper)

### Derived Rules (Type-level)
- `hilbert_cut`: Cut rule within the Hilbert framework
- `hilbert_weakening`: Explicit weakening

### Prop-level Versions
- `impI_deriv`, `impE_deriv`, `botE_deriv`, `hilbert_cut_deriv`,
  `hilbert_weakening_deriv`: `Deriv`-level versions of the above

## Design

These wrappers provide the familiar natural deduction interface while
being backed by the Hilbert derivation tree. This file coexists with
the standalone `NaturalDeduction/Basic.lean`.

## References

* Cslib/Logics/Propositional/NaturalDeduction/Basic.lean -- standalone ND system
* Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean -- deduction theorem
-/

namespace Cslib.Logic.PL

open Cslib.Logic

variable {Atom : Type*}

/-! ## Core ND Rules (Type-level) -/

/-- **Implication Introduction** (→I): From `A :: Γ ⊢ B`, derive `Γ ⊢ A → B`.

This is the deduction theorem, presented with the familiar ND name. -/
noncomputable def impI {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (d : DerivationTree (A :: Γ) B) :
    DerivationTree Γ (A.imp B) :=
  deduction_theorem Γ A B d

/-- **Implication Elimination** (→E / Modus Ponens):
From `Γ ⊢ A → B` and `Γ ⊢ A`, derive `Γ ⊢ B`. -/
def impE {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (d₁ : DerivationTree Γ (A.imp B))
    (d₂ : DerivationTree Γ A) :
    DerivationTree Γ B :=
  DerivationTree.modus_ponens Γ A B d₁ d₂

/-- **Ex Falso Quodlibet** (⊥E): From `Γ ⊢ ⊥`, derive `Γ ⊢ A`.

Uses the EFQ axiom (`⊥ → A`) combined with modus ponens. -/
def botE {Γ : List (PL.Proposition Atom)}
    {A : PL.Proposition Atom}
    (d : DerivationTree Γ Proposition.bot) :
    DerivationTree Γ A :=
  DerivationTree.modus_ponens Γ Proposition.bot A
    (DerivationTree.weakening [] Γ _
      (DerivationTree.ax [] _ (.efq A))
      (fun _ h => nomatch h))
    d

/-- **Assumption**: If `φ ∈ Γ`, then `Γ ⊢ φ`. -/
def assume {Γ : List (PL.Proposition Atom)}
    {φ : PL.Proposition Atom}
    (h : φ ∈ Γ) :
    DerivationTree Γ φ :=
  DerivationTree.assumption Γ φ h

/-- **Axiom Rule**: If `φ` is an axiom schema, then `Γ ⊢ φ`. -/
def axiom_rule {Γ : List (PL.Proposition Atom)}
    {φ : PL.Proposition Atom}
    (h : PropositionalAxiom φ) :
    DerivationTree Γ φ :=
  DerivationTree.ax Γ φ h

/-! ## Derived Rules (Type-level) -/

/-- **Cut Rule**: From `Γ ⊢ A` and `A :: Δ ⊢ B`, derive `Γ ++ Δ ⊢ B`.

Uses the deduction theorem to discharge `A` from the second derivation,
then modus ponens with the first, combined via weakening. -/
noncomputable def hilbert_cut {Γ Δ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (d₁ : DerivationTree Γ A)
    (d₂ : DerivationTree (A :: Δ) B) :
    DerivationTree (Γ ++ Δ) B := by
  -- Deduction theorem: Δ ⊢ A → B
  have h_dt := deduction_theorem Δ A B d₂
  -- Weaken d₁ to Γ ++ Δ
  have h_d₁ := DerivationTree.weakening Γ (Γ ++ Δ) A d₁
    (fun x hx => List.mem_append.mpr (Or.inl hx))
  -- Weaken h_dt to Γ ++ Δ
  have h_dt' := DerivationTree.weakening Δ (Γ ++ Δ) (A.imp B) h_dt
    (fun x hx => List.mem_append.mpr (Or.inr hx))
  -- MP: (Γ ++ Δ) ⊢ B
  exact DerivationTree.modus_ponens (Γ ++ Δ) A B h_dt' h_d₁

/-- **Weakening**: From `Γ ⊢ φ` and `Γ ⊆ Δ`, derive `Δ ⊢ φ`.

Direct wrapper around the `DerivationTree.weakening` constructor. -/
def hilbert_weakening {Γ Δ : List (PL.Proposition Atom)}
    {φ : PL.Proposition Atom}
    (d : DerivationTree Γ φ)
    (h : ∀ x ∈ Γ, x ∈ Δ) :
    DerivationTree Δ φ :=
  DerivationTree.weakening Γ Δ φ d h

/-! ## Prop-level (`Deriv`) Versions -/

/-- Implication introduction at the `Deriv` level. -/
noncomputable def impI_deriv {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (h : Deriv (A :: Γ) B) : Deriv Γ (A.imp B) := by
  obtain ⟨d⟩ := h
  exact ⟨impI d⟩

/-- Implication elimination at the `Deriv` level. -/
def impE_deriv {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (h₁ : Deriv Γ (A.imp B)) (h₂ : Deriv Γ A) :
    Deriv Γ B := by
  obtain ⟨d₁⟩ := h₁; obtain ⟨d₂⟩ := h₂
  exact ⟨impE d₁ d₂⟩

/-- Ex falso quodlibet at the `Deriv` level. -/
def botE_deriv {Γ : List (PL.Proposition Atom)}
    {A : PL.Proposition Atom}
    (h : Deriv Γ Proposition.bot) : Deriv Γ A := by
  obtain ⟨d⟩ := h
  exact ⟨botE d⟩

/-- Cut rule at the `Deriv` level. -/
noncomputable def hilbert_cut_deriv
    {Γ Δ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (h₁ : Deriv Γ A) (h₂ : Deriv (A :: Δ) B) :
    Deriv (Γ ++ Δ) B := by
  obtain ⟨d₁⟩ := h₁; obtain ⟨d₂⟩ := h₂
  exact ⟨hilbert_cut d₁ d₂⟩

/-- Weakening at the `Deriv` level. -/
def hilbert_weakening_deriv
    {Γ Δ : List (PL.Proposition Atom)}
    {φ : PL.Proposition Atom}
    (h : Deriv Γ φ) (hsub : ∀ x ∈ Γ, x ∈ Δ) :
    Deriv Δ φ := by
  obtain ⟨d⟩ := h
  exact ⟨hilbert_weakening d hsub⟩

/-! ## Substitution -/

/-- Helper: axiom schemata are preserved under substitution. -/
private theorem subst_preserves_axiom
    {Atom : Type u} {Atom' : Type u}
    {φ : PL.Proposition Atom}
    (h : PropositionalAxiom φ) (f : Atom → PL.Proposition Atom') :
    PropositionalAxiom (φ.subst f) := by
  cases h with
  | implyK a b => exact .implyK (a.subst f) (b.subst f)
  | implyS a b c => exact .implyS (a.subst f) (b.subst f) (c.subst f)
  | efq a => exact .efq (a.subst f)
  | peirce a b => exact .peirce (a.subst f) (b.subst f)

/-- Transport a derivation tree along an atom substitution.

If `Γ ⊢ φ` then `Γ.map (·.subst f) ⊢ φ.subst f`. -/
def hilbert_substitution
    {Atom : Type u} {Atom' : Type u} [DecidableEq Atom']
    {Γ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (d : DerivationTree Γ φ) (f : Atom → PL.Proposition Atom') :
    DerivationTree (Γ.map (·.subst f)) (φ.subst f) :=
  match d with
  | .ax Γ' _ h_ax =>
    .ax (Γ'.map (·.subst f)) _ (subst_preserves_axiom h_ax f)
  | .assumption _ ψ h_mem =>
    .assumption _ _ (List.mem_map.mpr ⟨ψ, h_mem, rfl⟩)
  | .modus_ponens _ _ _ d₁ d₂ =>
    .modus_ponens _ _ _ (hilbert_substitution d₁ f) (hilbert_substitution d₂ f)
  | .weakening _ _ _ d' h_sub =>
    .weakening _ _ _ (hilbert_substitution d' f) (fun _ hx =>
      let ⟨y, hy_mem, hy_eq⟩ := List.mem_map.mp hx
      List.mem_map.mpr ⟨y, h_sub y hy_mem, hy_eq⟩)

/-- Substitution at the `Deriv` level. -/
def hilbert_substitution_deriv
    {Atom : Type u} {Atom' : Type u} [DecidableEq Atom']
    {Γ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (h : Deriv Γ φ) (f : Atom → PL.Proposition Atom') :
    Deriv (Γ.map (·.subst f)) (φ.subst f) := by
  obtain ⟨d⟩ := h
  exact ⟨hilbert_substitution d f⟩

end Cslib.Logic.PL
