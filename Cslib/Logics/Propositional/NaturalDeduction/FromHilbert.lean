/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Metalogic.DeductionTheorem

/-! # Natural Deduction Rules as Hilbert Wrappers

This module provides ND-flavored lemma names as thin wrappers around the
Hilbert `DerivationTree` infrastructure, giving the familiar `impI`/`impE`/`botE`
interface. It also derives cut, weakening, and substitution within the
Hilbert framework.

All definitions are fixed at `PropositionalAxiom` (classical) since they use
classical axiom constructors directly (`.efq`, `.peirce`, `.implyK`, `.implyS`).

## Main Definitions

### Core ND Rules (Type-level)
- `impI`: Implication introduction (deduction theorem wrapper)
- `impE`: Implication elimination (modus ponens wrapper)
- `botE`: Ex falso quodlibet (EFQ axiom + modus ponens)
- `assume`: Assumption (context membership wrapper)
- `axiomRule`: Theory axiom (axiom schema wrapper)

### Derived Rules (Type-level)
- `hilbertCut`: Cut rule within the Hilbert framework
- `hilbertWeakening`: Explicit weakening

### Prop-level Versions
- `impIDeriv`, `impEDeriv`, `botEDeriv`, `hilbertCutDeriv`,
  `hilbertWeakeningDeriv`: `Deriv`-level versions of the above

## Design

These wrappers provide the familiar natural deduction interface while
being backed by the Hilbert derivation tree. This file coexists with
the standalone `NaturalDeduction/Basic.lean`.

## References

* Cslib/Logics/Propositional/NaturalDeduction/Basic.lean -- standalone ND system
* Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean -- deduction theorem
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic

variable {Atom : Type*}

/-! ## Core ND Rules (Type-level) -/

/-- **Implication Introduction** (→I): From `A :: Γ ⊢ B`, derive `Γ ⊢ A → B`.

This is the deduction theorem, presented with the familiar ND name.
Fixed at `PropositionalAxiom` (classical). -/
noncomputable def impI {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (d : DerivationTree PropositionalAxiom (A :: Γ) B) :
    DerivationTree PropositionalAxiom Γ (A.imp B) :=
  deductionTheorem
    (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
    Γ A B d

/-- **Implication Elimination** (→E / Modus Ponens):
From `Γ ⊢ A → B` and `Γ ⊢ A`, derive `Γ ⊢ B`. -/
def impE {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (d₁ : DerivationTree PropositionalAxiom Γ (A.imp B))
    (d₂ : DerivationTree PropositionalAxiom Γ A) :
    DerivationTree PropositionalAxiom Γ B :=
  DerivationTree.modus_ponens Γ A B d₁ d₂

/-- **Ex Falso Quodlibet** (⊥E): From `Γ ⊢ ⊥`, derive `Γ ⊢ A`.

Uses the EFQ axiom (`⊥ → A`) combined with modus ponens. -/
def botE {Γ : List (PL.Proposition Atom)}
    {A : PL.Proposition Atom}
    (d : DerivationTree PropositionalAxiom Γ Proposition.bot) :
    DerivationTree PropositionalAxiom Γ A :=
  DerivationTree.modus_ponens Γ Proposition.bot A
    (DerivationTree.weakening [] Γ _
      (DerivationTree.ax [] _ (.efq A))
      (fun _ h => nomatch h))
    d

/-- **Assumption**: If `φ ∈ Γ`, then `Γ ⊢ φ`. -/
def assume {Γ : List (PL.Proposition Atom)}
    {φ : PL.Proposition Atom}
    (h : φ ∈ Γ) :
    DerivationTree PropositionalAxiom Γ φ :=
  DerivationTree.assumption Γ φ h

/-- **Axiom Rule**: If `φ` is an axiom schema, then `Γ ⊢ φ`. -/
def axiomRule {Γ : List (PL.Proposition Atom)}
    {φ : PL.Proposition Atom}
    (h : PropositionalAxiom φ) :
    DerivationTree PropositionalAxiom Γ φ :=
  DerivationTree.ax Γ φ h

/-! ## Derived Rules (Type-level) -/

/-- **Cut Rule**: From `Γ ⊢ A` and `A :: Δ ⊢ B`, derive `Γ ++ Δ ⊢ B`.

Uses the deduction theorem to discharge `A` from the second derivation,
then modus ponens with the first, combined via weakening. -/
noncomputable def hilbertCut {Γ Δ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (d₁ : DerivationTree PropositionalAxiom Γ A)
    (d₂ : DerivationTree PropositionalAxiom (A :: Δ) B) :
    DerivationTree PropositionalAxiom (Γ ++ Δ) B := by
  -- Deduction theorem: Δ ⊢ A → B
  have h_dt := deductionTheorem
    (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
    Δ A B d₂
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
def hilbertWeakening {Γ Δ : List (PL.Proposition Atom)}
    {φ : PL.Proposition Atom}
    (d : DerivationTree PropositionalAxiom Γ φ)
    (h : ∀ x ∈ Γ, x ∈ Δ) :
    DerivationTree PropositionalAxiom Δ φ :=
  DerivationTree.weakening Γ Δ φ d h

/-! ## Prop-level (`Deriv`) Versions -/

/-- Implication introduction at the `Deriv` level. -/
theorem impIDeriv {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (h : Deriv PropositionalAxiom (A :: Γ) B) :
    Deriv PropositionalAxiom Γ (A.imp B) := by
  obtain ⟨d⟩ := h
  exact ⟨impI d⟩

/-- Implication elimination at the `Deriv` level. -/
theorem impEDeriv {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (h₁ : Deriv PropositionalAxiom Γ (A.imp B))
    (h₂ : Deriv PropositionalAxiom Γ A) :
    Deriv PropositionalAxiom Γ B := by
  obtain ⟨d₁⟩ := h₁; obtain ⟨d₂⟩ := h₂
  exact ⟨impE d₁ d₂⟩

/-- Ex falso quodlibet at the `Deriv` level. -/
theorem botEDeriv {Γ : List (PL.Proposition Atom)}
    {A : PL.Proposition Atom}
    (h : Deriv PropositionalAxiom Γ Proposition.bot) :
    Deriv PropositionalAxiom Γ A := by
  obtain ⟨d⟩ := h
  exact ⟨botE d⟩

/-- Cut rule at the `Deriv` level. -/
theorem hilbertCutDeriv
    {Γ Δ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (h₁ : Deriv PropositionalAxiom Γ A)
    (h₂ : Deriv PropositionalAxiom (A :: Δ) B) :
    Deriv PropositionalAxiom (Γ ++ Δ) B := by
  obtain ⟨d₁⟩ := h₁; obtain ⟨d₂⟩ := h₂
  exact ⟨hilbertCut d₁ d₂⟩

/-- Weakening at the `Deriv` level. -/
theorem hilbertWeakeningDeriv
    {Γ Δ : List (PL.Proposition Atom)}
    {φ : PL.Proposition Atom}
    (h : Deriv PropositionalAxiom Γ φ) (hsub : ∀ x ∈ Γ, x ∈ Δ) :
    Deriv PropositionalAxiom Δ φ := by
  obtain ⟨d⟩ := h
  exact ⟨hilbertWeakening d hsub⟩

/-! ## Substitution -/

/-- Helper: axiom schemata are preserved under substitution. -/
theorem subst_preserves_axiom
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
def hilbertSubstitution
    {Atom : Type u} {Atom' : Type u} [DecidableEq Atom']
    {Γ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (d : DerivationTree PropositionalAxiom Γ φ) (f : Atom → PL.Proposition Atom') :
    DerivationTree PropositionalAxiom (Γ.map (·.subst f)) (φ.subst f) :=
  match d with
  | .ax Γ' _ h_ax =>
    .ax (Γ'.map (·.subst f)) _ (subst_preserves_axiom h_ax f)
  | .assumption _ ψ h_mem =>
    .assumption _ _ (List.mem_map.mpr ⟨ψ, h_mem, rfl⟩)
  | .modus_ponens _ _ _ d₁ d₂ =>
    .modus_ponens _ _ _ (hilbertSubstitution d₁ f) (hilbertSubstitution d₂ f)
  | .weakening _ _ _ d' h_sub =>
    .weakening _ _ _ (hilbertSubstitution d' f) (fun _ hx =>
      let ⟨y, hy_mem, hy_eq⟩ := List.mem_map.mp hx
      List.mem_map.mpr ⟨y, h_sub y hy_mem, hy_eq⟩)

/-- Substitution at the `Deriv` level. -/
theorem hilbertSubstitutionDeriv
    {Atom : Type u} {Atom' : Type u} [DecidableEq Atom']
    {Γ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (h : Deriv PropositionalAxiom Γ φ) (f : Atom → PL.Proposition Atom') :
    Deriv PropositionalAxiom (Γ.map (·.subst f)) (φ.subst f) := by
  obtain ⟨d⟩ := h
  exact ⟨hilbertSubstitution d f⟩

end Cslib.Logic.PL
