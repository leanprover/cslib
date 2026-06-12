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

All definitions are parameterized over a generic axiom predicate `Axioms`, with
explicit axiom parameters (`h_K`, `h_S`, `h_EFQ`) following the pattern established
by `deductionTheorem` in `DeductionTheorem.lean`.

## Main Definitions

### Core ND Rules (Type-level)
- `impI`: Implication introduction (deduction theorem wrapper, needs K + S)
- `impE`: Implication elimination (modus ponens wrapper, no axiom params)
- `botE`: Ex falso quodlibet (needs EFQ)
- `assume`: Assumption (context membership wrapper, no axiom params)
- `axiomRule`: Theory axiom (axiom schema wrapper, no axiom params)

### Derived Rules (Type-level)
- `hilbertCut`: Cut rule within the Hilbert framework (needs K + S)
- `hilbertWeakening`: Explicit weakening (no axiom params)

### Substitution
- `subst_preserves_axiom`: Substitution preserves `PropositionalAxiom`
- `subst_preserves_intAxiom`: Substitution preserves `IntPropAxiom`
- `subst_preserves_minAxiom`: Substitution preserves `MinPropAxiom`
- `hilbertSubstitution`: Generic substitution (needs substitution-closure witness)

### Prop-level Versions
- `impIDeriv`, `impEDeriv`, `botEDeriv`, `hilbertCutDeriv`,
  `hilbertWeakeningDeriv`, `hilbertSubstitutionDeriv`: `Deriv`-level versions

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
Parameterized over `Axioms` with explicit K and S axiom witnesses. -/
noncomputable def impI
    {Axioms : PL.Proposition Atom → Prop}
    (h_K : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_S : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (d : DerivationTree Axioms (A :: Γ) B) :
    DerivationTree Axioms Γ (A → B) :=
  deductionTheorem h_K h_S Γ A B d

/-- **Implication Elimination** (→E / Modus Ponens):
From `Γ ⊢ A → B` and `Γ ⊢ A`, derive `Γ ⊢ B`. -/
def impE
    {Axioms : PL.Proposition Atom → Prop}
    {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (d₁ : DerivationTree Axioms Γ (A → B))
    (d₂ : DerivationTree Axioms Γ A) :
    DerivationTree Axioms Γ B :=
  DerivationTree.modus_ponens Γ A B d₁ d₂

/-- **Ex Falso Quodlibet** (⊥E): From `Γ ⊢ ⊥`, derive `Γ ⊢ A`.

Uses the EFQ axiom (`⊥ → A`) combined with modus ponens.
Parameterized over `Axioms` with an explicit EFQ axiom witness. -/
def botE
    {Axioms : PL.Proposition Atom → Prop}
    (h_EFQ : ∀ (φ : PL.Proposition Atom), Axioms (Proposition.bot.imp φ))
    {Γ : List (PL.Proposition Atom)}
    {A : PL.Proposition Atom}
    (d : DerivationTree Axioms Γ ⊥) :
    DerivationTree Axioms Γ A :=
  DerivationTree.modus_ponens Γ ⊥ A
    (DerivationTree.weakening [] Γ _
      (DerivationTree.ax [] _ (h_EFQ A))
      (fun _ h => nomatch h))
    d

/-- **Assumption**: If `φ ∈ Γ`, then `Γ ⊢ φ`. -/
def assume
    {Axioms : PL.Proposition Atom → Prop}
    {Γ : List (PL.Proposition Atom)}
    {φ : PL.Proposition Atom}
    (h : φ ∈ Γ) :
    DerivationTree Axioms Γ φ :=
  DerivationTree.assumption Γ φ h

/-- **Axiom Rule**: If `φ` satisfies the axiom predicate, then `Γ ⊢ φ`. -/
def axiomRule
    {Axioms : PL.Proposition Atom → Prop}
    {Γ : List (PL.Proposition Atom)}
    {φ : PL.Proposition Atom}
    (h : Axioms φ) :
    DerivationTree Axioms Γ φ :=
  DerivationTree.ax Γ φ h

/-! ## Derived Rules (Type-level) -/

/-- **Cut Rule**: From `Γ ⊢ A` and `A :: Δ ⊢ B`, derive `Γ ++ Δ ⊢ B`.

Uses the deduction theorem to discharge `A` from the second derivation,
then modus ponens with the first, combined via weakening.
Parameterized over `Axioms` with explicit K and S axiom witnesses. -/
noncomputable def hilbertCut
    {Axioms : PL.Proposition Atom → Prop}
    (h_K : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_S : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    {Γ Δ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (d₁ : DerivationTree Axioms Γ A)
    (d₂ : DerivationTree Axioms (A :: Δ) B) :
    DerivationTree Axioms (Γ ++ Δ) B := by
  -- Deduction theorem: Δ ⊢ A → B
  have h_dt := deductionTheorem h_K h_S Δ A B d₂
  -- Weaken d₁ to Γ ++ Δ
  have h_d₁ := DerivationTree.weakening Γ (Γ ++ Δ) A d₁
    (fun x hx => List.mem_append.mpr (Or.inl hx))
  -- Weaken h_dt to Γ ++ Δ
  have h_dt' := DerivationTree.weakening Δ (Γ ++ Δ) (A → B) h_dt
    (fun x hx => List.mem_append.mpr (Or.inr hx))
  -- MP: (Γ ++ Δ) ⊢ B
  exact DerivationTree.modus_ponens (Γ ++ Δ) A B h_dt' h_d₁

/-- **Weakening**: From `Γ ⊢ φ` and `Γ ⊆ Δ`, derive `Δ ⊢ φ`.

Direct wrapper around the `DerivationTree.weakening` constructor. -/
def hilbertWeakening
    {Axioms : PL.Proposition Atom → Prop}
    {Γ Δ : List (PL.Proposition Atom)}
    {φ : PL.Proposition Atom}
    (d : DerivationTree Axioms Γ φ)
    (h : ∀ x ∈ Γ, x ∈ Δ) :
    DerivationTree Axioms Δ φ :=
  DerivationTree.weakening Γ Δ φ d h

/-! ## Prop-level (`Deriv`) Versions -/

/-- Implication introduction at the `Deriv` level. -/
theorem impIDeriv
    {Axioms : PL.Proposition Atom → Prop}
    (h_K : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_S : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (h : Deriv Axioms (A :: Γ) B) :
    Deriv Axioms Γ (A → B) := by
  obtain ⟨d⟩ := h
  exact ⟨impI h_K h_S d⟩

/-- Implication elimination at the `Deriv` level. -/
theorem impEDeriv
    {Axioms : PL.Proposition Atom → Prop}
    {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (h₁ : Deriv Axioms Γ (A → B))
    (h₂ : Deriv Axioms Γ A) :
    Deriv Axioms Γ B := by
  obtain ⟨d₁⟩ := h₁; obtain ⟨d₂⟩ := h₂
  exact ⟨impE d₁ d₂⟩

/-- Ex falso quodlibet at the `Deriv` level. -/
theorem botEDeriv
    {Axioms : PL.Proposition Atom → Prop}
    (h_EFQ : ∀ (φ : PL.Proposition Atom), Axioms (Proposition.bot.imp φ))
    {Γ : List (PL.Proposition Atom)}
    {A : PL.Proposition Atom}
    (h : Deriv Axioms Γ ⊥) :
    Deriv Axioms Γ A := by
  obtain ⟨d⟩ := h
  exact ⟨botE h_EFQ d⟩

/-- Cut rule at the `Deriv` level. -/
theorem hilbertCutDeriv
    {Axioms : PL.Proposition Atom → Prop}
    (h_K : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_S : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    {Γ Δ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (h₁ : Deriv Axioms Γ A)
    (h₂ : Deriv Axioms (A :: Δ) B) :
    Deriv Axioms (Γ ++ Δ) B := by
  obtain ⟨d₁⟩ := h₁; obtain ⟨d₂⟩ := h₂
  exact ⟨hilbertCut h_K h_S d₁ d₂⟩

/-- Weakening at the `Deriv` level. -/
theorem hilbertWeakeningDeriv
    {Axioms : PL.Proposition Atom → Prop}
    {Γ Δ : List (PL.Proposition Atom)}
    {φ : PL.Proposition Atom}
    (h : Deriv Axioms Γ φ) (hsub : ∀ x ∈ Γ, x ∈ Δ) :
    Deriv Axioms Δ φ := by
  obtain ⟨d⟩ := h
  exact ⟨hilbertWeakening d hsub⟩

/-! ## Substitution -/

/-- Helper: classical axiom schemata are preserved under substitution. -/
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

/-- Helper: intuitionistic axiom schemata are preserved under substitution. -/
theorem subst_preserves_intAxiom
    {Atom : Type u} {Atom' : Type u}
    {φ : PL.Proposition Atom}
    (h : IntPropAxiom φ) (f : Atom → PL.Proposition Atom') :
    IntPropAxiom (φ.subst f) := by
  cases h with
  | implyK a b => exact .implyK (a.subst f) (b.subst f)
  | implyS a b c => exact .implyS (a.subst f) (b.subst f) (c.subst f)
  | efq a => exact .efq (a.subst f)

/-- Helper: minimal axiom schemata are preserved under substitution. -/
theorem subst_preserves_minAxiom
    {Atom : Type u} {Atom' : Type u}
    {φ : PL.Proposition Atom}
    (h : MinPropAxiom φ) (f : Atom → PL.Proposition Atom') :
    MinPropAxiom (φ.subst f) := by
  cases h with
  | implyK a b => exact .implyK (a.subst f) (b.subst f)
  | implyS a b c => exact .implyS (a.subst f) (b.subst f) (c.subst f)

/-- Transport a derivation tree along an atom substitution.

If `Γ ⊢ φ` then `Γ.map (·.subst f) ⊢ φ.subst f`.
Parameterized over `Axioms` with a substitution-closure witness. -/
def hilbertSubstitution
    {Atom : Type u} {Atom' : Type u}
    {Axioms : PL.Proposition Atom → Prop}
    {Axioms' : PL.Proposition Atom' → Prop}
    (h_subst : ∀ {φ : PL.Proposition Atom}, Axioms φ →
      ∀ (f : Atom → PL.Proposition Atom'), Axioms' (φ.subst f))
    {Γ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (d : DerivationTree Axioms Γ φ) (f : Atom → PL.Proposition Atom') :
    DerivationTree Axioms' (Γ.map (·.subst f)) (φ.subst f) :=
  match d with
  | .ax Γ' _ h_ax =>
    .ax (Γ'.map (·.subst f)) _ (h_subst h_ax f)
  | .assumption _ ψ h_mem =>
    .assumption _ _ (List.mem_map.mpr ⟨ψ, h_mem, rfl⟩)
  | .modus_ponens _ _ _ d₁ d₂ =>
    .modus_ponens _ _ _ (hilbertSubstitution h_subst d₁ f) (hilbertSubstitution h_subst d₂ f)
  | .weakening _ _ _ d' h_sub =>
    .weakening _ _ _ (hilbertSubstitution h_subst d' f) (fun _ hx =>
      let ⟨y, hy_mem, hy_eq⟩ := List.mem_map.mp hx
      List.mem_map.mpr ⟨y, h_sub y hy_mem, hy_eq⟩)

/-- Substitution at the `Deriv` level. -/
theorem hilbertSubstitutionDeriv
    {Atom : Type u} {Atom' : Type u}
    {Axioms : PL.Proposition Atom → Prop}
    {Axioms' : PL.Proposition Atom' → Prop}
    (h_subst : ∀ {φ : PL.Proposition Atom}, Axioms φ →
      ∀ (f : Atom → PL.Proposition Atom'), Axioms' (φ.subst f))
    {Γ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (h : Deriv Axioms Γ φ) (f : Atom → PL.Proposition Atom') :
    Deriv Axioms' (Γ.map (·.subst f)) (φ.subst f) := by
  obtain ⟨d⟩ := h
  exact ⟨hilbertSubstitution h_subst d f⟩

end Cslib.Logic.PL
