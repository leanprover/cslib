/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Semantics.Truth
public import Cslib.Logics.Bimodal.Syntax.Context
public import Mathlib.Order.SuccPred.Basic
public import Mathlib.Order.SuccPred.Archimedean

/-!
# Validity - Semantic Validity and Consequence

This module defines semantic validity and consequence for TM formulas.

## Main Definitions

- `valid`: A formula is valid if true in all models
- `semanticConsequence`: Semantic consequence relation
- `satisfiable`: Context satisfiability
- Notation: `⊨ φ` for validity, `Γ ⊨ φ` for semantic consequence

## Main Results

- Basic validity lemmas
- Relationship between validity and semantic consequence
- Validity reduction lemmas for G, H, □

## Note on Variable Naming

Frame variables use `ℱ` rather than `F` because `F` is a scoped
notation for `Formula.someFuture` within `Cslib.Logic.Bimodal`.
-/

@[expose] public section

namespace Cslib.Logic.Bimodal

/--
A formula is valid if it is true in all models at all times in all
histories within any shift-closed set of histories, for every
temporal type `D`.

Note: Uses `Type` (not `Type*`) to avoid universe level issues.
-/
def valid (φ : Formula Atom) : Prop :=
  ∀ (D : Type) [AddCommGroup D] [LinearOrder D]
    [IsOrderedAddMonoid D] [Nontrivial D]
    (ℱ : TaskFrame D) (M : TaskModel Atom ℱ)
    (Omega : Set (WorldHistory ℱ)) (_ : ShiftClosed Omega)
    (τ : WorldHistory ℱ) (_ : τ ∈ Omega) (t : D),
    truthAt M Omega τ t φ

/--
Notation for validity: `⊨ φ` means `valid φ`.
-/
notation:50 "⊨ " φ:50 => valid φ

/--
Semantic consequence: `Γ ⊨ φ` means φ is true in all models where
all of `Γ` are true, for every temporal type `D`.

Note: Uses `Type` (not `Type*`) to avoid universe level issues.
-/
def semanticConsequence (Γ : Context Atom) (φ : Formula Atom) :
    Prop :=
  ∀ (D : Type) [AddCommGroup D] [LinearOrder D]
    [IsOrderedAddMonoid D] [Nontrivial D]
    (ℱ : TaskFrame D) (M : TaskModel Atom ℱ)
    (Omega : Set (WorldHistory ℱ)) (_ : ShiftClosed Omega)
    (τ : WorldHistory ℱ) (_ : τ ∈ Omega) (t : D),
    (∀ ψ ∈ Γ, truthAt M Omega τ t ψ) →
    truthAt M Omega τ t φ

/--
Notation for semantic consequence: `Γ ⊨ φ`.
-/
notation:50 Γ:50 " ⊨ " φ:50 => semanticConsequence Γ φ

/--
A context is satisfiable in temporal type `D` if there exists a
model where all formulas in the context are true.
-/
def satisfiable (D : Type*) [AddCommGroup D] [LinearOrder D]
    [IsOrderedAddMonoid D] (Γ : Context Atom) : Prop :=
  ∃ (ℱ : TaskFrame D) (M : TaskModel Atom ℱ)
    (Omega : Set (WorldHistory ℱ))
    (τ : WorldHistory ℱ) (_ : τ ∈ Omega) (t : D),
    ∀ φ ∈ Γ, truthAt M Omega τ t φ

/--
A context is absolutely satisfiable if it is satisfiable in some
temporal type.
-/
def satisfiableAbs (Γ : Context Atom) : Prop :=
  ∃ (D : Type) (_ : AddCommGroup D) (_ : LinearOrder D)
    (_ : IsOrderedAddMonoid D), satisfiable D Γ

/--
A single formula is satisfiable if there exists a model where it is
true at some point.
-/
def formulaSatisfiable (φ : Formula Atom) : Prop :=
  ∃ (D : Type) (_ : AddCommGroup D) (_ : LinearOrder D)
    (_ : IsOrderedAddMonoid D)
    (ℱ : TaskFrame D) (M : TaskModel Atom ℱ)
    (Omega : Set (WorldHistory ℱ))
    (τ : WorldHistory ℱ) (_ : τ ∈ Omega) (t : D),
    truthAt M Omega τ t φ

/--
A formula is valid over dense temporal orders.
-/
def validDense (φ : Formula Atom) : Prop :=
  ∀ (D : Type) [AddCommGroup D] [LinearOrder D]
    [IsOrderedAddMonoid D] [DenselyOrdered D]
    [Nontrivial D]
    (ℱ : TaskFrame D) (M : TaskModel Atom ℱ)
    (Omega : Set (WorldHistory ℱ)) (_ : ShiftClosed Omega)
    (τ : WorldHistory ℱ) (_ : τ ∈ Omega) (t : D),
    truthAt M Omega τ t φ

/--
A formula is valid over discrete temporal orders.
-/
def validDiscrete (φ : Formula Atom) : Prop :=
  ∀ (D : Type) [AddCommGroup D] [LinearOrder D]
    [IsOrderedAddMonoid D] [SuccOrder D] [PredOrder D]
    [IsSuccArchimedean D] [IsPredArchimedean D]
    [Nontrivial D]
    (ℱ : TaskFrame D) (M : TaskModel Atom ℱ)
    (Omega : Set (WorldHistory ℱ)) (_ : ShiftClosed Omega)
    (τ : WorldHistory ℱ) (_ : τ ∈ Omega) (t : D),
    truthAt M Omega τ t φ

namespace Validity

variable {Atom : Type*}

/--
Validity implies validity over dense orders.
-/
theorem valid_implies_valid_dense {φ : Formula Atom}
    (h : valid φ) : validDense φ := by
  intro D _ _ _ _ _ ℱ M Omega h_sc τ h_mem t
  exact h D ℱ M Omega h_sc τ h_mem t

/--
Validity implies validity over discrete orders.
-/
theorem valid_implies_valid_discrete {φ : Formula Atom}
    (h : valid φ) : validDiscrete φ :=
  fun D _ _ _ _ _ _ _ _ ℱ M Omega h_sc τ h_mem t =>
    h D ℱ M Omega h_sc τ h_mem t

/--
Valid formulas are semantic consequences of empty context.
-/
theorem valid_iff_empty_consequence (φ : Formula Atom) :
    (⊨ φ) ↔ ([] ⊨ φ) := by
  constructor
  · intro h D _ _ _ _ ℱ M Omega h_sc τ h_mem t _
    exact h D ℱ M Omega h_sc τ h_mem t
  · intro h D _ _ _ _ ℱ M Omega h_sc τ h_mem t
    exact h D ℱ M Omega h_sc τ h_mem t
      (by intro ψ hψ; exact absurd hψ List.not_mem_nil)

/--
Semantic consequence is monotonic.
-/
theorem consequence_monotone {Γ Δ : Context Atom}
    {φ : Formula Atom} :
    Γ ⊆ Δ → (Γ ⊨ φ) → (Δ ⊨ φ) := by
  intro h_sub h_cons D _ _ _ _ ℱ M Omega h_sc τ
    h_mem t h_delta
  apply h_cons D ℱ M Omega h_sc τ h_mem t
  intro ψ hψ
  exact h_delta ψ (h_sub hψ)

/--
If a formula is valid, it is a consequence of any context.
-/
theorem valid_consequence (φ : Formula Atom)
    (Γ : Context Atom) :
    (⊨ φ) → (Γ ⊨ φ) :=
  fun h D _ _ _ _ ℱ M Omega h_sc τ h_mem t _ =>
    h D ℱ M Omega h_sc τ h_mem t

/--
Context with all formulas true implies each formula individually
true.
-/
theorem consequence_of_member {Γ : Context Atom}
    {φ : Formula Atom} :
    φ ∈ Γ → (Γ ⊨ φ) := by
  intro h _ _ _ _ _ ℱ M Omega h_sc τ h_mem t h_all
  exact h_all φ h

/--
Unsatisfiable context (in ALL temporal types) semantically implies
anything.
-/
theorem unsatisfiable_implies_all {Γ : Context Atom}
    {φ : Formula Atom} :
    (∀ (D : Type) [AddCommGroup D] [LinearOrder D]
      [IsOrderedAddMonoid D], ¬satisfiable D Γ) →
    (Γ ⊨ φ) :=
  fun h_unsat D _ _ _ _ ℱ M Omega _h_sc τ h_mem t
    h_all =>
    absurd ⟨ℱ, M, Omega, τ, h_mem, t, h_all⟩ (h_unsat D)

/--
Unsatisfiable context in a fixed temporal type implies consequence
in that type.
-/
theorem unsatisfiable_implies_all_fixed
    {D : Type*} [AddCommGroup D] [LinearOrder D]
    [IsOrderedAddMonoid D]
    {Γ : Context Atom} {φ : Formula Atom} :
    ¬satisfiable D Γ →
    ∀ (ℱ : TaskFrame D) (M : TaskModel Atom ℱ)
      (Omega : Set (WorldHistory ℱ))
        (_ : ShiftClosed Omega)
      (τ : WorldHistory ℱ) (_ : τ ∈ Omega)
      (t : D),
      (∀ ψ ∈ Γ, truthAt M Omega τ t ψ) →
        truthAt M Omega τ t φ := by
  intro h_unsat ℱ M Omega _h_sc τ h_mem t h_all
  exfalso
  apply h_unsat
  exact ⟨ℱ, M, Omega, τ, h_mem, t, h_all⟩

/-! ### Validity Reduction Lemmas -/

/--
If G(φ) is valid, then φ is valid.
-/
theorem valid_of_valid_allFuture {φ : Formula Atom}
    (h : valid (Formula.allFuture φ)) :
    valid φ := by
  intro D _ _ _ _ ℱ M Omega h_sc τ h_mem t
  have h_all := h D ℱ M Omega h_sc τ h_mem
  obtain ⟨r, hrt⟩ := exists_lt t
  have := h_all r
  simp only [Truth.future_iff] at this
  exact this t hrt

/--
If H(φ) is valid, then φ is valid.
-/
theorem valid_of_valid_allPast {φ : Formula Atom}
    (h : valid (Formula.allPast φ)) :
    valid φ := by
  intro D _ _ _ _ ℱ M Omega h_sc τ h_mem t
  have h_past := h D ℱ M Omega h_sc τ h_mem
  obtain ⟨s, hts⟩ := exists_gt t
  have := h_past s
  simp only [Truth.past_iff] at this
  exact this t hts

/--
If □φ is valid, then φ is valid.
-/
theorem valid_of_valid_box {φ : Formula Atom}
    (h : valid (Formula.box φ)) :
    valid φ := by
  intro D _ _ _ _ ℱ M Omega h_sc τ h_mem t
  exact h D ℱ M Omega h_sc τ h_mem t τ h_mem

end Validity

end Cslib.Logic.Bimodal
