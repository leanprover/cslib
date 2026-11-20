/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module

public import Cslib.Init
public import Mathlib.Order.Closure

/-! # Consequence relations

Set-based consequence relations in the sense of Tarski: relations between sets of premises and
conclusions in which every premise is a consequence, and consequences of consequences are
consequences. The interface is stated for an arbitrary relation, so that the same propositions can
carry several consequence relations, semantic or proof-theoretic.

Premises are sets, so the interface does not cover substructural logics, whose contexts are
multisets or lists and whose cut is sensitive to resources.

## Main definitions

- `Cslib.Logic.IsConsequence`: set-based consequence relations.
- `Cslib.Logic.IsConsequence.closure`: the consequences of a set of premises, as a closure
  operator.

## Main results

- `Cslib.Logic.IsConsequence.mono`: weakening.
- `Cslib.Logic.IsConsequence.equivalence`: mutual consequence is an equivalence relation.
-/

@[expose] public section

namespace Cslib.Logic

variable {α : Type*}

/-- Set-based consequence relations: every premise is a consequence, and consequences of
consequences are consequences. Weakening follows (`IsConsequence.mono`). -/
class IsConsequence (R : Set α → α → Prop) : Prop where
  /-- Every premise is a consequence. -/
  of_mem {Γ : Set α} {φ : α} : φ ∈ Γ → R Γ φ
  /-- Cut: if every premise in `Δ` is a consequence of `Γ`, so is every consequence of `Δ`. -/
  trans {Γ Δ : Set α} {φ : α} : (∀ ψ ∈ Δ, R Γ ψ) → R Δ φ → R Γ φ

namespace IsConsequence

variable {R : Set α → α → Prop} [IsConsequence R]

/-- Weakening: consequence is preserved by adding premises. -/
theorem mono {Γ Δ : Set α} {φ : α} (h : R Γ φ) (hΓΔ : Γ ⊆ Δ) : R Δ φ :=
  trans (fun _ hψ => of_mem (hΓΔ hψ)) h

variable (R) in
/-- The consequences of a set of premises, as a closure operator. -/
def closure : ClosureOperator (Set α) :=
  ClosureOperator.mk' (fun Γ => {φ | R Γ φ})
    (fun _ _ h _ (hφ : R _ _) => mono (R := R) hφ h)
    (fun _ _ h => of_mem (R := R) h)
    (fun _ _ (hφ : R _ _) => trans (R := R) (fun _ hψ => hψ) hφ)

@[simp]
theorem mem_closure {Γ : Set α} {φ : α} : φ ∈ IsConsequence.closure R Γ ↔ R Γ φ := Iff.rfl

/-- Mutual consequence is an equivalence relation. -/
theorem equivalence : Equivalence fun φ ψ : α => R {φ} ψ ∧ R {ψ} φ where
  refl _ := ⟨of_mem rfl, of_mem rfl⟩
  symm h := h.symm
  trans h₁ h₂ :=
    ⟨trans (R := R) (fun _ h => Set.mem_singleton_iff.mp h ▸ h₁.1) h₂.1,
      trans (R := R) (fun _ h => Set.mem_singleton_iff.mp h ▸ h₂.2) h₁.2⟩

end IsConsequence

end Cslib.Logic
