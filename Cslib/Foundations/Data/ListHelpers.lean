/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module
public import Cslib.Init

/-! # Shared List Helper Utilities

Shared `removeAll` definition and supporting lemmas used by all DeductionTheorem
files (Propositional, Modal, Temporal, Bimodal). Extracted to avoid duplication.

## Main Definitions

- `removeAll`: Remove all occurrences of an element from a list
- `removeAll_subset_of_subset`: If `A in Gamma'` and `Gamma' subs A :: Delta`,
  then `removeAll Gamma' A subs Delta`
- `mem_removeAll_of_mem_of_ne`: Membership in removeAll from membership and inequality
- `removeAll_subset_removeAll`: removeAll preserves subset relationships

## Aliases

- `removeAll_sub_of_sub`: Alias for `removeAll_subset_of_subset` using `List.Subset`
- `removeAll_sub_removeAll`: Alias for `removeAll_subset_removeAll` using `List.Subset`
-/

@[expose] public section

namespace Cslib.Logic.Helpers

/-- Remove all occurrences of `a` from a list. -/
def removeAll [DecidableEq α] (l : List α) (a : α) : List α :=
  l.filter (· ≠ a)

theorem removeAll_subset_of_subset [DecidableEq α] {A : α} {Γ' Δ : List α}
    (h_sub : ∀ x ∈ Γ', x ∈ A :: Δ) (h_mem : A ∈ Γ') :
    ∀ x ∈ removeAll Γ' A, x ∈ Δ := by
  intro x hx
  simp only [removeAll, ne_eq, decide_not, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not] at hx
  obtain ⟨hx_in, hx_ne⟩ := hx
  have := h_sub x hx_in
  simp only [List.mem_cons] at this
  rcases this with rfl | h
  · exact absurd rfl hx_ne
  · exact h

theorem mem_removeAll_of_mem_of_ne [DecidableEq α] {a x : α} {l : List α}
    (h_mem : x ∈ l) (h_ne : x ≠ a) : x ∈ removeAll l a := by
  simp only [removeAll, ne_eq, decide_not, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not]
  exact ⟨h_mem, h_ne⟩

theorem removeAll_subset_removeAll [DecidableEq α] {a : α} {l₁ l₂ : List α}
    (h : ∀ x ∈ l₁, x ∈ l₂) : ∀ x ∈ removeAll l₁ a, x ∈ removeAll l₂ a := by
  intro x hx
  simp only [removeAll, ne_eq, decide_not, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not] at hx ⊢
  exact ⟨h x hx.1, hx.2⟩

/-- Alias using `List.Subset` notation for `removeAll_subset_of_subset`. -/
theorem removeAll_sub_of_sub [DecidableEq α] {A : α} {Γ' Δ : List α}
    (h_sub : Γ' ⊆ A :: Δ) (h_mem : A ∈ Γ') :
    removeAll Γ' A ⊆ Δ :=
  removeAll_subset_of_subset h_sub h_mem

/-- Alias using `List.Subset` notation for `removeAll_subset_removeAll`. -/
theorem removeAll_sub_removeAll [DecidableEq α] {a : α} {l₁ l₂ : List α}
    (h : l₁ ⊆ l₂) : removeAll l₁ a ⊆ removeAll l₂ a :=
  removeAll_subset_removeAll h

end Cslib.Logic.Helpers
