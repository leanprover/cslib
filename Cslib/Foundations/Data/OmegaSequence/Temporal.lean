/-
Copyright (c) 2025 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import Cslib.Foundations.Data.OmegaSequence.Defs
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Temporal reasoning over infinite sequences.
-/

open Function Set Filter

namespace Cslib.ωSequence

variable {α : Type*}

/-- `Step p q` means that whenever `p` holds at a position in `xs`, `q` holds at the next position
in `xs`. -/
def Step (xs : ωSequence α) (p q : Set α) : Prop :=
  ∀ k, xs k ∈ p → xs (k + 1) ∈ q

/-- "`p` leads to `q`" means that whenever `p` holds at a position in `xs`, `q` holds at the same
or a later position in `xs`. -/
def LeadsTo (xs : ωSequence α) (p q : Set α) : Prop :=
  ∀ k, xs k ∈ p → ∃ k' ≥ k, xs k' ∈ q

variable {xs : ωSequence α}

/-- `Step` implies `LeadsTo`. -/
theorem step_leadsTo {p q : Set α}
    (h : xs.Step p q) : xs.LeadsTo p q := by
  intro k h_p
  have := h k h_p
  grind

/-- `LeadsTo` is transitive. -/
theorem leadsTo_trans {p q r : Set α}
    (h1 : xs.LeadsTo p q) (h2 : xs.LeadsTo q r) : xs.LeadsTo p r := by
  intro k h_p
  obtain ⟨k', _, h_q⟩ := h1 k h_p
  have := h2 k' h_q
  grind

/-- If `p ∩ q` leads to `r` and `p ∩ qᶜ` leads to `s`, then `p` leads to `r ∪ s`. -/
theorem leadsTo_cases_or {p q r s : Set α}
    (h1 : xs.LeadsTo (p ∩ q) r) (h2 : xs.LeadsTo (p ∩ qᶜ) s) : xs.LeadsTo p (r ∪ s) := by
  intro k h_p
  rcases Classical.em (xs k ∈ q) with h_q | h_not_q
  · have h_pq : xs k ∈ p ∩ q := by grind
    have := h1 k h_pq
    grind
  · have h_pq : xs k ∈ p ∩ qᶜ := by grind
    have := h2 k h_pq
    grind

private lemma ge_lemma {k k' : ℕ} (h : k' ≥ k) : ∃ n, k' = k + n :=
  ⟨k' - k, by omega⟩

/-- If `p` holds until `q` and `p` fails infinitely often, then `p` leads to `q`. -/
theorem until_frequently_not_leadsTo {p q : Set α}
    (h1 : xs.Step (p ∩ qᶜ) p) (h2 : ∃ᶠ k in atTop, xs k ∉ p) : xs.LeadsTo p q := by
  intro k h_p
  by_contra! h_q
  suffices ∀ k' ≥ k, xs k' ∈ p by
    have := frequently_atTop.mp h2 k
    grind
  intro k' h_k'
  obtain ⟨n, rfl⟩ := ge_lemma h_k'
  induction n
  case zero => grind
  case succ n h_ind =>
    have h_pq_n : xs (k + n) ∈ p ∩ qᶜ := by grind
    exact h1 (k + n) h_pq_n

/-- If `p` holds until `q` and `q` holds infinite often, then `p` leads to `p ∩ q`. -/
theorem until_frequently_leadsTo_and {p q : Set α}
    (h1 : xs.Step (p ∩ qᶜ) p) (h2 : ∃ᶠ k in atTop, xs k ∈ q) : xs.LeadsTo p (p ∩ q) := by
  intro k h_p
  by_contra! h_not_pq
  suffices ∀ k' ≥ k, xs k' ∈ p ∩ qᶜ by
    have := frequently_atTop.mp h2 k
    grind
  intro k' h_k'
  obtain ⟨n, rfl⟩ := ge_lemma h_k'
  induction n
  case zero => grind
  case succ n h_ind =>
    have := h1 (k + n) <| h_ind (by omega)
    grind

/-- If `p` holds infinitely often and `p` leads to `q`, then `q` holds infinite often as well. -/
theorem frequently_leadsTo_frequently {p q : Set α}
    (h1 : ∃ᶠ k in atTop, xs k ∈ p) (h2 : xs.LeadsTo p q) : ∃ᶠ k in atTop, xs k ∈ q := by
  rw [frequently_atTop] at h1 ⊢
  intro k0
  obtain ⟨k1, _, h_k1_p⟩ := h1 k0
  have := h2 k1 h_k1_p
  grind

end Cslib.ωSequence
