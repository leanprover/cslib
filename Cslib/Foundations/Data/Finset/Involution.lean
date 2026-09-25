/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Init
public import Mathlib.Data.Finset.Card

/-! # Counting via involutions

If `σ` is an involution on a finset `s` and every orbit `{x, σ x}` meets a
predicate `p`, then at least half of `s` satisfies `p`. This is the
combinatorial core of pairing arguments such as the Ehrenfeucht–Haussler–
Kearns–Valiant lower bound on PAC sample complexity.

## Main statements

- `Finset.card_filter_not_le_card_filter_of_involution`: the elements of `s`
  failing `p` inject via `σ` into those satisfying `p`.
- `Finset.card_div_two_le_card_filter_of_involution`: at least half of `s`
  satisfies `p`.
-/

@[expose] public section

namespace Finset

variable {α : Type*} {s : Finset α} {σ : α → α} {p : α → Prop} [DecidablePred p]

/-- If `σ` is an involution on `s` and every orbit `{x, σ x}` meets `p`, then
`σ` injects the elements of `s` failing `p` into those satisfying `p`. -/
theorem card_filter_not_le_card_filter_of_involution
    (hσ : ∀ x ∈ s, σ (σ x) = x) (hσs : ∀ x ∈ s, σ x ∈ s)
    (hp : ∀ x ∈ s, p x ∨ p (σ x)) :
    #(s.filter fun x => ¬ p x) ≤ #(s.filter p) := by
  refine card_le_card_of_injOn σ ?_ ?_
  · intro x hx
    simp only [coe_filter, Set.mem_ofPred_eq] at hx ⊢
    exact ⟨hσs x hx.1, (hp x hx.1).resolve_left hx.2⟩
  · intro x hx y hy hxy
    simp only [coe_filter, Set.mem_ofPred_eq] at hx hy
    rw [← hσ x hx.1, hxy, hσ y hy.1]

/-- If `σ` is an involution on `s` and every orbit `{x, σ x}` meets `p`, then
at least half of `s` satisfies `p`. -/
theorem card_div_two_le_card_filter_of_involution
    (hσ : ∀ x ∈ s, σ (σ x) = x) (hσs : ∀ x ∈ s, σ x ∈ s)
    (hp : ∀ x ∈ s, p x ∨ p (σ x)) :
    #s / 2 ≤ #(s.filter p) := by
  have h₁ := card_filter_not_le_card_filter_of_involution hσ hσs hp
  have h₂ := card_filter_add_card_filter_not (s := s) p
  omega

end Finset
