/-
Copyright (c) 2026 Sorrachai Yingchareonthawornhcai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trong-Nghia Be, Sorrachai Yingchareonthawornhcai
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Order.Defs.LinearOrder

@[expose] public section

/-!
# Shared Sorting Definitions

Common definitions used by sorting algorithm files.

## Main definitions

- `IsSortedAscending`: A list is sorted in ascending order if each element is less than or equal
to the next.
- `IsSortedDescending`: A list is sorted in descending order if each element is greater than or
equal to the next.
- `IsSorted`: A list is sorted if it is either sorted in ascending or descending order.
- `MinOfList`: `x` is a minimum element of a list if `x ≤ b` for all `b` in the list.
- `MaxOfList`: `x` is a maximum element of a list if `x ≥ b` for all `b` in the list.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

variable {α : Type} [LinearOrder α]

section Sortedness

/-- A list is sorted (ascending/increasing) if it satisfies the `Pairwise (· ≤ ·)` predicate.
-/
abbrev IsSortedAscending (l : List α) : Prop := List.Pairwise (· ≤ ·) l

/-- A list is sorted (descending/decreasing) if it satisfies the `Pairwise (· ≥ ·)` predicate.
-/
abbrev IsSortedDescending (l : List α) : Prop := List.Pairwise (· ≥ ·) l

/-- A list is strictly sorted (ascending/increasing)
if it satisfies the `Pairwise (· < ·)` predicate.
-/
abbrev IsStrictlySortedAscending (l : List α) : Prop := List.Pairwise (· < ·) l

/-- A list is strictly sorted (descending/decreasing)
if it satisfies the `Pairwise (· > ·)` predicate.
-/
abbrev IsStrictlySortedDescending (l : List α) : Prop := List.Pairwise (· > ·) l

/-- A list is sorted if it is either sorted in ascending or descending order.
-/
abbrev IsSorted (l : List α) : Prop := IsSortedAscending l ∨ IsSortedDescending l

/-- If a list is strictly sorted in ascending order, then it is also sorted in ascending order.
-/
theorem StrictlySortedAscendingImpliesSortedAscending (l : List α) :
    IsStrictlySortedAscending l → IsSortedAscending l := by
  intro h
  unfold IsStrictlySortedAscending at h
  unfold IsSortedAscending
  apply List.Pairwise.imp _ h
  intro a b hab
  exact le_of_lt hab

/-- If a list is strictly sorted in descending order, then it is also sorted in descending order.
-/
theorem StrictlySortedDescendingImpliesSortedDescending (l : List α) :
    IsStrictlySortedDescending l → IsSortedDescending l := by
  intro h
  unfold IsStrictlySortedDescending at h
  unfold IsSortedDescending
  apply List.Pairwise.imp _ h
  intro a b hab
  apply le_of_lt hab

/-- If a list is strictly sorted in either ascending or descending order, then it is also sorted.
-/
theorem StrictlySortedImpliesSorted (l : List α) :
    IsStrictlySortedAscending l ∨ IsStrictlySortedDescending l → IsSorted l := by
  intro h
  cases h with
  | inl hAsc =>
    exact Or.inl (StrictlySortedAscendingImpliesSortedAscending l hAsc)
  | inr hDesc =>
    exact Or.inr (StrictlySortedDescendingImpliesSortedDescending l hDesc)

end Sortedness

section Extrema

/-- `x` is a minimum element of list `l` if `x ≤ b` for all `b ∈ l`.
-/
abbrev MinOfList (x : α) (l : List α) : Prop := ∀ b ∈ l, x ≤ b

/-- `x` is a maximum element of list `l` if `x ≥ b` for all `b ∈ l`.
-/
abbrev MaxOfList (x : α) (l : List α) : Prop := ∀ b ∈ l, x ≥ b

end Extrema

end Cslib.Algorithms.Lean.TimeM
