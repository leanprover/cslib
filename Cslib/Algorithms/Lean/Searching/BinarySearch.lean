/-
Copyright (c) 2025 Sorrachai Yingchareonthawornhcai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornhcai
-/

import Cslib.Algorithms.Lean.TimeM
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.Nat.Log

/-!
# Binary Search on a sorted array

In this file we introduce `binarySearch` algorithm on `SortedArray` that returns a time monad
over `Option ℕ`, representing whether a key exists and its index if so. The time complexity
represents the number of array accesses.

## Main definitions

* `SortedArray`: A structure representing a sorted array with monotone access function.
  We model a sorted array as a function from Nat to a type equipped with a size
  and a sortedness property. This representation eliminates concerns about out-of-bounds indexing.
  With fewer proof obligations related to array indices, the analysis becomes significantly cleaner
  and more modular.
* `binarySearch`: Binary search algorithm that searches for a key in a sorted array
  and returns an index if the search is successful or none otherwise.

## Main results

* `binarySearch_correct`: Given a key `q`, `binarySearch` returns some index if and only if
  the array contains `q`. Furthermore, if `binarySearch` returns an index `i`, then `arr[i] = q`
* `binarySearch_time`: The number of array accesses is at most `⌊log₂(n-1)⌋ + 2`

-/

namespace Cslib.Algorithms.Lean.TimeM

set_option autoImplicit false
set_option tactic.hygienic false

variable {α : Type} [LinearOrder α]

/-- `SortedArray` represents a sorted array via a total access function.
    We model a sorted array as a function `ℕ → α` equipped with a logical size
    and a sortedness property. Indices outside the first `n` positions are
    intentionally left unconstrained, eliminating out-of-bounds concerns.
    This design substantially reduces index-related proof obligations,
    leading to cleaner and more modular algorithmic analysis. -/
structure SortedArray (α : Type) [LinearOrder α] (n : ℕ) where
  /-- Total access function for the array.
      The value at indices `i ≥ n` is arbitrary and irrelevant to correctness. -/
  get : ℕ → α
  /-- Logical size of the array, fixed to `n` for algorithmic analysis. -/
  size : ℕ := n
  /-- Monotonicity of the access function, expressing that the array is sorted. -/
  sorted : Monotone get

/-- Scoped notation for accessing elements of a `SortedArray`.
    Writing `a[i]` abbreviates `SortedArray.get a i`, avoiding explicit projections
    and improving readability in algorithm definitions such as `binarySearch`. -/
scoped notation a "[" i "]"  => SortedArray.get a i


variable {α : Type} [LinearOrder α]

/-- Binary search on a sorted array, counting array accesses as time cost.
Returns a `TimeM (Option ℕ)` where the time represents the number of array accesses,
and the result is `some i` if `arr[i] = q`, or `none` if `q` is not in the array. -/
def binarySearch {n : ℕ} (arr : SortedArray α n) (q : α) : TimeM (Option ℕ) :=
  bs_aux 0 (n-1)
  where
  /-- A helper function of binary search to run in range [a,b] -/
  bs_aux (a b : ℕ) (h: a ≤ b := by omega): TimeM (Option ℕ) := do
  if h: a = b then
    let arr_a ← ✓ (arr[a])
    if q = arr_a then return (some a)
    else return none
  else
    let mid := (a+b)/2
    let arr_mid ← ✓ (arr[mid])
    if q < arr_mid then
      bs_aux a mid
    else if arr_mid < q then
      bs_aux (mid+1) b
    else return (some mid)

section Correctness

/-- If `q < arr[mid]`, then any index containing `q` must be in the left subinterval. -/
private theorem subinterval_left {n : ℕ} (arr : SortedArray α n) (q : α) (a mid b : ℕ)
  (h_bounds : a ≤ mid ∧ mid ≤ b)
  (h_q : q < arr[mid]) :
  (∃ i, a ≤ i ∧ i ≤ b ∧ arr[i] = q) ↔ (∃ i, a ≤ i ∧ i ≤ mid ∧ arr[i] = q)  := by
  constructor
  · intro h'
    obtain ⟨i,hi⟩ := h'
    use i
    suffices  i ≤ mid by grind
    replace hi: arr[i] = q := by grind
    rw [← hi] at h_q
    have: Monotone arr.get := arr.sorted
    simp only [Monotone] at this
    by_contra h_con
    simp at h_con
    have h_con': mid ≤ i := by grind
    grind
  · grind

/-- If `arr[mid] < q`, then any index containing `q` must be in the right subinterval. -/
private theorem subinterval_right {n : ℕ} (arr : SortedArray α n) (q : α) (a mid b : ℕ)
  (h_bounds : a ≤ mid ∧ mid ≤ b)
  (h_q : arr[mid] < q) :
  (∃ i, a ≤ i ∧ i ≤ b ∧ arr[i] = q) ↔ (∃ i, (mid+1) ≤ i ∧ i ≤ b ∧ arr[i] = q)  := by
  constructor
  · intro h'
    obtain ⟨i,hi⟩ := h'
    use i
    suffices  mid ≤ i by grind
    replace hi: arr[i] = q := by grind
    rw [← hi] at h_q
    have: Monotone arr.get := arr.sorted
    simp only [Monotone] at this
    by_contra h_con
    simp at h_con
    have h_con': i ≤ mid := by grind
    grind
  · grind

/-- Binary search returns `some` if and only if the key exists in the array. -/
theorem binarySearch_some_iff (n : ℕ) (q : α) (h : 0 < n) (arr : SortedArray α n) :
  (∃ i, i < n ∧ arr[i] = q) ↔ ((binarySearch arr q).ret ≠ none) := by
  unfold binarySearch
  have := bs_correct_aux n q arr 0 (n-1) (by omega)
  grind
where bs_correct_aux (n : ℕ) (q : α) (arr : SortedArray α n) (a b : ℕ) (h_le : a ≤ b) :
(∃ i, a ≤ i ∧ i ≤ b ∧ arr[i] = q) ↔ ((binarySearch.bs_aux arr q a b h_le).ret ≠ none) := by {
    fun_induction binarySearch.bs_aux
    · simp only [Bind.bind, tick, Pure.pure, pure, ret_bind, ne_eq]
      split_ifs <;> grind
    · simp_all only [ne_eq, Bind.bind, tick, Pure.pure, pure, ret_bind]
      split_ifs <;> try grind
      · rw [← ih2]
        rw [subinterval_left arr q a_1 mid b_1 (by grind) (by grind)]
      · rw [← ih1]
        rw [subinterval_right arr q a_1 (mid) b_1 (by grind) (by grind)]
}

/-- If binary search returns an index, that index contains the search key. -/
private theorem binarySearch_index_correct (n : ℕ) (q : α) (arr : SortedArray α n) :
  ∀ i, (binarySearch arr q).ret = some i → arr[i] = q := by
    intro i hi
    apply aux n q 0 (n-1) (by omega)
    rw [binarySearch.eq_def] at hi
    exact hi
where aux (n : ℕ) (q : α) (a b : ℕ)
  (h_ab : a ≤ b) (arr : SortedArray α n) :
  ∀ i : ℕ, (binarySearch.bs_aux arr q a b h_ab).ret = some i → arr[i] = q := by {
    fun_induction binarySearch.bs_aux <;> all_goals (simp; split_ifs<;> grind)
  }


/-- Binary search is functionally correct. -/
theorem binarySearch_correct (n : ℕ) (q : α) (h : 0 < n) (arr : SortedArray α n) :
    ((∃ i, i < n ∧ arr[i] = q) ↔ (binarySearch arr q).ret ≠ none) ∧
    ∀ i, (binarySearch arr q).ret = some i → arr[i] = q :=
  ⟨binarySearch_some_iff n q h arr, binarySearch_index_correct n q arr⟩


end Correctness

section TimeComplexity


/-- Recurrence relation for the time complexity of binary search.
For a search range of size `n`, this counts the total number of array accesses:
- Base case: 0 accesses for empty range
- Recursive case: 1 access to check middle element, plus recursive search on half the range -/
def g (n : ℕ) : ℕ :=
  if n = 0 then 0
  else g (n/2) + 1

/-- Alternative formulation that's more convenient for functional induction. -/
private def g' (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if n = 1 then 1
  else g' (n/2) + 1

private theorem g'_eq_g : g' = g := by
  ext n
  fun_induction g' <;> grind [g]

/-- Upper bound for the recurrence in terms of logarithm. -/
private theorem g'_close_form (n : ℕ) : g' n ≤ (Nat.log 2 n) +1  := by
  fun_induction g'
  · simp only [Nat.log_zero_right, zero_add, zero_le]
  · simp only [Nat.log_one_right, zero_add, le_refl]
  · simp only [add_le_add_iff_right]
    grw [ih1]
    simp only [Nat.log_div_base]
    rw [Nat.sub_add_cancel ?_]
    (expose_names; rw [propext (Nat.le_log_iff_pow_le Nat.le.refl h)])
    grind

/-- The recurrence relation is monotone. -/
theorem g_monotone : Monotone g := by
  intro a b hab
  apply g_monotone_aux b (by omega) (by omega)
where g_monotone_aux {a b : ℕ} (n : ℕ) (hab : a ≤ b) (hn : b ≤ n) : g a ≤ g b := by {
  induction n using Nat.strong_induction_on generalizing a b
  unfold g
  split_ifs
  · simp only [le_refl]
  · simp only [le_add_iff_nonneg_left, zero_le]
  · simp_all only [nonpos_iff_eq_zero]
  · simp_all only [add_le_add_iff_right]
    expose_names
    apply a_1
    pick_goal 4
    · exact n_1/2
    all_goals omega
}

/-- Time complexity of binary search. -/
theorem binarySearch_time (n : ℕ) (q : α) (arr : SortedArray α n) :
  (binarySearch arr q).time ≤ Nat.log 2 (n-1) + 2 := by
  have:= bs_time_le_g n q arr 0 (n-1) (by omega)
  simp only [tsub_zero] at this
  simp only [binarySearch, ge_iff_le]
  grw [this]
  rw [← g'_eq_g]
  simp only [add_le_add_iff_right]
  exact g'_close_form (n - 1)
where bs_time_le_g (n : ℕ) (q : α) (arr : SortedArray α n) (a b : ℕ) (h_le : a ≤ b) :
  (binarySearch.bs_aux arr q a b).time ≤ g (b-a) + 1 := by {
  fun_induction binarySearch.bs_aux arr q a b
  · simp only [Bind.bind, tick, Pure.pure, pure, time_of_bind, tsub_self]
    split_ifs <;> grind
  · simp only [Bind.bind, tick, Pure.pure, pure, time_of_bind]
    rw [Nat.add_comm (g (b_1 - a_1)) 1]
    simp only [add_le_add_iff_left]
    split_ifs <;> try grind
    · grw [ih2]
      conv =>
        right
        unfold g
      split_ifs <;> grind
    · grw [ih1]
      have: b_1 - ((a_1 + b_1) / 2 + 1) ≤ (b_1 - a_1)/2  := by grind
      have gmono:= g_monotone
      simp [Monotone] at gmono
      conv =>
        right
        unfold g
      split_ifs <;> grind
}

end TimeComplexity

end Cslib.Algorithms.Lean.TimeM
