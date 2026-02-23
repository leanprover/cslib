/-
Copyright (c) 2026 Trong-Nghia Be. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trong-Nghia Be
-/

module

public import Cslib.Algorithms.Lean.Sorting
public import Mathlib.Data.Nat.Cast.Order.Ring

@[expose] public section

/-!
# InsertionSort on a list

In this file we introduce `insert` and `insertionSort` algorithms that return a time monad
over the list `TimeM ℕ (List α)`. The time complexity of `insertionSort` is the number of
comparisons.

--
## Main results

- `insertionSort_correct`: `insertionSort` permutes the list into a sorted one.
- `insertionSort_time`: The number of comparisons of `insertionSort` is at most `(n * (n - 1)) / 2`.
- `insertionSort_time_worst_case`: In the worst case, the number of comparisons
is exactly `(n * (n - 1)) / 2`.
- `insertionSort_time_best_case`: In the best case, the number of comparisons
is `n - 1` for a non-empty list, and `0` for an empty list.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Cslib.Algorithms.Lean.TimeM

variable {α : Type} [LinearOrder α]

/-- Inserts an element `x` into a sorted list, counting comparisons as time cost.
Returns a `TimeM ℕ (List α)` where the time represents the number of comparisons performed.
-/
def insert (x : α) : List α → TimeM ℕ (List α)
  -- Base case: Inserting into an empty list just returns a singleton list with no comparisons.
  | [] => return [x]
  -- Recursive case: Compare `x` with the head `y` of the list,
  -- then recursively insert into the tail.
  | y :: ys => do
    -- Each comparison of `x` with `y` costs 1 unit of time.
    -- Define `c` as the result of the comparison, and charge for it.
    ✓ let c := (x ≤ y : Bool)
    -- If `x` is less than or equal to `y`, we can place `x` before `y` without further comparisons.
    if c then
      return (x :: y :: ys)
    -- Otherwise, we need to insert `x` into the tail `ys`, which may involve more comparisons.
    else
      let rest ← insert x ys
      return (y :: rest)

/-- Sorts a list using the `insertionSort` algorithm, counting comparisons as time cost.
Returns a `TimeM ℕ (List α)` where the time represents the total number of comparisons.
-/
def insertionSort : List α → TimeM ℕ (List α)
  -- Base case: An empty list is already sorted, so we return it with no time cost.
  | [] => return []
  -- Recursive case: Sort the tail of the list, then insert the head into the sorted tail.
  | x :: xs => do
    let sorted ← insertionSort xs
    insert x sorted

section Correctness

open List

/-- If `z` is in the result of inserting `x` into `ys`, then `z` is either `x`
or an element of `ys`.
-/
@[grind →]
theorem mem_insert_ret (x : α) (ys : List α) (z : α) (hz : z ∈ ⟪insert x ys⟫) :
    z = x ∨ z ∈ ys := by
  -- The proof proceeds by induction on the structure of the function `insert`.
  fun_induction insert x ys with
  -- Case 1: Inserting into an empty list.
  | case1 =>
    simp only [ret_pure] at hz
    exact Or.inl (List.mem_singleton.mp hz)
  -- Case 2: Inserting into a non-empty list `y :: ys`.
  | case2 =>
    grind

/-- If `ys` is a sorted list and `x` is inserted into `ys`, then the result is also sorted.
-/
theorem sorted_insert (x : α) (ys : List α) (hys : IsSortedAscending ys) :
    IsSortedAscending ⟪insert x ys⟫ := by
  -- The proof proceeds by induction on the structure of the function `insert`.
  fun_induction insert x ys with
  -- Case 1: Inserting into an empty list.
  | case1 =>
    simp [IsSortedAscending]
  -- Case 2: Inserting into a non-empty list `y :: ys`.
  | case2 =>
    grind [pairwise_cons]

/-- If `x` is inserted into a list `ys`, then the result is a permutation of `x :: ys`.
-/
theorem insert_perm (x : α) (ys : List α) :
    ⟪insert x ys⟫ ~ x :: ys := by
  -- The proof proceeds by induction on the structure of the function `insert`.
  fun_induction insert x ys with
  -- Case 1: Inserting into an empty list.
  | case1 =>
    simp [Perm.refl]
  -- Case 2: Inserting into a non-empty list `y :: ys`.
  | case2 =>
    simp only [ret_bind]
    grind

/-- If `insertionSort` is applied to a list `xs`, then the result is a sorted list.
-/
theorem insertionSort_sorted (xs : List α) :
    IsSortedAscending ⟪insertionSort xs⟫ := by
  -- The proof proceeds by induction on the structure of the function `insertionSort`.
  fun_induction insertionSort xs with
  -- Case 1: Sorting an empty list.
  | case1 =>
    simp [IsSortedAscending]
  -- Case 2: Sorting a non-empty list `x :: xs`.
  | case2 x xs ih =>
    simp only [ret_bind]
    exact sorted_insert _ _ ih

/-- If `insertionSort` is applied to a list `xs`, then the result is a permutation of `xs`.
-/
theorem insertionSort_perm (xs : List α) :
    ⟪insertionSort xs⟫ ~ xs := by
  -- The proof proceeds by induction on the structure of the function `insertionSort`.
  fun_induction insertionSort xs with
  -- Case 1: Sorting an empty list.
  | case1 =>
    simp
  -- Case 2: Sorting a non-empty list `x :: xs`.
  | case2 x xs ih =>
    simp only [ret_bind]
    exact (insert_perm _ _).trans (Perm.cons _ ih)

/-- Functional correctness of `insertionSort`.

If `insertionSort` is applied to a list `xs`, then the result is:
(1) a sorted list, and
(2) a permutation of `xs`.
-/
theorem insertionSort_correct (xs : List α) :
    let sorted_xs := ⟪insertionSort xs⟫
    IsSortedAscending sorted_xs ∧ sorted_xs ~ xs :=
  -- Combine the results of `insertionSort_sorted` and `insertionSort_perm` to conclude correctness.
  ⟨insertionSort_sorted xs, insertionSort_perm xs⟩

end Correctness

section TimeComplexity

open List

/-- Recurrence relation for the time complexity of `insertionSort`.

For a list of length `n`, this counts the worst-case total number of comparisons:
- Base case: 0 comparisons for an empty list.
- Recursive case: Sort the tail (cost `timeInsertionSortRec (n-1)`),
  then insert into the sorted tail (worst-case `n-1` comparisons).
-/
def timeInsertionSortRec : ℕ → ℕ
  | 0 => 0
  | n + 1 => timeInsertionSortRec n + n

/-- The recurrence solves to exactly `n*(n-1)/2`, stated without division. -/
theorem timeInsertionSortRec_eq (n : ℕ) :
    2 * timeInsertionSortRec n = n * (n - 1) := by
  -- The proof proceeds by induction on `n`.
  induction n with
  -- Base case: `n = 0`.
  | zero =>
    rfl
  -- Inductive case: Assume the statement holds for `n`, and prove it for `n + 1`.
  | succ n ih =>
    unfold timeInsertionSortRec
    cases n with
    | zero =>
      simp [timeInsertionSortRec]
    | succ m =>
      simp only [Nat.succ_sub_one] at ih ⊢
      rw [mul_add, ih, mul_comm 2 (m + 1), ← mul_add]
      exact mul_comm _ _

/-- Inserting an element `x` into a list `ys` results in a list with length
equal to `ys.length + 1`.
-/
@[simp]
theorem insert_ret_length (x : α) (ys : List α) :
    ⟪insert x ys⟫.length = ys.length + 1 := by
  -- The proof proceeds by induction on the structure of the function `insert`.
  fun_induction insert x ys with
  -- Case 1: Inserting into an empty list.
  | case1 =>
    simp
  -- Case 2: Inserting into a non-empty list `y :: ys`.
  | case2 =>
    grind

/-- If `x ≤ y`, inserting `x` into a list `ys` with head `y` results in a list
starting with `x`, followed by `y` and the rest of `ys`.
-/
@[simp]
theorem insert_ret_of_le (x y : α) (ys : List α) (h : x ≤ y) :
    ⟪insert x (y :: ys)⟫ = x :: y :: ys := by
  unfold insert
  simp [h]

/-- Applying `insertionSort` to a list `xs` results in a list with the same length as `xs`.
-/
@[simp]
theorem insertionSort_same_length (xs : List α) :
    ⟪insertionSort xs⟫.length = xs.length := by
  -- The proof proceeds by induction on the structure of the function `insertionSort`.
  fun_induction insertionSort with
  -- Case 1: Sorting an empty list.
  | case1 =>
    simp
  -- Case 2: Sorting a non-empty list `x :: xs`.
  | case2 =>
    grind [insert_ret_length]

/-- `insertionSort` acts as an identity function on already-sorted lists. -/
@[simp]
theorem insertionSort_eq_of_sorted (xs : List α) (h : IsSortedAscending xs) :
    ⟪insertionSort xs⟫ = xs := by
  induction xs with
  | nil =>
    simp [insertionSort]
  | cons x xs ih =>
    rw [IsSortedAscending, List.pairwise_cons] at h
    have h_head : ∀ y ∈ xs, x ≤ y := h.left
    have h_tail : IsSortedAscending xs := h.right
    unfold insertionSort
    simp only [ret_bind, ih h_tail]
    cases xs with
    | nil =>
      simp [insert]
    | cons y ys =>
      have h_x_le_y : x ≤ y := h_head y List.mem_cons_self
      simp [h_x_le_y]

/-- If two lists are permutations of each other, any element-wise property
that holds for all elements of the first list also holds for the second. -/
theorem forall_mem_of_perm {P : α → Prop} {l1 l2 : List α}
    (h_perm : l1 ~ l2) (h_forall : ∀ a ∈ l1, P a) :
    ∀ a ∈ l2, P a := by
  intro a ha
  have ha_in_l1 : a ∈ l1 := h_perm.mem_iff.mpr ha
  exact h_forall a ha_in_l1

/-- If `x` is inserted into a list `ys`, then the time taken is at most the length of `ys`.
-/
@[simp]
theorem insert_time (x : α) (ys : List α) :
    (insert x ys).time ≤ ys.length := by
  -- The proof proceeds by induction on the structure of the function `insert`.
  fun_induction insert x ys with
  -- Case 1: Inserting into an empty list.
  | case1 =>
    simp
  -- Case 2: Inserting into a non-empty list `y :: ys`.
  | case2 =>
    simp only [time_bind]
    grind

/-- If an element `x` is less than or equal to the head `y`, insertion takes exactly 1 comparison.
-/
@[simp]
theorem insert_time_of_le (x y : α) (ys : List α) (h : x ≤ y) :
    (insert x (y :: ys)).time = 1 := by
  unfold insert
  simp [h]

/-- If an element `x` is strictly greater than every element in `ys`,
insertion takes exactly `ys.length` comparisons.
-/
@[simp]
theorem insert_time_of_gt_all (x : α) (ys : List α) (h : ∀ y ∈ ys, x > y) :
    (insert x ys).time = ys.length := by
  induction ys with
  | nil =>
    simp [insert]
  | cons y ys ih =>
    have h_head : y < x := h y List.mem_cons_self
    have h_not_le : ¬(x ≤ y) := not_le_of_gt h_head
    have h_tail : ∀ y' ∈ ys, x > y' := fun y' hy' => h y' (List.mem_cons_of_mem _ hy')
    unfold insert
    simp [h_not_le, ih h_tail, add_comm]

/-- If `insertionSort` is applied to a list `xs`,
then the time taken is at most `timeInsertionSortRec xs.length`.
-/
theorem insertionSort_time_le (xs : List α) :
    (insertionSort xs).time ≤ timeInsertionSortRec xs.length := by
  -- The proof proceeds by induction on the structure of the function `insertionSort`.
  fun_induction insertionSort with
  -- Case 1: Sorting an empty list.
  | case1 =>
    grind
  -- Case 2: Sorting a non-empty list `x :: xs`.
  | case2 _ _ ih =>
    simp only [time_bind]
    grw [insert_time]
    simp only [insertionSort_same_length]
    unfold timeInsertionSortRec
    grind

/-- Time complexity of `insertionSort`.

If `insertionSort` is applied to a list `xs` of length `n`,
then the time taken is at most `(n * (n - 1)) / 2` (the worst-case number of comparisons).
-/
theorem insertionSort_time (xs : List α) :
    let n := xs.length
    (insertionSort xs).time ≤ (n * (n - 1)) / 2 := by
  grind [insertionSort_time_le, timeInsertionSortRec_eq]

/-- Auxiliary lemma to show that the closed-form solution of the recurrence matches
the expected formula.
-/
private lemma worst_case_math (n : ℕ) : n * (n - 1) / 2 + n = (n + 1) * n / 2 := by
  have h1 : timeInsertionSortRec n = n * (n - 1) / 2 := by
    have h := timeInsertionSortRec_eq n
    omega
  have h2 : timeInsertionSortRec (n + 1) = (n + 1) * n / 2 := by
    have h := timeInsertionSortRec_eq (n + 1)
    have h_sub : (n + 1) - 1 = n := rfl
    rw [h_sub] at h
    omega
  have h3 : timeInsertionSortRec (n + 1) = timeInsertionSortRec n + n := rfl
  omega

/-- Time complexity of `insertionSort` - Worst-case scenario.

In the worst case, the input list is strictly sorted in descending order,
so each insertion requires comparing with every element in the sorted tail.

Thus, the total time is `n * (n - 1) / 2` comparisons for a list of length `n`.
-/
theorem insertionSort_time_worst_case (xs : List α) (h_sorted : IsStrictlySortedDescending xs) :
    let n := xs.length
    (insertionSort xs).time = n * (n - 1) / 2 := by
  -- The proof proceeds by induction on the structure of the list `xs`.
  induction xs with
  -- Base case: n = 0.
  | nil =>
    simp [insertionSort]
  -- Inductive case: Assume the statement holds for lists of length `n`, and prove it for `n + 1`.
  | cons x xs ih =>
    rw [IsStrictlySortedDescending, List.pairwise_cons] at h_sorted
    have h_head : ∀ y ∈ xs, x > y := h_sorted.left
    have h_tail : IsStrictlySortedDescending xs := h_sorted.right
    have ih_tail := ih h_tail
    have h_perm : xs ~ ⟪insertionSort xs⟫ := (insertionSort_perm xs).symm
    have h_gt_sorted : ∀ y ∈ ⟪insertionSort xs⟫, x > y :=
      forall_mem_of_perm h_perm h_head
    unfold insertionSort
    simp only [time_bind]
    have h_insert_time : (insert x ⟪insertionSort xs⟫).time = ⟪insertionSort xs⟫.length :=
      insert_time_of_gt_all x ⟪insertionSort xs⟫ h_gt_sorted
    rw [h_insert_time, ih_tail, insertionSort_same_length]
    simp
    have h_math := worst_case_math xs.length
    simp [h_math]

/-- Time complexity of `insertionSort` - Best-case scenario.

In the best case, the input list is already sorted in ascending order,
so each insertion takes only 1 comparison.

Thus, if `xs` is a non-empty sorted list of length `n > 0`, the total time is `n - 1` comparisons
for a list of length `n`.
If `xs` is empty, the time is 0 comparisons.
-/
theorem insertionSort_time_best_case (xs : List α) (h_sorted : IsSortedAscending xs) :
    let n := xs.length
    if n = 0
    then (insertionSort xs).time = 0
    else (insertionSort xs).time = n - 1 := by
  -- Remove the `let n := xs.length` to avoid issues with the `if` statement
  -- and make the proof more straightforward.
  change
    if xs.length = 0
    then (insertionSort xs).time = 0
    else (insertionSort xs).time = xs.length - 1
  -- The proof proceeds by induction on the structure of the list `xs`.
  induction xs with
  -- Base case: n = 0.
  | nil =>
    simp [insertionSort]
  -- Inductive case: Assume the statement holds for lists of length `n`, and prove it for `n + 1`.
  | cons x xs ih =>
    split
    · contradiction
    · rw [IsSortedAscending, List.pairwise_cons] at h_sorted
      have h_head : ∀ y ∈ xs, x ≤ y := h_sorted.left
      have h_tail : IsSortedAscending xs := h_sorted.right
      unfold insertionSort
      simp only [time_bind]
      rw [insertionSort_eq_of_sorted xs h_tail]
      cases xs with
      | nil =>
        simp [insert, insertionSort]
      | cons y ys =>
        have h_x_le_y : x ≤ y := h_head y List.mem_cons_self
        rw [insert_time_of_le x y ys h_x_le_y]
        have ih_tail := ih h_tail
        split at ih_tail
        · contradiction
        · simp_all

end TimeComplexity

end Cslib.Algorithms.Lean.TimeM
