/-
Copyright (c) 2026 Priyanshu Sharma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Priyanshu Sharma
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Data.List.Sort

/-!
# InsertionSort on a list

In this file we introduce `orderedInsert` and `insertionSort` algorithms that return a time monad
over the list `TimeM ℕ (List α)`. The time complexity of `insertionSort` is the number of
comparisons.

## Main results

- `insertionSort_correct`: `insertionSort` permutes the list into a sorted one.
- `insertionSort_time`: The number of comparisons of `insertionSort` is at most `n * n`.

-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

variable {α : Type} [LinearOrder α]

/-- Inserts an element into a sorted list, counting comparisons as time cost.
Returns a `TimeM ℕ (List α)` where the time represents the number of comparisons performed. -/
def orderedInsert (a : α) : List α → TimeM ℕ (List α)
  | [] => return [a]
  | b :: l => do
    ✓
    if a ≤ b then
      return a :: b :: l
    else
      let rest ← orderedInsert a l
      return b :: rest

/-- Sorts a list using the insertion sort algorithm, counting comparisons as time cost.
Returns a `TimeM ℕ (List α)` where the time represents the total number of comparisons. -/
def insertionSort : List α → TimeM ℕ (List α)
  | [] => return []
  | a :: l => do
    let sorted ← insertionSort l
    orderedInsert a sorted

section Correctness

open List

/-- Our ordered insert computes the one already in mathlib. -/
@[simp, grind =]
theorem ret_orderedInsert (a : α) (l : List α) :
    ⟪orderedInsert a l⟫ = l.orderedInsert (· ≤ ·) a := by
  induction l with
  | nil => simp [orderedInsert]
  | cons b l ih =>
      by_cases h : a ≤ b
      · simp [orderedInsert, List.orderedInsert_cons, h]
      · simp [orderedInsert, List.orderedInsert_cons, h, ih]

/-- Our insertion sort computes the one already in mathlib. -/
@[simp, grind =]
theorem ret_insertionSort (l : List α) : ⟪insertionSort l⟫ = l.insertionSort (· ≤ ·) := by
  induction l with
  | nil => simp [insertionSort]
  | cons a l ih => simp [insertionSort, ih, ret_orderedInsert]

theorem insertionSort_sorted (l : List α) : List.Pairwise (· ≤ ·) ⟪insertionSort l⟫ := by
  rw [ret_insertionSort]
  simpa using (List.sortedLE_insertionSort (l := l)).pairwise

theorem insertionSort_perm (l : List α) : ⟪insertionSort l⟫ ~ l := by
  rw [ret_insertionSort]
  simpa using (List.perm_insertionSort (r := (· ≤ ·)) (l := l))

/-- InsertionSort is functionally correct. -/
theorem insertionSort_correct (l : List α) :
    List.Pairwise (· ≤ ·) ⟪insertionSort l⟫ ∧ ⟪insertionSort l⟫ ~ l :=
  ⟨insertionSort_sorted l, insertionSort_perm l⟩

end Correctness

section TimeComplexity

/-- Recurrence relation for the time complexity of insertion sort.
For a list of length `n`, this counts the total number of comparisons:
- Base case: 0 comparisons for the empty list
- Recursive case: sort the tail, then insert the head into the sorted tail -/
def timeInsertionSortRec : ℕ → ℕ
  | 0 => 0
  | n + 1 => timeInsertionSortRec n + n

@[simp] theorem orderedInsert_ret_length (a : α) (l : List α) :
    ⟪orderedInsert a l⟫.length = l.length + 1 := by
  rw [ret_orderedInsert]
  simpa using (List.orderedInsert_length (r := (· ≤ ·)) l a)

@[simp] theorem insertionSort_same_length (l : List α) :
    ⟪insertionSort l⟫.length = l.length := by
  rw [ret_insertionSort]
  simp only [List.length_insertionSort]

@[simp] theorem orderedInsert_time (a : α) (l : List α) : (orderedInsert a l).time ≤ l.length := by
  induction l with
  | nil => simp [orderedInsert]
  | cons b l ih =>
      by_cases h : a ≤ b
      · simp [orderedInsert, h]
      · simp [orderedInsert, h]
        simpa [Nat.succ_eq_add_one, Nat.add_comm] using Nat.succ_le_succ ih

theorem timeInsertionSortRec_le (n : ℕ) : timeInsertionSortRec n ≤ n * n := by
  induction n with
  | zero => simp [timeInsertionSortRec]
  | succ n ih =>
      calc
        timeInsertionSortRec (n + 1) = timeInsertionSortRec n + n := by
          simp [timeInsertionSortRec]
        _ ≤ n * n + n := Nat.add_le_add_right ih n
        _ ≤ (n + 1) * (n + 1) := by
          have h : n * n + n ≤ n * n + n + (n + 1) := by omega
          simpa [Nat.mul_add, Nat.add_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

theorem insertionSort_time_le (l : List α) :
    (insertionSort l).time ≤ timeInsertionSortRec l.length := by
  induction l with
  | nil => simp [insertionSort, timeInsertionSortRec]
  | cons a l ih =>
      calc
        (insertionSort (a :: l)).time =
            (insertionSort l).time + (orderedInsert a ⟪insertionSort l⟫).time := by
          simp [insertionSort]
        _ ≤ timeInsertionSortRec l.length + ⟪insertionSort l⟫.length :=
          Nat.add_le_add ih (orderedInsert_time a ⟪insertionSort l⟫)
        _ = timeInsertionSortRec l.length + l.length := by rw [insertionSort_same_length]
        _ = timeInsertionSortRec (List.length (a :: l)) := by simp [timeInsertionSortRec]

/-- Time complexity of insertionSort -/
theorem insertionSort_time (l : List α) :
    let n := l.length
    (insertionSort l).time ≤ n * n := by
  grind [insertionSort_time_le, timeInsertionSortRec_le]

end TimeComplexity

end Cslib.Algorithms.Lean.TimeM
