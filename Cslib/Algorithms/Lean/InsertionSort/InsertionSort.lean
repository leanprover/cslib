/-
Copyright (c) 2026 Robert Joseph George. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George
-/

module

public import Cslib.Algorithms.Lean.Sorting
public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Data.List.Sort
public import Mathlib.Data.Nat.Basic

/-!
# Stable insertion sort on lists

`insertionSort` returns a `TimeM ℕ (List α)`: the return value is the sorted list, and the time
component counts comparisons.

Equal values are inserted before equal values already in the sorted tail. Since the sort processes
the input from right to left, this preserves the original order of equal values.

The cost model charges exactly one tick for each comparison made while searching for the insertion
point.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

variable {α : Type*} [LinearOrder α]

/--
Inserts one value into a sorted list, counting comparisons as time cost. The test is `x ≤ y`, so
the new value is placed before equal values in the already-sorted tail.
-/
def insert (x : α) : List α → TimeM ℕ (List α)
  | [] => return [x]
  | y :: ys => do
    ✓ let inFront := x ≤ y
    if inFront then
      return x :: y :: ys
    else
      let rest ← insert x ys
      return y :: rest

/-- Sorts a list using stable insertion sort, counting comparisons as time cost. -/
def insertionSort : List α → TimeM ℕ (List α)
  | [] => return []
  | x :: xs => do
    let sortedTail ← insertionSort xs
    insert x sortedTail

section Correctness

/-- Timed `insert` computes mathlib's ordered insertion. -/
@[simp, grind =]
theorem ret_insert (x : α) (xs : List α) :
    ⟪insert x xs⟫ = xs.orderedInsert (· ≤ ·) x := by
  induction xs with
  | nil => simp [insert]
  | cons y ys ih =>
    by_cases h : x ≤ y <;> simp [insert, h, ih]

/-- Timed insertion sort computes mathlib's insertion sort. -/
@[simp, grind =]
theorem ret_insertionSort (xs : List α) :
    ⟪insertionSort xs⟫ = xs.insertionSort (· ≤ ·) := by
  induction xs with
  | nil => simp [insertionSort]
  | cons x xs ih => simp [insertionSort, ih]

/-- Inserting one value keeps exactly the original values. -/
private theorem insert_perm (x : α) (xs : List α) : (⟪insert x xs⟫).Perm (x :: xs) := by
  simpa using List.perm_orderedInsert (· ≤ ·) x xs

/-- Insertion sort returns a permutation of its input. -/
theorem insertionSort_perm (xs : List α) : (⟪insertionSort xs⟫).Perm xs := by
  simpa using List.perm_insertionSort (· ≤ ·) xs

/-- Inserting one value is stable with respect to filtering by any fixed value. -/
private theorem insert_stable (x : α) (xs : List α) : StableByValue (x :: xs) ⟪insert x xs⟫ := by
  induction xs with
  | nil => simp [StableByValue, insert]
  | cons y ys ih =>
    intro z
    by_cases h : x ≤ y
    · simp [insert, h]
    · have ihz := ih z
      by_cases hyz : y = z
      · by_cases hxz : x = z
        · subst x
          subst y
          exact (h le_rfl).elim
        · have hxlez : ¬x ≤ z := by simpa [hyz] using h
          simpa [insert, hxlez, hxz, hyz] using ihz
      · by_cases hxz : x = z
        · subst x
          have hzley : ¬z ≤ y := by simpa using h
          simpa [insert, hzley, hyz] using ihz
        · simpa [insert, h, hyz, hxz] using ihz

/--
Insertion sort is stable. The induction uses stability of the recursive tail and then stability of
one insertion step.
-/
theorem insertionSort_stable (xs : List α) : StableByValue xs ⟪insertionSort xs⟫ := by
  induction xs with
  | nil => simp [StableByValue, insertionSort]
  | cons x xs ih =>
    intro z
    simp only [insertionSort, ret_bind]
    rw [insert_stable x ⟪insertionSort xs⟫ z]
    simp only [List.filter_cons]
    rw [ih z]

/-- Insertion sort returns a sorted list. -/
theorem insertionSort_sorted (xs : List α) : List.Pairwise (· ≤ ·) ⟪insertionSort xs⟫ := by
  simpa using List.pairwise_insertionSort (· ≤ ·) xs

/-- Insertion sort is functionally correct. -/
theorem insertionSort_correct (xs : List α) : List.Pairwise (· ≤ ·) ⟪insertionSort xs⟫ ∧
    (⟪insertionSort xs⟫).Perm xs ∧ StableByValue xs ⟪insertionSort xs⟫ := by
  exact ⟨insertionSort_sorted xs, insertionSort_perm xs, insertionSort_stable xs⟩

end Correctness

section TimeComplexity

/-- Inserting into a list performs at most one comparison per possible insertion point. -/
private theorem insert_time_le (x : α) (xs : List α) : (insert x xs).time ≤ xs.length + 1 := by
  induction xs with
  | nil => simp [insert]
  | cons y ys ih =>
    by_cases h : x ≤ y
    · simp [insert, h]
    · simp [insert, h]
      omega

/-- Insertion sort preserves length. -/
private theorem insertionSort_length (xs : List α) : ⟪insertionSort xs⟫.length = xs.length := by
  simp

/-- Time complexity of insertion sort. -/
theorem insertionSort_time (xs : List α) :
    let n := xs.length
    (insertionSort xs).time ≤ n * n := by
  induction xs with
  | nil => simp [insertionSort]
  | cons x xs ih =>
    simp only [List.length_cons]
    simp only [insertionSort, time_bind]
    have hinsert := insert_time_le x ⟪insertionSort xs⟫
    rw [insertionSort_length xs] at hinsert
    have hsquare : xs.length * xs.length + (xs.length + 1) ≤
        (xs.length + 1) * (xs.length + 1) := by
      exact Nat.le_trans
        (Nat.add_le_add_right
          (Nat.mul_le_mul_right xs.length (Nat.le_succ xs.length)) (xs.length + 1))
        (by rw [Nat.mul_succ])
    exact (Nat.add_le_add ih hinsert).trans hsquare

end TimeComplexity

end Cslib.Algorithms.Lean.TimeM
