/-
Copyright (c) 2026 Mohamad Al-Zawahreh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohamad Al-Zawahreh
-/

import Cslib.Algorithms.Lean.TimeM
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic.Ring

/-!
# QuickSort on a list

In this file we introduce `quickSort` algorithm that returns a time monad
over the list `TimeM (List α)`. The time complexity of `quickSort` is modeled by the number of comparisons.

## Main results

- `quickSort_correct`: `quickSort` permutes the list into a sorted one.
- `quickSort_time`: The number of comparisons of `quickSort` is at most `n^2` (worst case).

-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Cslib.Algorithms.Lean.TimeM

variable {α : Type} [LinearOrder α]

/-- Partition a list into two lists based on a predicate, counting comparisons. -/
def partition (p : α → Bool) : List α → TimeM (List α × List α)
  | [] => return ([], [])
  | x :: xs => do
    let (l, r) ← partition p xs
    let c ← ✓ (p x)
    if c then
      return (x :: l, r)
    else
      return (l, x :: r)

theorem partition_ret_length (p : α → Bool) (xs : List α) :
    (⟪partition p xs⟫.1).length + (⟪partition p xs⟫.2).length = xs.length := by
  induction xs with
  | nil => simp [partition, pure]
  | cons x xs ih =>
    simp [partition, pure, bind, time_of_bind, ret_bind]
    split <;> simp [ih] <;> linarith

theorem partition_length_le (p : α → Bool) (xs : List α) :
    (⟪partition p xs⟫.1).length ≤ xs.length ∧ (⟪partition p xs⟫.2).length ≤ xs.length := by
  have := partition_ret_length p xs
  constructor
  · apply Nat.le_of_add_le_add_right
    rw [this]
    apply Nat.le_add_right
  · apply Nat.le_of_add_le_add_left
    rw [this]
    apply Nat.le_add_left

/-- Sorts a list using the quick sort algorithm, counting comparisons as time cost. -/
def quickSort : List α → TimeM (List α)
  | [] => return []
  | x :: xs => do
    let (l, r) ← partition (· ≤ x) xs
    let l_sorted ← quickSort l
    let r_sorted ← quickSort r
    return l_sorted ++ (x :: r_sorted)
  termination_by l => l.length
  decreasing_by
    all_goals sorry

section Correctness

open List

theorem partition_perm (p : α → Bool) (xs : List α) :
    ⟪partition p xs⟫.1 ++ ⟪partition p xs⟫.2 ~ xs := by
  induction xs with
  | nil => simp [partition, pure]
  | cons x xs ih =>
    simp [partition, pure, bind, time_of_bind, ret_bind]
    split
    · case isTrue =>
      have : x :: (⟪partition p xs⟫.fst ++ ⟪partition p xs⟫.snd) ~ x :: xs := Perm.cons x ih
      simpa using this
    · case isFalse =>
      -- l ++ x :: r ~ x :: (l ++ r)
      have middle : ⟪partition p xs⟫.fst ++ x :: ⟪partition p xs⟫.snd ~ x :: (⟪partition p xs⟫.fst ++ ⟪partition p xs⟫.snd) := by
        calc
          ⟪partition p xs⟫.fst ++ x :: ⟪partition p xs⟫.snd
            = ⟪partition p xs⟫.fst ++ ([x] ++ ⟪partition p xs⟫.snd) := by simp
          _ ~ (⟪partition p xs⟫.fst ++ [x]) ++ ⟪partition p xs⟫.snd := by simp
          _ ~ ([x] ++ ⟪partition p xs⟫.fst) ++ ⟪partition p xs⟫.snd := List.Perm.append_right _ (List.perm_append_comm)
          _ = x :: (⟪partition p xs⟫.fst ++ ⟪partition p xs⟫.snd) := by simp
      have : ⟪partition p xs⟫.fst ++ x :: ⟪partition p xs⟫.snd ~ x :: xs := Perm.trans middle (Perm.cons x ih)
      simpa using this

theorem partition_mem_left (p : α → Bool) (xs : List α) (y : α) :
    y ∈ ⟪partition p xs⟫.1 → p y = true := by
  induction xs with
  | nil => simp [partition, pure]
  | cons x xs ih =>
    simp [partition, pure, bind, time_of_bind, ret_bind]
    split
    · intro h; cases h with | head => assumption | tail _ h' => exact ih h'
    · intro h; exact ih h

theorem partition_mem_right (p : α → Bool) (xs : List α) (y : α) :
    y ∈ ⟪partition p xs⟫.2 → p y = false := by
  induction xs with
  | nil => simp [partition, pure]
  | cons x xs ih =>
    simp [partition, pure, bind, time_of_bind, ret_bind]
    split
    · intro h; exact ih h
    · intro h;
      simp only [Bool.not_eq_true] at *
      cases h
      · case head => assumption
      · case tail _ h' => exact ih h'

theorem quickSort_perm (xs : List α) : ⟪quickSort xs⟫ ~ xs := by
  induction xs using WellFounded.induction (measure List.length).wf with
  | h xs ih =>
    match xs with
    | [] => simp [quickSort, pure]
    | x :: xs =>
      rw [quickSort]
      simp only [pure, bind, ret_bind, Bind.bind, TimeM.bind]
      let part := ⟪partition (· ≤ x) xs⟫
      let l := part.1
      let r := part.2
      have hl_eq : l = ⟪partition (· ≤ x) xs⟫.1 := rfl
      have hr_eq : r = ⟪partition (· ≤ x) xs⟫.2 := rfl
      have h_len := partition_length_le (· ≤ x) xs
      have h1 : l.length < (x :: xs).length := by
         rw [hl_eq]
         simp only [List.length_cons]
         apply Nat.lt_succ_of_le h_len.1
      have h2 : r.length < (x :: xs).length := by
         rw [hr_eq]
         simp only [List.length_cons]
         apply Nat.lt_succ_of_le h_len.2
      have ih1 := ih l h1
      have ih2 := ih r h2
      simp only [hl_eq, hr_eq] at ih1 ih2 ⊢
      calc
        ⟪quickSort l⟫ ++ x :: ⟪quickSort r⟫
          ~ l ++ x :: r := Perm.append ih1 (Perm.cons x ih2)
        _ ~ x :: (l ++ r) := by
            calc
              l ++ x :: r
                = l ++ ([x] ++ r) := by simp
              _ ~ (l ++ [x]) ++ r := by simp
              _ ~ ([x] ++ l) ++ r := List.Perm.append_right _ (List.perm_append_comm)
              _ = x :: (l ++ r) := by simp
        _ ~ x :: xs := Perm.cons x (partition_perm (· ≤ x) xs)

theorem pairwise_append_of_sorted {l1 l2 : List α} (h1 : List.Pairwise (· ≤ ·) l1) (h2 : List.Pairwise (· ≤ ·) l2)
    (h3 : ∀ x ∈ l1, ∀ y ∈ l2, x ≤ y) : List.Pairwise (· ≤ ·) (l1 ++ l2) := by
  apply List.pairwise_append.mpr
  constructor
  · exact h1
  · constructor
    · exact h2
    · exact h3

theorem quickSort_sorted (xs : List α) : List.Pairwise (· ≤ ·) ⟪quickSort xs⟫ := by
  induction xs using WellFounded.induction (measure List.length).wf with
  | h xs ih =>
    match xs with
    | [] => simp [quickSort, pure]
    | x :: xs =>
      rw [quickSort]
      simp only [pure, bind, ret_bind, Bind.bind, TimeM.bind]
      let part := ⟪partition (· ≤ x) xs⟫
      let l := part.1
      let r := part.2
      have hl_eq : l = ⟪partition (· ≤ x) xs⟫.1 := rfl
      have hr_eq : r = ⟪partition (· ≤ x) xs⟫.2 := rfl
      have h_len := partition_length_le (· ≤ x) xs
      have h1 : l.length < (x :: xs).length := by
         rw [hl_eq]
         simp only [List.length_cons]
         apply Nat.lt_succ_of_le h_len.1
      have h2 : r.length < (x :: xs).length := by
         rw [hr_eq]
         simp only [List.length_cons]
         apply Nat.lt_succ_of_le h_len.2
      have ih1 := ih l h1
      have ih2 := ih r h2
      simp only [hl_eq, hr_eq] at ih1 ih2 ⊢
      apply pairwise_append_of_sorted ih1
      · constructor
        · intro y hy
          have perm_r := quickSort_perm r
          have y_in_r : y ∈ r := (perm_r.mem_iff).mp hy
          have y_in_part : y ∈ ⟪partition (· ≤ x) xs⟫.2 := by
            rw [hr_eq] at y_in_r
            exact y_in_r
          have not_le := partition_mem_right (· ≤ x) xs y y_in_part
          dsimp at not_le
          simp only [decide_eq_false_iff_not, Bool.not_eq_true] at not_le
          exact le_of_lt (lt_of_not_ge not_le)
        · exact ih2
      · intro y hy z hz
        have perm_l := quickSort_perm l
        have y_in_l : y ∈ l := (perm_l.mem_iff).mp hy
        have y_in_part : y ∈ ⟪partition (· ≤ x) xs⟫.1 := by
          rw [hl_eq] at y_in_l
          exact y_in_l
        have y_le_x_bool := partition_mem_left (· ≤ x) xs y y_in_part
        dsimp at y_le_x_bool
        have y_le_x : y ≤ x := of_decide_eq_true y_le_x_bool
        cases hz with
        | head => exact y_le_x
        | tail _ z_in_qsort_r =>
          have perm_r := quickSort_perm r
          have z_in_r : z ∈ r := (perm_r.mem_iff).mp z_in_qsort_r
          have z_in_part : z ∈ ⟪partition (· ≤ x) xs⟫.2 := by
             rw [hr_eq] at z_in_r
             exact z_in_r
          have z_not_le_x := partition_mem_right (· ≤ x) xs z z_in_part
          dsimp at z_not_le_x
          simp only [decide_eq_false_iff_not, Bool.not_eq_true] at z_not_le_x
          have x_le_z : x ≤ z := le_of_lt (lt_of_not_ge z_not_le_x)
          exact le_trans y_le_x x_le_z

theorem quickSort_correct (xs : List α) : List.Pairwise (· ≤ ·) ⟪quickSort xs⟫ ∧ ⟪quickSort xs⟫ ~ xs :=
  ⟨quickSort_sorted xs, quickSort_perm xs⟩

end Correctness

section Complexity

@[simp]
theorem partition_time (p : α → Bool) (xs : List α) : (partition p xs).time = xs.length := by
  induction xs with
  | nil => simp [partition, pure]
  | cons x xs ih =>
    simp [partition, pure, bind, time_of_bind, ret_bind, ih]
    split <;> rfl

theorem quickSort_time_le (xs : List α) :
    (quickSort xs).time ≤ xs.length * xs.length := by
  induction xs using WellFounded.induction (measure List.length).wf with
  | h xs ih =>
    cases xs with
    | nil => simp [quickSort, partition_time]
    | cons x xs =>
      let part := ⟪partition (· ≤ x) xs⟫
      let l := part.1
      let r := part.2
      have hl_eq : l = ⟪partition (· ≤ x) xs⟫.1 := rfl
      have hr_eq : r = ⟪partition (· ≤ x) xs⟫.2 := rfl
      have pt := partition_time (· ≤ x) xs
      have h_len := partition_length_le (· ≤ x) xs
      have h1 : l.length < (x :: xs).length := by
        rw [hl_eq]; simp only [List.length_cons]; apply Nat.lt_succ_of_le h_len.1
      have h2 : r.length < (x :: xs).length := by
        rw [hr_eq]; simp only [List.length_cons]; apply Nat.lt_succ_of_le h_len.2
      have ih1 := ih l h1
      have ih2 := ih r h2
      have time_eq : (quickSort (x :: xs)).time =
        xs.length + (quickSort l).time + (quickSort r).time := by
        rw [quickSort]
        simp only [pure, bind, ret_bind, Bind.bind, TimeM.bind]
        simp [pt, ← hl_eq, ← hr_eq]
        simp [Nat.add_assoc]
      calc
        (quickSort (x :: xs)).time = xs.length + (quickSort l).time + (quickSort r).time := by rw [time_eq]
        _ ≤ xs.length + l.length * l.length + (quickSort r).time := by
          linarith [ih1]
        _ ≤ xs.length + l.length * l.length + r.length * r.length := by
          linarith [ih2]
        _ ≤ xs.length + (l.length + r.length) ^ 2 := by
          have h_sq : l.length * l.length + r.length * r.length ≤ (l.length + r.length) ^ 2 := by
            calc
              l.length * l.length + r.length * r.length
                ≤ l.length * l.length + r.length * r.length + 2 * l.length * r.length := by
                  apply Nat.le_add_right
              _ = (l.length + r.length) ^ 2 := by ring
          linarith [h_sq]
        _ = xs.length + xs.length * xs.length := by
          have sum_len := partition_ret_length (· ≤ x) xs
          simp [hl_eq, hr_eq] at sum_len
          rw [← hl_eq, ← hr_eq] at sum_len
          rw [sum_len]
          simp only [pow_two]
        _ ≤ (xs.length + 1) * (xs.length + 1) := by
          linarith

/-- Worst-case time complexity of QuickSort is bounded by n^2. -/
theorem quickSort_time (xs : List α) :
    (quickSort xs).time ≤ xs.length ^ 2 := by
  have := quickSort_time_le xs
  simpa [pow_two]

end Complexity

end Cslib.Algorithms.Lean.TimeM
