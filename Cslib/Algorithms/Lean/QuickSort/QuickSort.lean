/-
Copyright (c) 2026 Mohamad Al-Zawahreh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohamad Al-Zawahreh
-/

import Cslib.Algorithms.Lean.TimeM
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.List.Perm.Basic


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

@[simp]
theorem partition_ret_length (p : α → Bool) (xs : List α) :
    (⟪partition p xs⟫.1).length + (⟪partition p xs⟫.2).length = xs.length := by
  induction xs with
  | nil => simp [partition, pure]
  | cons x xs ih =>
    simp [partition, pure, bind, time_of_bind, ret_bind]
      simp [ih] <;> linarith

theorem partition_length_le (p : α → Bool) (xs : List α) :
    (⟪partition p xs⟫.1).length ≤ xs.length ∧ (⟪partition p xs⟫.2).length ≤ xs.length := by
  have := partition_ret_length p xs
  linarith

/-- Sorts a list using the quick sort algorithm, counting comparisons as time cost. -/
def quickSort : List α → TimeM (List α)
  | [] => return []
  | x :: xs => do
    let (l, r) ← partition (· ≤ x) xs
    have h1 : l.length < (x :: xs).length := by
      have := partition_length_le (· ≤ x) xs
      simp; apply Nat.lt_succ_of_le this.1
    have h2 : r.length < (x :: xs).length := by
      have := partition_length_le (· ≤ x) xs
      simp; apply Nat.lt_succ_of_le this.2
    let l_sorted ← quickSort l
    let r_sorted ← quickSort r
    return l_sorted ++ (x :: r_sorted)
  termination_by l => l.length

section Correctness

open List

/-- `x` is a minimum element of list `l` if `x ≤ b` for all `b ∈ l`. -/
abbrev MinOfList (x : α) (l : List α) : Prop := ∀ b ∈ l, x ≤ b

/-- `x` is a maximum element of list `l` if `b ≤ x` for all `b ∈ l`. -/
abbrev MaxOfList (x : α) (l : List α) : Prop := ∀ b ∈ l, b ≤ x

@[simp]
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
    · intro h; cases h with | head => assumption | tail _ h' => exact ih h'

theorem quickSort_perm (xs : List α) : ⟪quickSort xs⟫ ~ xs := by
  fun_induction quickSort xs with
  | case1 => simp [pure]
  | case2 x xs ih =>
    simp [pure, bind, ret_bind]
    let l := ⟪partition (· ≤ x) xs⟫.1
    let r := ⟪partition (· ≤ x) xs⟫.2
    have h_len := partition_length_le (· ≤ x) xs
    have h1 : l.length < (x :: xs).length := by
      simp [l]; apply Nat.lt_succ_of_le h_len.1
    have h2 : r.length < (x :: xs).length := by
      simp [r]; apply Nat.lt_succ_of_le h_len.2
    have ih1 : ⟪quickSort l⟫ ~ l := ih l h1
    have ih2 : ⟪quickSort r⟫ ~ r := ih r h2
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

abbrev IsSorted (l : List α) : Prop := List.Pairwise (· ≤ ·) l

theorem pairwise_append_of_sorted {l1 l2 : List α} (h1 : IsSorted l1) (h2 : IsSorted l2)
    (h3 : ∀ x ∈ l1, ∀ y ∈ l2, x ≤ y) : IsSorted (l1 ++ l2) := by
  apply List.pairwise_append.mpr
  constructor
  · exact h1
  · constructor
    · exact h2
    · exact h3

theorem quickSort_sorted (xs : List α) : IsSorted ⟪quickSort xs⟫ := by
  fun_induction quickSort xs with
  | case1 => simp [pure, IsSorted]
  | case2 x xs ih =>
    simp [pure, bind, ret_bind]
    let l := ⟪partition (· ≤ x) xs⟫.1
    let r := ⟪partition (· ≤ x) xs⟫.2
    have h_len := partition_length_le (· ≤ x) xs
    have h1 : l.length < (x :: xs).length := by
      simp [l]; apply Nat.lt_succ_of_le h_len.1
    have h2 : r.length < (x :: xs).length := by
      simp [r]; apply Nat.lt_succ_of_le h_len.2
    have ih1 : IsSorted ⟪quickSort l⟫ := ih l h1
    have ih2 : IsSorted ⟪quickSort r⟫ := ih r h2
    apply pairwise_append_of_sorted ih1
    · constructor
      · intro y hy
        -- y in right part, need y >= x
        have perm_r := quickSort_perm (⟪partition (· ≤ x) xs⟫.2)
        have y_in_part : y ∈ ⟪partition (· ≤ x) xs⟫.2 := (perm_r.mem_iff).mp hy
        have not_le := partition_mem_right (· ≤ x) xs y y_in_part
        simp at not_le
        exact le_of_lt (lt_of_not_ge not_le)
      · exact ih2
    · intro y hy z hz
      -- y in left sorted, z in right (x::right_sorted)
      -- y <= x is key
      have perm_l := quickSort_perm (⟪partition (· ≤ x) xs⟫.1)
      have y_in_part : y ∈ ⟪partition (· ≤ x) xs⟫.1 := (perm_l.mem_iff).mp hy
      have y_le_x := partition_mem_left (· ≤ x) xs y y_in_part
      simp at y_le_x
      cases hz with
      | head => exact y_le_x
      | tail _ z_in_r =>
        have perm_r := quickSort_perm (⟪partition (· ≤ x) xs⟫.2)
        have z_in_part : z ∈ ⟪partition (· ≤ x) xs⟫.2 := (perm_r.mem_iff).mp z_in_r
        have z_gt_x := partition_mem_right (· ≤ x) xs z z_in_part
        simp at z_gt_x
        apply le_trans y_le_x (le_of_lt (lt_of_not_ge z_gt_x))

theorem quickSort_correct (xs : List α) : IsSorted ⟪quickSort xs⟫ ∧ ⟪quickSort xs⟫ ~ xs :=
  ⟨quickSort_sorted xs, quickSort_perm xs⟩

end Correctness

section Complexity

@[simp]
theorem partition_time (p : α → Bool) (xs : List α) : (partition p xs).time = xs.length := by
  induction xs <;> simp [partition, pure, bind, time_of_bind, *]

theorem quickSort_time_le (xs : List α) :
    (quickSort xs).time ≤ xs.length * xs.length := by
  fun_induction quickSort xs with
  | case1 => simp [pure]
  | case2 x xs ih =>
    simp [pure, bind, time_of_bind, ret_bind]
    -- Cost: partition (xs.length) + T(l) + T(r)
    -- Bound: (length (x::xs))^2 = (xs.length + 1)^2
    let n := xs.length
    let l := ⟪partition (· ≤ x) xs⟫.1
    let r := ⟪partition (· ≤ x) xs⟫.2
    have h_len := partition_length_le (· ≤ x) xs
    have h1 : l.length < (x :: xs).length := by
      simp [l]; apply Nat.lt_succ_of_le h_len.1
    have h2 : r.length < (x :: xs).length := by
      simp [r]; apply Nat.lt_succ_of_le h_len.2
    have len_sum : l.length + r.length = n := by using_elims [partition_ret_length]
    -- Instantiate IH with explicit terms, then fold to local vars if needed
    have ih1' : (quickSort l).time ≤ l.length * l.length := ih l h1
    have ih2' : (quickSort r).time ≤ r.length * r.length := ih r h2
    dsimp [l, r] at *
    rw [ih1', ih2']
    -- Goal: n + l^2 + r^2 <= (n+1)^2
    have : (n + 1) * (n + 1) = n * n + 2 * n + 1 := by ring
    rw [this]
    
    have sq_sum : (l.length + r.length) * (l.length + r.length) = l.length^2 + r.length^2 + 2 * l.length * r.length := by ring
    rw [len_sum] at sq_sum
    -- n^2 = l^2 + r^2 + 2lr
    -- So l^2 + r^2 <= n^2
    have : l.length * l.length + r.length * r.length ≤ n * n := by
      rw [← sq_sum]
      apply Nat.le_add_right
    
    -- Goal: n + l^2 + r^2 <= n^2 + 2n + 1
    -- Reduces to: n + (l^2 + r^2) <= n^2 + 2n + 1
    apply Nat.le_trans (Nat.add_le_add_left this n)
    -- n + n^2 <= n^2 + 2n + 1
    -- n + n^2 <= n^2 + n + (n + 1)
    rw [Nat.add_assoc (n*n) n (n+1), Nat.add_comm (n*n) n, ← Nat.add_assoc]
    apply Nat.add_le_add_left
    apply Nat.le_add_right

/-- Worst-case time complexity of QuickSort is bounded by n^2. -/
theorem quickSort_time (xs : List α) :
    (quickSort xs).time ≤ xs.length ^ 2 := by
  have := quickSort_time_le xs
  simpa [pow_two]

end Complexity

end Cslib.Algorithms.Lean.TimeM

