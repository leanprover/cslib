/-
Copyright (c) 2025 Sorrachai Yingchareonthawornhcai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornhcai
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Nat.Lattice
public import Mathlib.Data.Nat.Log

@[expose] public section

/-!
# MergeSort on a list

In this file we introduce `merge` and `mergeSort` algorithms that returns a time monad
over the list `TimeM (List α)`. The time complexity of `mergeSort` is the number of comparisons.

--
## Main results

- `mergeSort_correct`: `mergeSort` permutes the list into a sorted one.
- `mergeSort_time`:  The number of comparisons of `mergeSort` is at most `n*⌈log₂ n⌉`.

-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

variable {α : Type} [LinearOrder α]

/-- Merges two lists into a single list, counting comparisons as time cost.
Returns a `TimeM (List α)` where the time represents the number of comparisons performed. -/
def merge :  List α → List α → TimeM (List α)
  | [], ys => return ys
  | xs, [] => return xs
  | x::xs', y::ys' => do
    ✓ let c := (x ≤ y : Bool)
    if c then
      let rest ← merge xs' (y::ys')
      return (x :: rest)
    else
      let rest ← merge (x::xs') ys'
      return (y :: rest)

/-- Sorts a list using the merge sort algorithm, counting comparisons as time cost.
Returns a `TimeM (List α)` where the time represents the total number of comparisons. -/
def mergeSort (xs : List α) : TimeM (List α) :=  do
  if xs.length < 2 then return xs
  else
    let half  := xs.length / 2
    let left  := xs.take half
    let right := xs.drop half
    let sortedLeft  ← mergeSort left
    let sortedRight ← mergeSort right
    merge sortedLeft sortedRight

section Correctness

open List

/-- A list is sorted if it satisfies the `Pairwise (· ≤ ·)` predicate. -/
abbrev IsSorted (l : List α) : Prop := List.Pairwise (· ≤ ·) l

/-- `x` is a minimum element of list `l` if `x ≤ b` for all `b ∈ l`. -/
abbrev MinOfList (x : α) (l : List α) : Prop := ∀ b ∈ l, x ≤ b

@[grind →]
theorem mem_either_merge (xs ys : List α) (z : α) (hz : z ∈ ⟪merge xs ys⟫) : z ∈ xs ∨ z ∈ ys := by
  fun_induction merge
  · exact mem_reverseAux.mp hz
  · left
    exact hz
  · grind

theorem min_all_merge (x : α) (xs ys : List α) (hxs : MinOfList x xs) (hys : MinOfList x ys) :
    MinOfList x ⟪merge xs ys⟫ := by
  grind

theorem sorted_merge {l1 l2 : List α} (hxs : IsSorted l1) (hys : IsSorted l2) :
    IsSorted ⟪merge l1 l2⟫ := by
  fun_induction merge l1 l2 with
  | case3 =>
    grind [pairwise_cons]
  | _ => simpa

theorem mergeSort_sorted (xs : List α) : IsSorted ⟪mergeSort xs⟫ := by
  fun_induction mergeSort xs with
  | case1 x =>
    rcases x with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> grind
  | case2 _ _ _ _ _ ih2 ih1 => exact sorted_merge ih2 ih1

lemma merge_perm (l₁ l₂ : List α) : ⟪merge l₁ l₂⟫ ~ l₁ ++ l₂ := by
  fun_induction merge with
  | case1 => simp
  | case2 => simp
  | case3 =>
    grind

theorem mergeSort_perm (xs : List α) : ⟪mergeSort xs⟫ ~ xs := by
  fun_induction mergeSort xs with
  | case1 => simp
  | case2 x _ _ left right ih2 ih1 =>
    simp only [ret_bind]
    calc
      ⟪merge ⟪mergeSort left⟫ ⟪mergeSort right⟫⟫  ~
      ⟪mergeSort left⟫ ++ ⟪mergeSort right⟫  := by apply merge_perm
      _ ~ left++right := Perm.append ih2 ih1
      _ ~ x := by simp only [take_append_drop, Perm.refl, left, right]

/-- MergeSort is functionally correct. -/
theorem mergeSort_correct (xs : List α) : IsSorted ⟪mergeSort xs⟫ ∧ ⟪mergeSort xs⟫ ~ xs :=
  ⟨mergeSort_sorted xs, mergeSort_perm xs⟩

end Correctness

section TimeComplexity

/-- Recurrence relation for the time complexity of merge sort.
For a list of length `n`, this counts the total number of comparisons:
- Base cases: 0 comparisons for lists of length 0 or 1
- Recursive case: split the list, sort both halves,
  then merge (which takes at most `n` comparisons) -/
def timeMergeSortRec : ℕ → ℕ
| 0 => 0
| 1 => 0
| n@(_+2) => timeMergeSortRec (n/2) + timeMergeSortRec ((n-1)/2 + 1) + n

open Nat (clog)

/-- Key Lemma: ⌈log2 ⌈n/2⌉⌉ ≤ ⌈log2 n⌉ - 1 for n > 1 -/
@[grind →]
lemma clog2_half_le (n : ℕ) (h : n > 1) : clog 2 ((n + 1) / 2) ≤ clog 2 n - 1 := by
  rw [Nat.clog_of_one_lt one_lt_two h]
  grind

/-- Same logic for the floor half: ⌈log2 ⌊n/2⌋⌉ ≤ ⌈log2 n⌉ - 1 -/
@[grind →]
lemma clog2_floor_half_le (n : ℕ) (h : n > 1) : clog 2 (n / 2) ≤ clog 2 n - 1 := by
  apply Nat.le_trans _ (clog2_half_le n h)
  apply Nat.clog_monotone
  grind

private lemma some_algebra (n : ℕ) :
    (n / 2 + 1) * clog 2 (n / 2 + 1) + ((n + 1) / 2 + 1) * clog 2 ((n + 1) / 2 + 1) + (n + 2) ≤
    (n + 2) * clog 2 (n + 2) := by
  -- 1. Substitution: Let N = n_1 + 2 to clean up the expression
  let N := n + 2
  have hN : N ≥ 2 := by omega
  -- 2. Rewrite the terms using N
  have t1 : n / 2 + 1 = N / 2 := by omega
  have t2 : (n + 1) / 2 + 1 = (N + 1) / 2 := by omega
  have t3 : n + 1 + 1 = N := by omega
  let k := clog 2 N
  have h_bound_l : clog 2 (N / 2) ≤ k - 1 := clog2_floor_half_le N hN
  have h_bound_r : clog 2 ((N + 1) / 2) ≤ k - 1 := clog2_half_le N hN
  have h_split : N / 2 + (N + 1) / 2 = N := by omega
  grw [t1, t2, t3, h_bound_l, h_bound_r, ←Nat.add_mul, h_split]
  exact Nat.le_refl (N * (k - 1) + N)

/-- Upper bound function for merge sort time complexity: `T(n) = n * ⌈log₂ n⌉` -/
abbrev T (n : ℕ) : ℕ := n * clog 2 n

/-- Solve the recurrence -/
theorem timeMergeSortRec_le (n : ℕ) : timeMergeSortRec n ≤ T n := by
  fun_induction timeMergeSortRec with
  | case1 => grind
  | case2 => grind
  | case3 n ih2 ih1 =>
    grw [ih1,ih2]
    have := some_algebra n
    grind [Nat.add_div_right]

@[simp] theorem merge_ret_length_eq_sum (xs ys : List α) :
    ⟪merge xs ys⟫.length = xs.length + ys.length := by
  fun_induction merge with
  | case3 =>
    grind
  | _ => simp

@[simp] theorem mergeSort_same_length (xs : List α) :
    ⟪mergeSort xs⟫.length = xs.length := by
  fun_induction mergeSort
  · simp
  · grind [merge_ret_length_eq_sum]

@[simp] theorem merge_time (xs ys : List α) : (merge xs ys).time ≤ xs.length + ys.length := by
  fun_induction merge with
  | case3 =>
    grind
  | _ => simp

theorem mergeSort_time_le (xs : List α) :
    (mergeSort xs).time ≤ timeMergeSortRec xs.length := by
  fun_induction mergeSort with
  | case1 =>
    grind
  | case2 _ _ _ _ _ ih2 ih1 =>
    simp only [time_bind]
    grw [merge_time]
    simp only [mergeSort_same_length]
    unfold timeMergeSortRec
    grind

/-- Time complexity of mergeSort -/
theorem mergeSort_time (xs : List α) :
  let n := xs.length
  (mergeSort xs).time ≤ n * clog 2 n := by
  grind [mergeSort_time_le, timeMergeSortRec_le]

end TimeComplexity

end Cslib.Algorithms.Lean.TimeM
