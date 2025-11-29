/-
Copyright (c) 2025 Sorrachai Yingchareonthawornhcai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornhcai
-/

import Mathlib.Tactic
import Cslib.Algorithms.Lean.TimeM


/-!
# MergeSort on a list

In this file we introduce `merge` and `mergeSort` algorithms that returns a time monad
over the list `TimeM (List α)`. The time complexity of `mergeSort` is the number of comparisons.

--
## Main results

- `mergeSort_correct`: `mergeSort` returns a sorted list which is a permutation of the input list.
- `mergeSort_time`:  `mergeSort` time is at most `n*⌈log₂ n⌉` where `n` is the list size.

-/

set_option tactic.hygienic false
set_option autoImplicit false

namespace TimeM

variable {α : Type} [LinearOrder α]

def merge :  List α → List α  → TimeM (List α)
  | [], ys => return ys
  | xs, [] => return xs
  | x::xs', y::ys' => do
    if x ≤ y then
      let rest ← merge xs' (y::ys')
      ✓ (x :: rest)
    else
      let rest ← merge (x::xs') ys'
      ✓ (y :: rest)

def mergeSort (xs : List α) : TimeM (List α) :=  do
  if xs.length < 2 then return xs
  else
    let n := xs.length
    let half := n / 2
    let left :=  xs.take half
    let right := xs.drop half
    let sortedLeft ← mergeSort left
    let sortedRight ← mergeSort right
    merge sortedLeft sortedRight

section Correctness

open List

abbrev IsSorted (l : List α) : Prop := Sorted (· ≤ ·) l
abbrev MinOfList (x : α) (l : List α) : Prop := ∀ b ∈ l, x ≤ b

theorem mem_either_merge (xs ys : List α) (z : α)
  (hz : z ∈ (merge xs ys).ret) : z ∈ xs ∨ z ∈ ys := by
  fun_induction merge
  · simp_all only [Pure.pure, pure, not_mem_nil, or_true]
  · simp_all only [imp_false, Pure.pure, pure, not_mem_nil, or_false]
  all_goals
  simp_all only [mem_cons, Bind.bind, tick, ret_bind]
  cases hz
  all_goals (grind)

theorem min_all_merge (x : α) (xs ys : List α)
(hxs : MinOfList x xs) (hys : MinOfList x ys) : MinOfList x (merge xs ys).ret := by
  simp_all only [MinOfList]
  intro a ha
  apply mem_either_merge at ha
  grind

theorem sorted_merge {l1 l2 : List α} (hxs : IsSorted l1)
  (hys : IsSorted l2) : IsSorted ((merge l1 l2).ret) := by
  fun_induction merge l1 l2 <;> try simpa
  all_goals
  simp_all only [not_le, IsSorted, sorted_cons, Bind.bind, tick,
   ret_bind, and_true, forall_const]
  apply min_all_merge <;> grind

theorem mergeSort_sorted (xs : List α) : IsSorted (mergeSort xs).ret := by
  fun_induction mergeSort xs
  · simp only [IsSorted, Pure.pure, pure]
    rcases x with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> simp [sorted_nil,sorted_singleton]; grind
  · simp only [IsSorted, Bind.bind, ret_bind]
    exact sorted_merge ih2 ih1

lemma merge_perm (l₁ l₂ : List α) : (merge l₁ l₂).ret ~ l₁ ++ l₂ := by
  fun_induction merge <;> simp_all only [not_le, cons_append, Bind.bind, tick,
    Pure.pure, pure, ret_bind] <;> grind

theorem mergeSort_perm (xs : List α) : (mergeSort xs).ret ~ xs := by
  fun_induction mergeSort xs
  · simp only [Pure.pure, pure, Perm.refl]
  · simp only [Bind.bind, ret_bind]
    calc
      (merge (mergeSort left).ret (mergeSort right).ret).ret ~
      (mergeSort left).ret ++ (mergeSort right).ret  := by apply merge_perm
      _ ~ left++right := Perm.append ih2 ih1
      _ ~ x := by simp only [take_append_drop, Perm.refl, left, right]

/-- MergeSort is functionally correct. -/
theorem mergeSort_correct (xs : List α) :
  IsSorted (mergeSort xs).ret ∧ (mergeSort xs).ret ~ xs  := by
  constructor
  · apply mergeSort_sorted
  · apply mergeSort_perm

end Correctness

section TimeComplexity

def timeMergeSortRec : ℕ → ℕ
| 0 => 0
| 1 => 0
| n@(_+2) => timeMergeSortRec (n/2) + timeMergeSortRec ((n-1)/2 + 1) + n

/-- The ceiling of Nat.log 2 -/
def clog2 (n : ℕ) : ℕ :=
  if n ≤ 1 then 0 else Nat.log 2 (n - 1) + 1


/-- Key Lemma: ⌈log2 ⌈n/2⌉⌉ ≤ ⌈log2 n⌉ - 1 for n > 1 -/
lemma clog2_half_le (n : ℕ) (h : n > 1) : clog2 ((n + 1) / 2) ≤ clog2 n - 1 := by
  unfold clog2
  split_ifs with h_small
  · omega
  · simp only [add_tsub_cancel_right, zero_le]
  · omega
  · simp only [add_tsub_cancel_right]
    rw [← Nat.sub_mul_div (n + 1) 2 1]
    simp only [mul_one, Nat.reduceSubDiff, Nat.log_div_base]
    rw [Nat.sub_one_add_one ?_]
    simp only [ne_eq, Nat.log_eq_zero_iff, Nat.not_ofNat_le_one, or_false, not_lt]
    omega

/-- Same logic for the floor half: ⌈log2 ⌊n/2⌋⌉ ≤ ⌈log2 n⌉ - 1 -/
lemma clog2_floor_half_le (n : ℕ) (h : n > 1) : clog2 (n / 2) ≤ clog2 n - 1 := by
  apply Nat.le_trans _ (clog2_half_le n h)
  simp only [clog2]
  split_ifs with h_small
  · rfl
  · omega
  · omega
  · expose_names
    grw [Nat.log_mono_right]
    grind

private lemma some_algebra (n : ℕ) :
  (n / 2 + 1) * clog2 (n / 2 + 1) + ((n + 1) / 2 + 1) * clog2 ((n + 1) / 2 + 1) + (n + 2) ≤
  (n + 2) * clog2 (n + 2) := by
  -- 1. Substitution: Let N = n_1 + 2 to clean up the expression
  let N := n + 2
  have hN : N ≥ 2 := by omega
  -- 2. Rewrite the terms using N
  have t1 : n / 2 + 1 = N / 2 := by omega
  have t2 : (n + 1) / 2 + 1 = (N + 1) / 2 := by omega
  have t3 : n + 1 + 1 = N := by omega
  rw [t1, t2, t3]
  let k := clog2 N
  have h_bound_l : clog2 (N / 2) ≤ k - 1 := clog2_floor_half_le N hN
  have h_bound_r : clog2 ((N + 1) / 2) ≤ k - 1 := clog2_half_le N hN
  grw [h_bound_l,h_bound_r]
  rw [←Nat.add_mul]
  have h_split : N / 2 + (N + 1) / 2 = N := by omega
  rw [h_split]
  bound

abbrev T (n : ℕ) : ℕ := n * clog2 n

/-- Solve the recurrence -/
theorem timeMergeSortRec_le (n : ℕ) : timeMergeSortRec n ≤ T n := by
  fun_induction timeMergeSortRec
  · simp [T]
  · simp
  · grw [ih1,ih2]
    simp only [Nat.ofNat_pos, Nat.add_div_right, Nat.add_one_sub_one, Nat.succ_eq_add_one]
    exact some_algebra n_1


@[simp] theorem merge_ret_length_eq_sum (xs ys : List α) :
  (merge xs ys).ret.length = xs.length + ys.length := by
  fun_induction merge <;> simp [Pure.pure, pure, List.length_nil, add_zero,zero_add]
  all_goals grind

@[simp] theorem mergeSort_same_length (xs : List α) :
  (mergeSort xs).ret.length = xs.length:= by
  fun_induction mergeSort
  · simp only [Pure.pure, pure]
  · simp only [Bind.bind, ret_bind, merge_ret_length_eq_sum]
    grind

@[simp] theorem merge_time (xs ys : List α) :
  (merge xs ys).time ≤ xs.length + ys.length := by
  fun_induction merge <;> simp
  all_goals grind

private theorem mergeSort_time_le (xs : List α) :
  (mergeSort xs).time ≤ timeMergeSortRec xs.length := by
  fun_induction mergeSort
  · simp only [Pure.pure, pure]
    grind
  · simp only [Bind.bind, time_of_bind]
    grw [merge_time]
    simp only [mergeSort_same_length]
    unfold timeMergeSortRec
    grw [ih1,ih2]
    split <;> all_goals (simp_all)
    grind

/-- Time complexity of mergeSort -/
theorem mergeSort_time (xs : List α) :
  let n := xs.length
  (mergeSort xs).time ≤ n * clog2 n:= by
  simp only
  grw [mergeSort_time_le,timeMergeSortRec_le]

end TimeComplexity

end TimeM
