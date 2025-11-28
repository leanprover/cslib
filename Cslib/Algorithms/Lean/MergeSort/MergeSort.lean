/-
Copyright (c) 2025 Sorrachai Yingchareonthawornhcai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornhcai
-/

import Mathlib.Tactic
import Cslib.Algorithms.Lean.TimeM


/-!
# MergeSort on a list

In this file we introduce `merge` and `mergeSort` algorithms that returns a time
monad over the list `TimeM (List α)`.

--
## Main results

- `mergeSort_correct`: `mergeSort` returns a sorted list which is a permutation of the input list.
- `mergeSort_time`:  `mergeSort` time is `n *(Nat.log 2 n)` where `n` is the list size.

-/

set_option tactic.hygienic false
set_option autoImplicit false

namespace TimeM
section MergeSort

variable {α : Type} [LinearOrder α]

def merge :  List α → List α  → TimeM (List α)
  | [], ys => ✓ ys, ys.length
  | xs, [] => ✓ xs, xs.length
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

open List

@[simp] def IsSorted (l : List α) : Prop := Sorted (· ≤ ·) l
@[simp, grind] def MinOfList (x : α) (l : List α) : Prop := ∀ b ∈ l, x ≤ b

theorem mem_either_merge (xs ys : List α) (z : α)
  (hz : z ∈ (merge xs ys).ret) : z ∈ xs ∨ z ∈ ys := by
  fun_induction merge
  all_goals (try (simp only [not_mem_nil, false_or];assumption))
  all_goals
  simp only [Bind.bind, tick, ret_bind, mem_cons] at hz
  cases hz
  all_goals (aesop)

theorem min_all_merge (x : α) (xs ys : List α)
(hxs : MinOfList x xs) (hys : MinOfList x ys) : MinOfList x (merge xs ys).ret := by
  simp_all only [MinOfList]
  intro a ha
  apply mem_either_merge at ha
  grind

theorem sorted_merge {l1 l2 : List α} (hxs : IsSorted l1)
  (hys : IsSorted l2) : IsSorted ((merge l1 l2).ret) := by
  fun_induction merge l1 l2 <;> try simpa
  all_goals (simp_all only [IsSorted, sorted_cons, and_imp, Bind.bind, tick, Nat.cast_one, ret_bind,
      implies_true, and_true, forall_const]; apply min_all_merge <;> grind)

theorem mergeSort_sorted (xs : List α) : IsSorted (mergeSort xs).ret := by
  fun_induction mergeSort xs
  · simp only [IsSorted, Pure.pure, pure]
    rcases x with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> simp [sorted_nil,sorted_singleton]; grind
  · simp only [IsSorted, Bind.bind, ret_bind]
    exact sorted_merge ih2 ih1

lemma merge_perm (l₁ l₂ : List α) : (merge l₁ l₂).ret ~ l₁ ++ l₂ := by
  fun_induction merge <;> simp only [Bind.bind, tick, ret_bind, cons_append, perm_cons] <;> grind

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

@[grind =] private def timeMergeSortRec : ℕ → ℤ
| 0 => 0
| 1 => 0
| n@(_+2) => timeMergeSortRec (n/2) + timeMergeSortRec ((n-1)/2 + 1) + n

@[simp] theorem merge_ret_length_eq_sum (xs ys : List α) :
  (merge xs ys).ret.length = xs.length + ys.length := by
  fun_induction merge <;> all_goals
  simp_all only [length_cons, Bind.bind, tick, ret_bind]
  grind

@[simp] theorem mergeSort_same_length (xs : List α) :
  (mergeSort xs).ret.length = xs.length:= by
  fun_induction mergeSort
  · simp only [Pure.pure, pure]
  · simp only [Bind.bind, ret_bind, merge_ret_length_eq_sum]
    grind

@[simp] theorem merge_time (xs ys : List α) :
  (merge xs ys).time = xs.length + ys.length := by
  fun_induction merge <;> simp_all only [tick, length_nil, CharP.cast_eq_zero, zero_add,add_zero]
  all_goals (simp_all;grind)

private theorem mergeSort_time_eq (xs : List α) :
  (mergeSort xs).time = timeMergeSortRec xs.length := by
  fun_induction mergeSort
  · simp only [Pure.pure, pure]
    unfold timeMergeSortRec
    norm_cast
    grind
  · simp only [Bind.bind, time_of_bind, merge_time, mergeSort_same_length]
    unfold timeMergeSortRec
    split <;> all_goals (simp_all)
    norm_cast
    grind

@[grind =] private def timeMergeSortRecSimp : ℕ → ℤ
| 0 => 0
| 1 => 0
| n@(_+2) => 2*timeMergeSortRecSimp (n/2) + n

private theorem timeMergeSortRecSimp_EQ (n : ℕ) :
(timeMergeSortRec (2^n))= (timeMergeSortRecSimp (2^n))  := by
  induction n
  · grind
  · unfold timeMergeSortRecSimp timeMergeSortRec
    split <;> grind

private theorem timeMergeSortRecSimp_EQ_CLOSED (n : ℕ) :
  timeMergeSortRecSimp (2^n) = 2^n * n := by
  induction n
  · grind
  · unfold timeMergeSortRecSimp
    split <;> grind

/-- Time complexity of mergeSort -/
theorem mergeSort_time (xs : List α) (h : ∃ k, xs.length = 2 ^ k) :
  (mergeSort xs).time = xs.length*(Nat.log 2 xs.length)  := by
  rw [mergeSort_time_eq]
  obtain ⟨k,hk⟩ := h
  rw [hk,timeMergeSortRecSimp_EQ,timeMergeSortRecSimp_EQ_CLOSED]
  simp only [Nat.lt_add_one, Nat.log_pow]
  norm_cast

end MergeSort

end TimeM
