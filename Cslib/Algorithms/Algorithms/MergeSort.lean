/-
Copyright (c) 2026 Shreyas Srinivas, Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas, Eric Wieser, Kim Morrison, Sorrachai Yingchareonthawornchai
-/

module

public import Cslib.Algorithms.Models.ListComparisonSort
public import Cslib.Algorithms.MergeSort.MergeSort
import all Cslib.Algorithms.Lean.Sort.Merge
import all Init.Data.List.Sort.Basic

/-!
# Merge sort in a list

In this file we state and prove the correctness and complexity of merge sort in lists under
the `SortOps` model. The implementation and proofs are adapted from Kim Morrison's
[PR #401](https://github.com/leanprover/cslib/pull/401), using `List.mergeM` and
`List.mergeSortM` with explicit comparison queries. Evaluation agrees exactly with
`List.mergeSort`, including its stable ordering of ties.

## Main Definitions
- `merge` : Merge algorithm for merging two sorted lists in the `SortOps` query model
- `mergeSort` : Merge sort algorithm in the `SortOps` query model

## Main results

- `mergeSort_eval`: `mergeSort` evaluates identically to `List.mergeSort`.
- `mergeSort_sorted` :  `mergeSort` outputs a sorted list.
- `mergeSort_perm` : The output of `mergeSort` is a permutation of the input list
- `mergeSort_complexity` : `mergeSort` takes at most n * ⌈log n⌉ comparisons.
-/

@[expose] public section

namespace Cslib.Algorithms

open SortOps

/-- Merge two sorted lists using comparisons in the query monad. -/
abbrev merge (xs ys : List α) : Prog (SortOps α) (List α) :=
  List.mergeM xs ys fun x y => FreeM.lift (cmpLE x y)

lemma merge_timeComplexity (xs ys : List α) (le : α → α → Bool) :
    (merge xs ys).time (sortModelNat le) ≤ xs.length + ys.length := by
  unfold merge
  fun_induction List.mergeM with
  | case1 | case2 => simp
  | case3 x xs y ys ihx ihy =>
    simp only [Prog.time_bind', Prog.eval_lift, sortModelNat_evalQuery_cmpLE,
      Prog.time_lift, sortModelNat_cost, List.length_cons]
    split <;> simp_all <;> omega

@[simp]
lemma merge_eval (xs ys : List α) (le : α → α → Bool) :
    (merge xs ys).eval (sortModelNat le) = List.merge xs ys le := by
  simpa using Id.ext_iff.1 <|
    (Prog.isMonadHom_pure_eval (sortModelNat le)).map_listMergeM xs ys
      (fun x y => FreeM.lift (cmpLE x y))

lemma merge_length (x y : List α) (le : α → α → Bool) :
    ((merge x y).eval (sortModelNat le)).length = x.length + y.length := by
  rw [merge_eval]
  apply List.length_merge

/-- Sort a list using merge sort with comparison queries, as in PR #401. -/
abbrev mergeSort (xs : List α) : Prog (SortOps α) (List α) :=
  List.mergeSortM xs fun x y => FreeM.lift (cmpLE x y)

/-- Evaluating query-based merge sort agrees with Lean's stable `List.mergeSort`. -/
@[simp]
lemma mergeSort_eval (xs : List α) (le : α → α → Bool) :
    (mergeSort xs).eval (sortModelNat le) = List.mergeSort xs le := by
  simpa using Id.ext_iff.1 <|
    (Prog.isMonadHom_pure_eval (sortModelNat le)).map_listMergeSortM xs
      (fun x y => FreeM.lift (cmpLE x y))

lemma mergeSort_length (xs : List α) (le : α → α → Bool) :
    ((mergeSort xs).eval (sortModelNat le)).length = xs.length := by
  simp

lemma merge_sorted_sorted
    (xs ys : List α) (le : α → α → Bool) [Std.Total (fun x y => le x y)]
    [IsTrans _ (fun x y => le x y)]
    (hxs_mono : xs.Pairwise (fun x y => le x y))
    (hys_mono : ys.Pairwise (fun x y => le x y)) :
    ((merge xs ys).eval (sortModelNat le)).Pairwise (fun x y => le x y) := by
  rw [merge_eval]
  simpa using hxs_mono.merge hys_mono

theorem mergeSort_sorted
    (xs : List α) (le : α → α → Bool) [Std.Total (fun x y => le x y = true)]
    [IsTrans _ (fun x y => le x y = true)] :
    ((mergeSort xs).eval (sortModelNat le)).Pairwise ((fun x y => le x y = true)) := by
  rw [mergeSort_eval]
  simpa using List.pairwise_mergeSort' (fun x y => le x y = true) xs

theorem mergeSort_perm (xs : List α) (le : α → α → Bool) :
    ((mergeSort xs).eval (sortModelNat le)).Perm xs := by
  rw [mergeSort_eval]
  exact List.mergeSort_perm xs le

section TimeComplexity

open Cslib.Algorithms.Lean.TimeM

/-- The arithmetic inequality for the merge sort recurrence, from PR #401. -/
private theorem mergeSort_bound (n : ℕ) (hn : 2 ≤ n) :
    ((n + 1) / 2) * Nat.clog 2 ((n + 1) / 2) +
      (n / 2 * Nat.clog 2 (n / 2) + ((n + 1) / 2 + n / 2)) ≤
      n * Nat.clog 2 n := by
  have hclog := Nat.clog_of_one_lt (by omega : (1 : Nat) < 2) hn
  have hceil : Nat.clog 2 ((n + 1) / 2) + 1 ≤ Nat.clog 2 n := le_of_eq hclog.symm
  have hfloor : Nat.clog 2 (n / 2) + 1 ≤ Nat.clog 2 n :=
    (Nat.add_le_add_right (Nat.clog_mono_right 2 (by omega)) 1).trans hceil
  have hsum : (n + 1) / 2 + n / 2 = n := by omega
  have h1 := Nat.mul_le_mul_left ((n + 1) / 2) hceil
  have h2 := Nat.mul_le_mul_left (n / 2) hfloor
  rw [Nat.mul_succ] at h1 h2
  calc _ = ((n + 1) / 2 * Nat.clog 2 ((n + 1) / 2) + (n + 1) / 2) +
           (n / 2 * Nat.clog 2 (n / 2) + n / 2) := by omega
    _ ≤ (n + 1) / 2 * Nat.clog 2 n + n / 2 * Nat.clog 2 n := Nat.add_le_add h1 h2
    _ = ((n + 1) / 2 + n / 2) * Nat.clog 2 n := (Nat.add_mul ..).symm
    _ = n * Nat.clog 2 n := by rw [hsum]

theorem mergeSort_complexity (xs : List α) (le : α → α → Bool) :
    (mergeSort xs).time (sortModelNat le) ≤ T xs.length := by
  unfold mergeSort
  fun_induction List.mergeSortM with
  | case1 | case2 => simp
  | case3 x y zs halves ihl ihr =>
    simp only [Prog.time_bind']
    grw [merge_timeComplexity, ihl, ihr]
    simp only [mergeSort_length]
    rw [halves.1.property, halves.2.property]
    exact mergeSort_bound _ (by simp)

end TimeComplexity

end Cslib.Algorithms
