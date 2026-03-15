/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas, Eric Wieser
-/

module

public import Cslib.AlgorithmsTheory.Models.ListComparisonSort
public import Cslib.AlgorithmsTheory.Lean.MergeSort.MergeSort
import all Cslib.AlgorithmsTheory.Lean.MergeSort.MergeSort
import all Init.Data.List.Sort.Basic
@[expose] public section

/-!
# Merge sort in a list

In this file we state and prove the correctness and complexity of merge sort in lists under
the `SortOps` model.
--

## Main Definitions
- `merge` : Merge algorithm for merging two sorted lists in the `SortOps` query model
- `mergeSort` : Merge sort algorithm in the `SortOps` query model

## Main results

- `mergeSort_eval`: `mergeSort` evaluates identically to the priva.
- `mergeSort_sorted` :  `mergeSort` outputs a sorted list.
- `mergeSort_perm` : The output of `mergeSort` is a permutation of the input list
- `mergeSort_complexity` : `mergeSort` takes at most n * ⌈log n⌉ comparisons.
-/
namespace Cslib.Algorithms

open SortOps

/-- Merge two sorted lists using comparisons in the query monad. -/
@[simp]
def merge (x y : List α) : Prog (SortOps α) (List α) := do
  match x,y with
  | [], ys => return ys
  | xs, [] => return xs
  | x :: xs', y :: ys' => do
      let cmp : Bool ← cmpLE x y
      if cmp then
        let rest ← merge xs' (y :: ys')
        return (x :: rest)
      else
        let rest ← merge (x :: xs') ys'
        return (y :: rest)

lemma merge_timeComplexity (x y : List α) (le : α → α → Bool) :
    (merge x y).time (sortModelNat le) ≤ x.length + y.length := by
  fun_induction List.merge x y (le · ·) with
  | case1 => simp
  | case2 => simp
  | case3 x xs y ys hxy ihx =>
    suffices 1 + (merge xs (y :: ys)).time (sortModelNat le) ≤ xs.length + 1 + (ys.length + 1) by
      simpa [hxy]
    grind
  | case4 x xs y ys hxy ihy =>
    suffices 1 + (merge (x :: xs) ys).time (sortModelNat le) ≤ xs.length + 1 + (ys.length + 1) by
      simpa [hxy]
    grind

@[simp]
lemma merge_eval (x y : List α) (le : α → α → Bool) :
    (merge x y).eval (sortModelNat le) = List.merge x y (le · ·) := by
  fun_induction List.merge with simp_all [merge]

lemma merge_length (x y : List α) (le : α → α → Bool) :
    ((merge x y).eval (sortModelNat le)).length = x.length + y.length := by
  rw [merge_eval]
  apply List.length_merge

/--
The `mergeSort` algorithm in the `SortOps` query model. It sorts the input list
according to the mergeSort algorithm.
-/
def mergeSort (xs : List α) : Prog (SortOps α) (List α) :=  do
  if xs.length < 2 then return xs
  else
    let half  := xs.length / 2
    let left  := xs.take half
    let right := xs.drop half
    let sortedLeft  ← mergeSort left
    let sortedRight ← mergeSort right
    merge sortedLeft sortedRight

/--
The vanilla-lean version of `mergeSortNaive` that is extensionally equal to `mergeSort`
-/
private def mergeSortNaive (xs : List α) (le : α → α → Bool) : List α :=
  if xs.length < 2 then xs
  else
    let sortedLeft  := mergeSortNaive (xs.take (xs.length/2)) le
    let sortedRight := mergeSortNaive (xs.drop (xs.length/2)) le
    List.merge sortedLeft sortedRight (le · ·)

private proof_wanted mergeSortNaive_eq_mergeSort
    [LinearOrder α] (xs : List α) (le : α → α → Bool) :
    mergeSortNaive xs le = xs.mergeSort

private lemma mergeSortNaive_Perm (xs : List α) (le : α → α → Bool) :
  (mergeSortNaive xs le).Perm xs := by
  fun_induction mergeSortNaive with
  | case1 => simp
  | case2 x _ _ _ ih2 ih1 => grw [←List.take_append_drop _ x, List.merge_perm_append, ← ih1, ← ih2]

@[simp]
private lemma mergeSort_eval (xs : List α) (le : α → α → Bool) :
    (mergeSort xs).eval (sortModelNat le) = mergeSortNaive xs le := by
  fun_induction mergeSort with
  | case1 xs h =>
    simp [h, mergeSortNaive, Prog.eval]
  | case2 xs h n left right ihl ihr =>
    rw [mergeSortNaive, if_neg h]
    simp [ihl, ihr, merge_eval]
    rfl

private lemma mergeSortNaive_length (xs : List α) (le : α → α → Bool) :
    (mergeSortNaive xs le).length = xs.length := by
  fun_induction mergeSortNaive with
  | case1 xs h =>
    simp
  | case2 xs h left right ihl ihr =>
    rw [List.length_merge]
    convert congr($ihl + $ihr)
    rw [← List.length_append]
    simp

lemma mergeSort_length (xs : List α) (le : α → α → Bool) :
    ((mergeSort xs).eval (sortModelNat le)).length = xs.length := by
  rw [mergeSort_eval]
  apply mergeSortNaive_length

lemma merge_sorted_sorted
    (xs ys : List α) (le : α → α → Bool) [Std.Total (fun x y => le x y)]
    [IsTrans _ (fun x y => le x y)]
    (hxs_mono : xs.Pairwise (fun x y => le x y))
    (hys_mono : ys.Pairwise (fun x y => le x y)) :
    ((merge xs ys).eval (sortModelNat le)).Pairwise (fun x y => le x y) := by
  rw [merge_eval]
  simpa using hxs_mono.merge hys_mono

private lemma mergeSortNaive_sorted
    (xs : List α) (le : α → α → Bool) [Std.Total ((fun x y => le x y = true))]
    [IsTrans _ ((fun x y => le x y = true))] :
    (mergeSortNaive xs le).Pairwise ((fun x y => le x y = true)) := by
  fun_induction mergeSortNaive with
  | case1 xs h =>
    match xs with | [] | [x] => simp
  | case2 xs h left right ihl ihr =>
    simpa using ihl.merge ihr

theorem mergeSort_sorted
    (xs : List α) (le : α → α → Bool) [Std.Total (fun x y => le x y = true)]
    [IsTrans _ (fun x y => le x y = true)] :
    ((mergeSort xs).eval (sortModelNat le)).Pairwise ((fun x y => le x y = true)) := by
  rw [mergeSort_eval]
  apply mergeSortNaive_sorted

theorem mergeSort_perm (xs : List α) (le : α → α → Bool) :
    ((mergeSort xs).eval (sortModelNat le)).Perm xs := by
  rw [mergeSort_eval]
  apply mergeSortNaive_Perm

section TimeComplexity

open Cslib.Algorithms.Lean.TimeM

-- TODO: reuse the work in `mergeSort_time_le`?
theorem mergeSort_complexity (xs : List α) (le : α → α → Bool) :
    (mergeSort xs).time (sortModelNat le) ≤ T (xs.length) := by
  fun_induction mergeSort with
  | case1 => simp [T]
  | case2 x =>
  simp only [FreeM.bind_eq_bind, Prog.time_bind]
  grind [some_algebra (x.length - 2), mergeSort_eval, merge_timeComplexity, mergeSortNaive_length]

end TimeComplexity

end Cslib.Algorithms
