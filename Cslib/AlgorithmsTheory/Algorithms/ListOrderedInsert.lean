/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas, Eric Wieser
-/

module

public import Cslib.AlgorithmsTheory.QueryModel
public import Cslib.AlgorithmsTheory.Models.ListComparisonSort
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Data.List.Sort
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

@[expose] public section

/-!
# Ordered insertion in a list

In this file we state and prove the correctness and complexity of ordered insertions in lists under
the `SortOps` model. This ordered insert is later used in `insertionSort` mirroring the structure
in upstream libraries for the pure lean code versions of these declarations.

--

## Main Definitions

- `insertOrd` : ordered insert algorithm in the `SortOps` query model

## Main results

- `insertOrd_eval`: `insertOrd` evaluates identically to `List.orderedInsert`.
- `insertOrd_complexity_upper_bound` : Shows that `insertOrd` takes at most `n` comparisons,
   and `n + 1` list head-insertion operations.
- `insertOrd_sorted` : Applying `insertOrd` to a sorted list yields a sorted list.
-/

namespace Cslib
namespace Algorithms

open Prog

open SortOpsInsertHead

/--
Performs ordered insertion of `x` into a list `l` in the `SortOps` query model.
If `l` is sorted, then `x` is inserted into `l` such that the resultant list is also sorted.
-/
def insertOrd (x : α) (l : List α) : Prog (SortOpsInsertHead α) (List α) := do
  match l with
  | [] => insertHead x l
  | a :: as =>
      if (← cmpLE x a : Bool) then
        insertHead x (a :: as)
      else
        let res ← insertOrd x as
        insertHead a res

@[simp]
lemma insertOrd_eval (x : α) (l : List α) (le : α → α → Bool) :
    (insertOrd x l).eval (sortModel le) = l.orderedInsert (fun x y => le x y = true) x := by
  induction l with
  | nil =>
    simp [insertOrd, sortModel]
  | cons head tail ih =>
    by_cases h_head : le x head
    · simp [insertOrd, h_head]
    · simp [insertOrd, h_head, ih]

-- TODO : to upstream
@[simp]
lemma _root_.List.length_orderedInsert (x : α) (l : List α) [DecidableRel r] :
    (l.orderedInsert r x).length = l.length + 1 := by
  induction l <;> grind

theorem insertOrd_complexity_upper_bound
    (l : List α) (x : α) (le : α → α → Bool) :
    (insertOrd x l).time (sortModel le) ≤ ⟨l.length, l.length + 1⟩ := by
  induction l with
  | nil =>
    simp [insertOrd, sortModel]
  | cons head tail ih =>
    obtain ⟨ih_compares, ih_inserts⟩ := ih
    rw [insertOrd]
    by_cases h_head : le x head
    · simp [h_head]
    · simp [h_head]
      grind

lemma insertOrd_sorted
    (l : List α) (x : α) (le : α → α → Bool)
    [Std.Total (fun x y => le x y)]
    [IsTrans _ (fun x y => le x y)] :
    l.Pairwise (fun x y => le x y)
      → ((insertOrd x l).eval (sortModel le)).Pairwise (fun x y => le x y = true) := by
  rw [insertOrd_eval]
  exact List.Pairwise.orderedInsert _ _

end Algorithms

end Cslib
