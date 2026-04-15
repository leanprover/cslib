/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas, Eric Wieser, Ethan Ermovick
-/
module

public import Cslib.AlgorithmsTheory.Algorithms.ListOrderedInsert
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Insertion sort in a list

In this file we state and prove the correctness and complexity of insertion sort in lists under
the `SortOpsInsertHead` model. This insertionSort evaluates identically to the upstream version of
`List.insertionSort`
--

## Main Definitions

- `insertionSort` : Insertion sort algorithm in the `SortOpsInsertHead` query model

## Main results

- `insertionSort_eval`: `insertionSort` evaluates identically to `List.insertionSort`.
- `insertionSort_permutation` :  `insertionSort` outputs a permutation of the input list.
- `insertionSort_sorted` : `insertionSort` outputs a sorted list.
- `insertionSort_complexity` : `insertionSort` takes at most n * (n + 1) comparisons and
  (n + 1) * (n + 2) list head-insertions.
- `insertionSort_stable` : `insertionSort` is a stable sorting algorithm.
-/

namespace Cslib

namespace Algorithms

open Prog

/-- The insertionSort algorithms on lists with the `SortOps` query. -/
def insertionSort (l : List α) : Prog (SortOpsInsertHead α) (List α) :=
  match l with
  | [] => return []
  | x :: xs => do
      let rest ← insertionSort xs
      insertOrd x rest

@[simp]
theorem insertionSort_eval (l : List α) (le : α → α → Bool) :
    (insertionSort l).eval (sortModel le) = l.insertionSort (fun x y => le x y = true) := by
  induction l with simp_all [insertionSort]

theorem insertionSort_permutation (l : List α) (le : α → α → Bool) :
    ((insertionSort l).eval (sortModel le)).Perm l := by
    simp [insertionSort_eval, List.perm_insertionSort]

theorem insertionSort_sorted
    (l : List α) (le : α → α → Bool)
    [Std.Total (fun x y => le x y = true)] [IsTrans α (fun x y => le x y = true)] :
    ((insertionSort l).eval (sortModel le)).Pairwise (fun x y => le x y = true) := by
  simpa using List.pairwise_insertionSort _ _

lemma insertionSort_length (l : List α) (le : α → α → Bool) :
    ((insertionSort l).eval (sortModel le)).length = l.length := by
  simp

lemma insertionSort_time_compares (head : α) (tail : List α) (le : α → α → Bool) :
    ((insertionSort (head :: tail)).time (sortModel le)).compares =
      ((insertionSort tail).time (sortModel le)).compares +
        ((insertOrd head (tail.insertionSort (fun x y => le x y = true))).time
          (sortModel le)).compares := by
  simp [insertionSort]

lemma insertionSort_time_inserts (head : α) (tail : List α) (le : α → α → Bool) :
    ((insertionSort (head :: tail)).time (sortModel le)).inserts =
      ((insertionSort tail).time (sortModel le)).inserts +
        ((insertOrd head (tail.insertionSort (fun x y => le x y = true))).time
          (sortModel le)).inserts := by
  simp [insertionSort]

theorem insertionSort_complexity (l : List α) (le : α → α → Bool) :
    ((insertionSort l).time (sortModel le))
      ≤ ⟨l.length * (l.length + 1), (l.length + 1) * (l.length + 2)⟩ := by
  induction l with
  | nil =>
    simp [insertionSort]
  | cons head tail ih =>
    grind [insertOrd_complexity_upper_bound, List.length_insertionSort, SortOpsCost.le_def,
      insertionSort_time_compares, insertionSort_time_inserts]

section Stability

private lemma filter_orderedInsert_of_neg {r : α → α → Prop} [DecidableRel r]
    (a : α) (l : List α) (p : α → Bool) (ha : p a = false) :
    (l.orderedInsert r a).filter p = l.filter p := by
  induction l with
  | nil => rw [List.orderedInsert_nil]; simp [ha]
  | cons b l ih =>
    rw [List.orderedInsert_cons]
    split
    · simp [List.filter, ha]
    · simp only [List.filter]; split <;> simp [ih]

private lemma filter_orderedInsert_of_pos {r : α → α → Prop} [DecidableRel r]
    (a : α) (l : List α) (p : α → Bool)
    (ha : p a = true)
    (hcompat : ∀ b, p b = true → r a b)
    (hsorted : l.Pairwise r) :
    (l.orderedInsert r a).filter p = a :: l.filter p := by
  induction l with
  | nil => rw [List.orderedInsert_nil]; simp [ha]
  | cons b l ih =>
    rw [List.orderedInsert_cons]
    rw [List.pairwise_cons] at hsorted
    split
    · simp [List.filter, ha]
    · rename_i hnr
      have hnpb : p b = false := by
        by_contra h; push_neg at h
        cases hpb : p b with
        | false => simp [hpb] at h
        | true => exact hnr (hcompat b hpb)
      simp only [List.filter, hnpb]
      exact ih hsorted.2

theorem insertionSort_stable
    (xs : List α)
    (le : α → α → Bool)
    [Std.Total (fun x y => le x y = true)]
    [IsTrans α (fun x y => le x y = true)] :
    IsStableSort (fun xs => (insertionSort xs).eval (sortModel le)) xs le := by
  simp only [insertionSort_eval]
  intro k
  induction xs with
  | nil => simp
  | cons a rest ih =>
    change List.filter (fun x => le x k && le k x)
      (List.insertionSort (fun x y => le x y = true) (a :: rest)) =
      List.filter (fun x => le x k && le k x) (a :: rest)
    rw [List.insertionSort_cons]
    have hsorted : (rest.insertionSort (fun x y => le x y = true)).Pairwise
        (fun x y => le x y = true) :=
      List.pairwise_insertionSort _ rest
    rcases hab : (le a k && le k a) with _ | _
    · rw [filter_orderedInsert_of_neg a _ (fun x => le x k && le k x) hab]
      simp [hab, ih]
    · rw [filter_orderedInsert_of_pos a _ (fun x => le x k && le k x) hab _ hsorted]
      · simp [hab, ih]
      · intro b hb
        simp only [Bool.and_eq_true] at hab hb
        exact IsTrans.trans (r := fun x y => le x y = true) a k b hab.1 hb.2

end Stability

end Algorithms

end Cslib
