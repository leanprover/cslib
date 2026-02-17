/-
Copyright (c) 2025 Pedro Abreu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pedro Abreu
-/

module

public import Mathlib.Order.Basic
public import Mathlib.Tactic.Order
public import Cslib.Algorithms.Lean.TimeM

@[expose] public section

/-!
# InsertionSort on a list

In this file we introduce `insert` and `insertionSort` algorithms that returns a time monad
over the list `TimeM (List α)`. The time complexity of `insertionSort` is the number of comparisons.

--
## Main results

- `insertionSort_correct`: `insertionSort` permutes the list into a sorted one.
- `insertionSort_time`:  The number of comparisons of `mergeSort` is at most `n^2`.

-/

namespace Cslib.Algorithms.Lean.TimeM
open List

variable {α : Type} [LinearOrder α]

/--
Inserts an element into a list, maintaining the sorted order.

This function takes an element `a` and a list `l`, and returns a computation
in the `TimeM` monad that produces a new list with the element inserted at
the appropriate position to maintain ordering.

**Parameters:**
- `a : α` - The element to insert
- `l : List α` - The list into which the element is inserted

**Returns:**
- `TimeM (List α)` - A time-tracked computation producing the resulting list
-/
@[simp]
def insert (a : α) (l : List α) : TimeM (List α) :=
  match l with
  | nil => return [a]
  | x :: xs => do
    ✓ let c := (a ≤ x : Bool)
    if c then
      return a :: (x :: xs)
    else
      let rest ← insert a xs
      return x :: rest


/--
Sorts a list using the insertion sort algorithm.

This function performs an insertion sort on the input list and returns the result
wrapped in a `TimeM` monad, which tracks computational time complexity.

**Arguments:**
- `l : List α` - The list to be sorted

**Returns:**
- `TimeM (List α)` - The sorted list wrapped in the TimeM monad
-/
def insertionSort (l : List α) : TimeM (List α):=
  match l with
  | nil => return nil
  | x :: xs => do
    let rest ← insertionSort xs
    insert x rest

section Correctness

/-- A list is sorted if it satisfies the `Pairwise (· ≤ ·)` predicate. -/
abbrev IsSorted (l : List α) : Prop := List.Pairwise (· ≤ ·) l

@[grind →]
lemma mem_either_insert (l : List α) (h : x ∈ ⟪insert y l⟫) :  x = y ∨ x ∈ l := by
  fun_induction insert with
  | case1 => grind
  | case2 z l ih =>
    by_cases h1 : y ≤ z
    · simp [decide_eq_true_eq] at h
      grind
    · simp only [decide_eq_true_eq, bind_pure_comp, ret_bind] at h
      grind


lemma insert_correct : ∀ a (l : List α) (_ : IsSorted l), IsSorted (⟪insert a l⟫) := by
  intros a l h
  fun_induction insert a l with
  | case1 => simp
  | case2 x l ih =>
    simp only [decide_eq_true_eq, bind_pure_comp, ret_bind]
    split_ifs with h1
    · grind
    · simp only [pairwise_cons] at h
      simp only [IsSorted] at ih
      rcases h with ⟨ ha, hb ⟩
      simp only [ret_map, pairwise_cons]
      apply And.intro
      · intros a' h2
        have h3 := mem_either_insert _ h2
        grind
      · grind

theorem insertionSort_sorted (l : List α) :
  IsSorted (⟪insertionSort l⟫) := by
  induction l with
  | nil =>
    simp only [insertionSort, ret_pure, Pairwise.nil]
  | cons x xs ih =>
    simp only [insertionSort, ret_bind]
    exact insert_correct x ⟪(insertionSort xs)⟫ ih

lemma permutation_insert_aux : ∀ (l : List α) a,
  ⟪insert a l⟫ ~ (a :: l) := by
  intros l a
  fun_induction insert with
  | case1 => simp only [ret_pure, Perm.refl]
  | case2 b l' ih =>
    simp
    split_ifs with h1
    · simp
    · simp
      grind

lemma permutation_insert : ∀ (l l' : List α) a,
  l ~ l' →
  ⟪insert a l⟫ ~ a :: l' := by
  intro l l' a h
  cases l' with
  | nil =>
    have h1 : l.isEmpty = [].isEmpty := Perm.isEmpty_eq h
    simp only [isEmpty_nil, List.isEmpty_iff] at h1
    rw [h1]
    simp
  | cons a' l' =>
    apply Perm.symm
    apply Perm.trans (l₂ := a :: l)
    · simp only [perm_cons]
      apply Perm.symm
      assumption
    apply Perm.symm
    apply permutation_insert_aux

lemma insertionSort_perm (l : List α) : ⟪insertionSort l⟫ ~ l := by
  fun_induction insertionSort with
  | case1 => simp
  | case2 a l ih =>
    simp only [ret_bind]
    apply permutation_insert
    assumption

/-- InsertionSort is functionally correct. -/
theorem insertionSort_correct (l : List α) :
  IsSorted (⟪insertionSort l⟫) ∧ ⟪insertionSort l⟫ ~ l :=
    ⟨ insertionSort_sorted l, insertionSort_perm l⟩

end Correctness

section TimeComplexity

lemma insert_time (l : List α) :
  (insert a l).time ≤ l.length := by
  fun_induction insert with
  | case1 => simp
  | case2 b l ih =>
    simp at *
    split_ifs with h1
    · simp
    · grind

lemma insertionSort_len (l : List α) :
  ⟪insertionSort l⟫.length = l.length := by
  have h := insertionSort_perm l
  exact Perm.length_eq h

/-- Time complexity of insertionSort -/
theorem insertionSort_time (l : List α) :
  let n := l.length
  (insertionSort l).time ≤ n^2 := by
  fun_induction insertionSort with
  | case1 => simp
  | case2 a l ih =>
    simp only [time_bind, length_cons] at *
    have h : (insert a ⟪insertionSort l⟫).time ≤ ⟪insertionSort l⟫.length := by
      apply insert_time
    rw [insertionSort_len] at h
    grind

end TimeComplexity
end Cslib.Algorithms.Lean.TimeM
