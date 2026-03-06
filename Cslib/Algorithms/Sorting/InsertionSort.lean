/-
Copyright (c) 2025 Brando Miranda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brando Miranda
-/

module

public import Cslib.Init
public import Mathlib.Data.List.Perm.Basic

@[expose] public section

/-!
# Insertion Sort

This file implements insertion sort on lists of natural numbers and proves that the result
is sorted and a permutation of the input.

## Main definitions

- `insert`: Insert an element into a sorted list maintaining order.
- `insertionSort`: Sort a list by repeatedly inserting elements.

## Main results

- `insertionSort_sorted`: The output of `insertionSort` is sorted.
- `insertionSort_perm`: The output is a permutation of the input.

## References

Adapted from the VeriBench benchmark (https://github.com/brandomiranda/veribench).
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Sorting.InsertionSort

/-- A list is sorted in ascending order. -/
abbrev IsSorted (l : List Nat) : Prop := List.Pairwise (· ≤ ·) l

/-- Insert `a` into a sorted list maintaining ascending order. -/
def insert (a : Nat) : List Nat → List Nat
  | [] => [a]
  | x :: xs =>
    if a ≤ x then
      a :: x :: xs
    else
      x :: insert a xs

/-- Sort a list using insertion sort. -/
def insertionSort : List Nat → List Nat
  | [] => []
  | x :: xs => insert x (insertionSort xs)

/-! ## Tests -/

example : insertionSort [3, 1, 2] = [1, 2, 3] := by decide
example : insertionSort [] = ([] : List Nat) := by decide
example : insertionSort [1] = [1] := by decide
example : insertionSort [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by decide

/-! ## Membership in insert -/

/-- Membership in `insert a xs` is equivalent to being `a` or being in `xs`. -/
@[simp]
theorem mem_insert (a b : Nat) (xs : List Nat) :
    b ∈ insert a xs ↔ b = a ∨ b ∈ xs := by
  induction xs with
  | nil => simp [insert]
  | cons x rest ih =>
    simp only [insert]
    split <;> simp_all only [List.mem_cons]
    constructor
    · rintro (rfl | rfl | h) <;> simp_all
    · rintro (rfl | rfl | h) <;> simp_all

/-! ## Sorted proof -/

/-- Inserting into a sorted list produces a sorted list. -/
theorem insert_sorted (a : Nat) (xs : List Nat) (h : IsSorted xs) :
    IsSorted (insert a xs) := by
  induction xs with
  | nil => exact List.Pairwise.cons (fun _ hb => nomatch hb) List.Pairwise.nil
  | cons x rest ih =>
    simp only [insert]
    cases h with
    | cons h_all h_rest =>
      split
      · rename_i h_le
        exact List.Pairwise.cons (fun y hy => by
          simp only [List.mem_cons] at hy
          rcases hy with rfl | hy
          · exact h_le
          · exact Nat.le_trans h_le (h_all y hy)) (List.Pairwise.cons h_all h_rest)
      · rename_i h_nle
        have h_lt : x < a := Nat.lt_of_not_le h_nle
        exact List.Pairwise.cons (fun y hy => by
          rw [mem_insert] at hy
          rcases hy with rfl | hy
          · exact Nat.le_of_lt h_lt
          · exact h_all y hy) (ih h_rest)

/-- `insertionSort` produces a sorted list. -/
theorem insertionSort_sorted (xs : List Nat) : IsSorted (insertionSort xs) := by
  induction xs with
  | nil => exact List.Pairwise.nil
  | cons x rest ih => exact insert_sorted x (insertionSort rest) ih

/-! ## Permutation proof -/

/-- Inserting `a` into `xs` produces a permutation of `a :: xs`. -/
theorem insert_perm (a : Nat) (xs : List Nat) :
    List.Perm (insert a xs) (a :: xs) := by
  induction xs with
  | nil => exact List.Perm.refl _
  | cons x rest ih =>
    simp only [insert]
    split
    · exact List.Perm.refl _
    · exact (List.Perm.cons x ih).trans (List.Perm.swap a x rest)

/-- `insertionSort` produces a permutation of its input. -/
theorem insertionSort_perm (xs : List Nat) :
    List.Perm (insertionSort xs) xs := by
  induction xs with
  | nil => exact List.Perm.refl _
  | cons x rest ih =>
    exact (insert_perm x (insertionSort rest)).trans (List.Perm.cons x ih)

/-- `insertionSort` preserves length. -/
theorem insertionSort_length (xs : List Nat) :
    (insertionSort xs).length = xs.length :=
  (insertionSort_perm xs).length_eq

end Cslib.Algorithms.Sorting.InsertionSort
