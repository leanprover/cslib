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
# Bubble Sort

This file implements bubble sort on lists of natural numbers and proves that the result
is a permutation of the input with preserved length.

## Main definitions

- `bubblePassAux`: Accumulator-based helper that bubbles an element rightward through a list.
- `bubblePass`: One pass of bubble sort.
- `bubbleSortAux`: Repeated application of `bubblePass` with fuel-based termination.
- `bubbleSort`: Top-level bubble sort.

## Main results

- `bubbleSort_perm`: The output is a permutation of the input.
- `bubbleSort_length`: The output has the same length as the input.
- `bubblePass_fixed_sorted`: If a pass leaves the list unchanged, it is sorted.
- `bubblePass_sorted_id`: A sorted list is a fixed point of `bubblePass`.

## References

Adapted from the VeriBench benchmark (https://github.com/brandomiranda/veribench).
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Sorting.BubbleSort

/-- A list is sorted in ascending order. -/
abbrev IsSorted (l : List Nat) : Prop := List.Pairwise (· ≤ ·) l

/-- Accumulator-based helper for `bubblePass`. Carries `acc` rightward through `xs`,
swapping with smaller elements. Uses structural recursion on `xs`. -/
def bubblePassAux (acc : Nat) : List Nat → List Nat
  | [] => [acc]
  | x :: xs =>
    if acc > x then
      x :: bubblePassAux acc xs
    else
      acc :: bubblePassAux x xs

/-- One pass of bubble sort: compares adjacent elements and swaps them if out of order,
effectively bubbling the largest element to the end. -/
def bubblePass : List Nat → List Nat
  | [] => []
  | x :: xs => bubblePassAux x xs

/-- Repeated application of `bubblePass`. -/
def bubbleSortAux : List Nat → Nat → List Nat
  | l, 0 => l
  | l, k + 1 => bubbleSortAux (bubblePass l) k

/-- Sort a list using bubble sort. -/
def bubbleSort (l : List Nat) : List Nat :=
  bubbleSortAux l l.length

/-! ## Tests -/

example : bubbleSort [3, 1, 2] = [1, 2, 3] := by decide
example : bubbleSort [] = ([] : List Nat) := by decide
example : bubbleSort [1] = [1] := by decide
example : bubbleSort [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by decide
example : bubbleSort [2, 1] = [1, 2] := by decide

/-! ## Permutation proofs -/

/-- `bubblePassAux acc xs` is a permutation of `acc :: xs`. -/
theorem bubblePassAux_perm (acc : Nat) (xs : List Nat) :
    List.Perm (bubblePassAux acc xs) (acc :: xs) := by
  induction xs generalizing acc with
  | nil => exact List.Perm.refl _
  | cons x rest ih =>
    simp only [bubblePassAux]
    split
    · exact (List.Perm.cons x (ih acc)).trans (List.Perm.swap acc x rest)
    · exact List.Perm.cons acc (ih x)

/-- One pass of bubble sort produces a permutation of the input. -/
theorem bubblePass_perm (l : List Nat) : List.Perm (bubblePass l) l := by
  match l with
  | [] => exact List.Perm.refl _
  | x :: xs => exact bubblePassAux_perm x xs

/-- Repeated bubble passes preserve the permutation relation. -/
theorem bubbleSortAux_perm (l : List Nat) (k : Nat) :
    List.Perm (bubbleSortAux l k) l := by
  induction k generalizing l with
  | zero => exact List.Perm.refl _
  | succ k' ih => exact (ih (bubblePass l)).trans (bubblePass_perm l)

/-- `bubbleSort` produces a permutation of its input. -/
theorem bubbleSort_perm (l : List Nat) : List.Perm (bubbleSort l) l :=
  bubbleSortAux_perm l l.length

/-- `bubbleSort` preserves length. -/
theorem bubbleSort_length (l : List Nat) :
    (bubbleSort l).length = l.length :=
  (bubbleSort_perm l).length_eq

/-! ## Fixed-point characterization -/

/-- If `bubblePassAux acc xs` returns `acc :: xs` unchanged, then `acc :: xs` is sorted. -/
theorem bubblePassAux_fixed_sorted (acc : Nat) (xs : List Nat)
    (h : bubblePassAux acc xs = acc :: xs) : IsSorted (acc :: xs) := by
  induction xs generalizing acc with
  | nil => exact List.Pairwise.cons (fun _ hb => nomatch hb) List.Pairwise.nil
  | cons y rest ih =>
    simp only [bubblePassAux] at h
    split at h
    · rename_i h_gt
      have := (List.cons.inj h).1
      omega
    · rename_i h_ngt
      have h_le : acc ≤ y := by omega
      have h_tail := (List.cons.inj h).2
      have h_sorted_tail := ih y h_tail
      exact List.Pairwise.cons (fun b hb => by
        simp only [List.mem_cons] at hb
        rcases hb with rfl | hb
        · exact h_le
        · exact Nat.le_trans h_le (List.rel_of_pairwise_cons h_sorted_tail hb)
      ) h_sorted_tail

/-- If a bubble pass leaves the list unchanged, the list is sorted. -/
theorem bubblePass_fixed_sorted (l : List Nat) (h : bubblePass l = l) : IsSorted l := by
  match l with
  | [] => exact List.Pairwise.nil
  | x :: xs => exact bubblePassAux_fixed_sorted x xs h

/-- If `acc :: xs` is sorted, then `bubblePassAux acc xs = acc :: xs`. -/
theorem bubblePassAux_sorted_id (acc : Nat) (xs : List Nat)
    (h : IsSorted (acc :: xs)) : bubblePassAux acc xs = acc :: xs := by
  induction xs generalizing acc with
  | nil => rfl
  | cons y rest ih =>
    have h_le : acc ≤ y := List.rel_of_pairwise_cons h (List.mem_cons.mpr (Or.inl rfl))
    simp only [bubblePassAux]
    split
    · exfalso; omega
    · congr 1
      have h_tail : IsSorted (y :: rest) := by cases h with | cons _ hr => exact hr
      exact ih y h_tail

/-- A sorted list is a fixed point of `bubblePass`. -/
theorem bubblePass_sorted_id (l : List Nat) (h : IsSorted l) : bubblePass l = l := by
  match l with
  | [] => rfl
  | x :: xs => exact bubblePassAux_sorted_id x xs h

end Cslib.Algorithms.Sorting.BubbleSort
