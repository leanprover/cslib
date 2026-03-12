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
# Selection Sort

This file implements selection sort on lists of natural numbers and proves that the result
is sorted, a permutation of the input, and preserves length.

## Main definitions

- `extractMin`: Find and remove the minimum element from a non-empty list.
- `selectionSortAux`: Fuel-based selection sort helper.
- `selectionSort`: Top-level selection sort.

## Main results

- `selectionSort_sorted`: The output of `selectionSort` is sorted.
- `selectionSort_perm`: The output is a permutation of the input.
- `selectionSort_length`: The output has the same length as the input.

## References

Adapted from the VeriBench benchmark (https://github.com/brandomiranda/veribench).
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Sorting.SelectionSort

/-- A list is sorted in ascending order. -/
abbrev IsSorted (l : List Nat) : Prop := List.Pairwise (· ≤ ·) l

/-- Extract the minimum element from a non-empty list, returning it and the remaining elements.
Returns `(0, [])` for the empty list (should not be called on empty lists). -/
def extractMin : List Nat → Nat × List Nat
  | [] => (0, [])
  | [x] => (x, [])
  | x :: y :: xs =>
    let (minTail, restTail) := extractMin (y :: xs)
    if x ≤ minTail then
      (x, y :: xs)
    else
      (minTail, x :: restTail)

/-- Fuel-based selection sort: repeatedly extracts the minimum. -/
def selectionSortAux (l : List Nat) : Nat → List Nat
  | 0 => []
  | fuel + 1 =>
    match l with
    | [] => []
    | _ :: _ =>
      let (minVal, rest) := extractMin l
      minVal :: selectionSortAux rest fuel

/-- Sort a list using selection sort. -/
def selectionSort (l : List Nat) : List Nat :=
  selectionSortAux l l.length

/-! ## Tests -/

example : selectionSort [3, 1, 2] = [1, 2, 3] := by decide
example : selectionSort [] = ([] : List Nat) := by decide
example : selectionSort [1] = [1] := by decide
example : selectionSort [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by decide
example : selectionSort [2, 1] = [1, 2] := by decide

/-! ## Properties of extractMin -/

/-- The minimum extracted is ≤ every element of the original list. -/
theorem extractMin_fst_le :
    (l : List Nat) → l ≠ [] → ∀ y ∈ l, (extractMin l).1 ≤ y
  | [], h, _, _ => absurd rfl h
  | [x], _, y, hy => by simp only [extractMin, List.mem_singleton] at hy ⊢; omega
  | x :: z :: zs, _, y, hy => by
    simp only [extractMin]
    split
    · rename_i h_le
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact Nat.le_refl _
      · exact Nat.le_trans h_le
          (extractMin_fst_le (z :: zs) (List.cons_ne_nil z zs) y (List.mem_cons.mpr hy))
    · rename_i h_nle
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact Nat.le_of_lt (Nat.lt_of_not_le h_nle)
      · exact extractMin_fst_le (z :: zs) (List.cons_ne_nil z zs) y (List.mem_cons.mpr hy)

/-- Extracting gives a pair whose components form a permutation of the original list. -/
theorem extractMin_perm :
    (l : List Nat) → l ≠ [] →
    List.Perm ((extractMin l).1 :: (extractMin l).2) l
  | [], h => absurd rfl h
  | [_], _ => List.Perm.refl _
  | x :: z :: zs, _ => by
    simp only [extractMin]
    split
    · exact List.Perm.refl _
    · have ih := extractMin_perm (z :: zs) (List.cons_ne_nil z zs)
      exact (List.Perm.swap x (extractMin (z :: zs)).1 (extractMin (z :: zs)).2).trans
        (List.Perm.cons x ih)

/-- The rest after `extractMin` has one fewer element. -/
theorem extractMin_snd_length :
    (l : List Nat) → l ≠ [] → (extractMin l).2.length + 1 = l.length
  | [], h => absurd rfl h
  | [_], _ => by simp [extractMin]
  | x :: z :: zs, _ => by
    simp only [extractMin]
    split
    · simp
    · have ih := extractMin_snd_length (z :: zs) (List.cons_ne_nil z zs)
      simp only [List.length_cons] at ih ⊢
      omega

/-! ## Permutation proof -/

/-- `selectionSortAux l fuel` is a permutation of `l` when fuel ≥ l.length. -/
theorem selectionSortAux_perm (l : List Nat) (fuel : Nat) (hfuel : fuel ≥ l.length) :
    List.Perm (selectionSortAux l fuel) l := by
  induction fuel generalizing l with
  | zero =>
    match l with
    | [] => exact List.Perm.refl _
    | _ :: _ => exfalso; simp only [List.length_cons] at hfuel; omega
  | succ n ih =>
    match l with
    | [] => exact List.Perm.refl _
    | x :: xs =>
      simp only [selectionSortAux]
      have h_len := extractMin_snd_length (x :: xs) (List.cons_ne_nil x xs)
      have h_fuel : n ≥ (extractMin (x :: xs)).2.length := by omega
      exact (List.Perm.cons _ (ih _ h_fuel)).trans
        (extractMin_perm (x :: xs) (List.cons_ne_nil x xs))

/-- `selectionSort` produces a permutation of its input. -/
theorem selectionSort_perm (l : List Nat) : List.Perm (selectionSort l) l :=
  selectionSortAux_perm l l.length (Nat.le_refl _)

/-- `selectionSort` preserves length. -/
theorem selectionSort_length (l : List Nat) :
    (selectionSort l).length = l.length :=
  (selectionSort_perm l).length_eq

/-! ## Sorted proof -/

/-- `selectionSortAux l fuel` is sorted when fuel ≥ l.length. -/
theorem selectionSortAux_sorted (l : List Nat) (fuel : Nat) (hfuel : fuel ≥ l.length) :
    IsSorted (selectionSortAux l fuel) := by
  induction fuel generalizing l with
  | zero =>
    match l with
    | [] => exact List.Pairwise.nil
    | _ :: _ => exfalso; simp only [List.length_cons] at hfuel; omega
  | succ n ih =>
    match l with
    | [] => exact List.Pairwise.nil
    | x :: xs =>
      simp only [selectionSortAux]
      have h_ne := List.cons_ne_nil x xs
      have h_len := extractMin_snd_length (x :: xs) h_ne
      have h_fuel : n ≥ (extractMin (x :: xs)).2.length := by omega
      have h_sorted_rest := ih _ h_fuel
      have h_perm_rest := selectionSortAux_perm _ n h_fuel
      exact List.Pairwise.cons (fun y hy => by
        have h_in_rest : y ∈ (extractMin (x :: xs)).2 := h_perm_rest.mem_iff.mp hy
        have h_perm_em := extractMin_perm (x :: xs) h_ne
        have h_in_orig : y ∈ x :: xs :=
          h_perm_em.mem_iff.mp (List.mem_cons.mpr (Or.inr h_in_rest))
        exact extractMin_fst_le (x :: xs) h_ne y h_in_orig
      ) h_sorted_rest

/-- `selectionSort` produces a sorted list. -/
theorem selectionSort_sorted (l : List Nat) : IsSorted (selectionSort l) :=
  selectionSortAux_sorted l l.length (Nat.le_refl _)

end Cslib.Algorithms.Sorting.SelectionSort
