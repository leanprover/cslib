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
# Quick Sort

This file implements quick sort on lists of natural numbers and proves that the result
is sorted, a permutation of the input, and preserves length.

## Main definitions

- `partition`: Split a list into elements ≤ pivot and elements > pivot.
- `quickSort`: Fuel-based quick sort.

## Main results

- `sort_sorted`: The output of `sort` is sorted.
- `sort_perm`: The output is a permutation of the input.
- `sort_length`: The output has the same length as the input.

## References

Adapted from the VeriBench benchmark (https://github.com/brandomiranda/veribench).
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Sorting.QuickSort

/-- A list is sorted in ascending order. -/
abbrev IsSorted (l : List Nat) : Prop := List.Pairwise (· ≤ ·) l

/-- Partition a list into elements ≤ pivot and elements > pivot. -/
def partition (pivot : Nat) : List Nat → List Nat × List Nat
  | [] => ([], [])
  | x :: xs =>
    let (lo, hi) := partition pivot xs
    if x ≤ pivot then (x :: lo, hi) else (lo, x :: hi)

/-- Fuel-based quick sort. -/
def quickSort : List Nat → Nat → List Nat
  | _, 0 => []
  | [], _ => []
  | pivot :: tail, fuel + 1 =>
    let (lo, hi) := partition pivot tail
    quickSort lo fuel ++ [pivot] ++ quickSort hi fuel

/-- Top-level quick sort. -/
def sort (l : List Nat) : List Nat := quickSort l l.length

/-! ## Tests -/

example : sort [3, 1, 2] = [1, 2, 3] := by decide
example : sort [] = ([] : List Nat) := by decide
example : sort [1] = [1] := by decide
example : sort [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by decide
example : sort [2, 1] = [1, 2] := by decide

/-! ## Properties of partition -/

/-- The sum of partition lengths equals the input length. -/
theorem partition_length (pivot : Nat) :
    (xs : List Nat) → (partition pivot xs).1.length + (partition pivot xs).2.length = xs.length
  | [] => by simp [partition]
  | x :: xs => by
    simp only [partition]
    have ih := partition_length pivot xs
    split <;> simp only [List.length_cons] <;> omega

/-- Every element of the first component is ≤ the pivot. -/
theorem partition_fst_le (pivot : Nat) :
    (xs : List Nat) → ∀ y ∈ (partition pivot xs).1, y ≤ pivot
  | [], _, hy => by simp [partition] at hy
  | x :: xs, y, hy => by
    simp only [partition] at hy
    split at hy
    · rename_i h_le
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact h_le
      · exact partition_fst_le pivot xs y hy
    · exact partition_fst_le pivot xs y hy

/-- Every element of the second component is > the pivot. -/
theorem partition_snd_gt (pivot : Nat) :
    (xs : List Nat) → ∀ y ∈ (partition pivot xs).2, pivot < y
  | [], _, hy => by simp [partition] at hy
  | x :: xs, y, hy => by
    simp only [partition] at hy
    split at hy
    · exact partition_snd_gt pivot xs y hy
    · rename_i h_nle
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact Nat.lt_of_not_le h_nle
      · exact partition_snd_gt pivot xs y hy

/-- Partition produces a permutation of the input. -/
theorem partition_perm (pivot : Nat) :
    (xs : List Nat) →
    List.Perm ((partition pivot xs).1 ++ (partition pivot xs).2) xs
  | [] => List.Perm.refl _
  | x :: xs => by
    simp only [partition]
    have ih := partition_perm pivot xs
    split
    · simp only [List.cons_append]
      exact (List.perm_cons x).mpr ih
    · exact List.perm_middle.trans ((List.perm_cons x).mpr ih)

/-- First component of partition is no longer than input. -/
theorem partition_fst_length (pivot : Nat) (xs : List Nat) :
    (partition pivot xs).1.length ≤ xs.length := by
  have := partition_length pivot xs; omega

/-- Second component of partition is no longer than input. -/
theorem partition_snd_length (pivot : Nat) (xs : List Nat) :
    (partition pivot xs).2.length ≤ xs.length := by
  have := partition_length pivot xs; omega

/-! ## Permutation proof -/

/-- `quickSort l fuel` is a permutation of `l` when fuel ≥ l.length. -/
theorem quickSort_perm (l : List Nat) (fuel : Nat) (hfuel : fuel ≥ l.length) :
    List.Perm (quickSort l fuel) l := by
  induction fuel generalizing l with
  | zero =>
    match l with
    | [] => exact List.Perm.refl _
    | _ :: _ => exfalso; simp only [List.length_cons] at hfuel; omega
  | succ n ih =>
    match l with
    | [] => exact List.Perm.refl _
    | pivot :: tail =>
      simp only [quickSort]
      have h_fuel_fst : n ≥ (partition pivot tail).1.length := by
        have := partition_fst_length pivot tail
        simp only [List.length_cons] at hfuel; omega
      have h_fuel_snd : n ≥ (partition pivot tail).2.length := by
        have := partition_snd_length pivot tail
        simp only [List.length_cons] at hfuel; omega
      have ih_lo := ih _ h_fuel_fst
      have ih_hi := ih _ h_fuel_snd
      -- lo_sorted ++ [pivot] ++ hi_sorted
      -- = lo_sorted ++ (pivot :: hi_sorted)   by append_assoc + singleton
      -- ~ lo ++ (pivot :: hi)                  by append perm
      -- ~ pivot :: (lo ++ hi)                  by perm_middle.symm
      -- ~ pivot :: tail                        by cons partition_perm
      rw [List.append_assoc]
      exact (((List.Perm.append ih_lo (List.Perm.cons pivot ih_hi)).trans
        List.perm_middle).trans
        ((List.perm_cons pivot).mpr (partition_perm pivot tail)))

/-- `sort` produces a permutation of its input. -/
theorem sort_perm (l : List Nat) : List.Perm (sort l) l :=
  quickSort_perm l l.length (Nat.le_refl _)

/-- `sort` preserves length. -/
theorem sort_length (l : List Nat) : (sort l).length = l.length :=
  (sort_perm l).length_eq

/-! ## Sorted proof -/

/-- `quickSort l fuel` is sorted when fuel ≥ l.length. -/
theorem quickSort_sorted (l : List Nat) (fuel : Nat) (hfuel : fuel ≥ l.length) :
    IsSorted (quickSort l fuel) := by
  induction fuel generalizing l with
  | zero =>
    match l with
    | [] => exact List.Pairwise.nil
    | _ :: _ => exfalso; simp only [List.length_cons] at hfuel; omega
  | succ n ih =>
    match l with
    | [] => exact List.Pairwise.nil
    | pivot :: tail =>
      simp only [quickSort]
      have h_fuel_fst : n ≥ (partition pivot tail).1.length := by
        have := partition_fst_length pivot tail
        simp only [List.length_cons] at hfuel; omega
      have h_fuel_snd : n ≥ (partition pivot tail).2.length := by
        have := partition_snd_length pivot tail
        simp only [List.length_cons] at hfuel; omega
      have h_sorted_lo := ih _ h_fuel_fst
      have h_sorted_hi := ih _ h_fuel_snd
      have h_perm_lo := quickSort_perm _ n h_fuel_fst
      have h_perm_hi := quickSort_perm _ n h_fuel_snd
      -- Goal: sorted(lo_sorted ++ [pivot] ++ hi_sorted)
      rw [List.append_assoc]
      apply List.pairwise_append.mpr
      constructor
      · exact h_sorted_lo
      constructor
      · exact List.Pairwise.cons
          (fun b hb => Nat.le_of_lt
            (partition_snd_gt pivot tail b (h_perm_hi.mem_iff.mp hb)))
          h_sorted_hi
      · intro a ha b hb
        have ha' := partition_fst_le pivot tail a (h_perm_lo.mem_iff.mp ha)
        rcases List.mem_cons.mp hb with rfl | hb
        · exact ha'
        · exact Nat.le_of_lt (Nat.lt_of_le_of_lt ha'
            (partition_snd_gt pivot tail b (h_perm_hi.mem_iff.mp hb)))

/-- `sort` produces a sorted list. -/
theorem sort_sorted (l : List Nat) : IsSorted (sort l) :=
  quickSort_sorted l l.length (Nat.le_refl _)

end Cslib.Algorithms.Sorting.QuickSort
