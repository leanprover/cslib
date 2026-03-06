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
# Counting Sort

This file implements counting sort on lists of natural numbers and proves that the result
is sorted, a permutation of the input, and preserves length.

## Main definitions

- `findMax`: Find the maximum element of a list.
- `buildSorted`: Reconstruct a sorted list from a count array.
- `countingSort`: Top-level counting sort.

## Main results

- `countingSort_sorted`: The output of `countingSort` is sorted.
- `countingSort_perm`: The output is a permutation of the input.
- `countingSort_length`: The output has the same length as the input.

## References

Adapted from the VeriBench benchmark (https://github.com/brandomiranda/veribench).
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Sorting.CountingSort

/-- A list is sorted in ascending order. -/
abbrev IsSorted (l : List Nat) : Prop := List.Pairwise (· ≤ ·) l

/-- Find the maximum element of a list (0 for empty list). -/
def findMax : List Nat → Nat
  | [] => 0
  | x :: xs => Nat.max x (findMax xs)

/-- Build a sorted list from a count array starting at index `i`.
Each entry `counts[j]` tells how many copies of `i + j` to emit. -/
def buildSorted : List Nat → Nat → List Nat
  | [], _ => []
  | c :: cs, i => List.replicate c i ++ buildSorted cs (i + 1)

/-- Sort a list using counting sort. -/
def countingSort (l : List Nat) : List Nat :=
  match l with
  | [] => []
  | _ =>
    let m := findMax l
    buildSorted ((List.range (m + 1)).map (fun i => l.count i)) 0

/-! ## Tests -/

example : countingSort [3, 1, 2] = [1, 2, 3] := by decide
example : countingSort [] = ([] : List Nat) := by decide
example : countingSort [1] = [1] := by decide
example : countingSort [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by decide
example : countingSort [2, 1] = [1, 2] := by decide
example : countingSort [3, 1, 2, 1, 3, 2] = [1, 1, 2, 2, 3, 3] := by decide
example : countingSort [1, 0, 2, 0, 1, 0] = [0, 0, 0, 1, 1, 2] := by decide

/-! ## Properties of findMax -/

/-- Every element of a list is ≤ findMax. -/
theorem findMax_ge (l : List Nat) : ∀ x ∈ l, x ≤ findMax l := by
  intro x hx
  induction l with
  | nil => nomatch hx
  | cons a as ih =>
    simp only [findMax, List.mem_cons] at hx ⊢
    rcases hx with rfl | hx
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hx) (Nat.le_max_right _ _)

/-- If a > findMax l, then a does not appear in l. -/
theorem findMax_count_zero (l : List Nat) (a : Nat) (h : findMax l < a) :
    l.count a = 0 := by
  rw [List.count_eq_zero]
  intro ha
  have := findMax_ge l a ha; omega

/-! ## Helpers for replicate count -/

private theorem count_replicate_self (n a : Nat) :
    (List.replicate n a).count a = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ, List.count_cons_self, ih]

private theorem count_replicate_ne (n a b : Nat) (h : a ≠ b) :
    (List.replicate n b).count a = 0 := by
  rw [List.count_eq_zero]
  intro hm
  exact h (List.eq_of_mem_replicate hm)

/-! ## Properties of buildSorted -/

/-- All elements of `buildSorted counts i` are ≥ i. -/
theorem buildSorted_all_ge :
    (counts : List Nat) → (i : Nat) → ∀ x ∈ buildSorted counts i, i ≤ x
  | [], _, _, hx => nomatch hx
  | c :: cs, i, x, hx => by
    simp only [buildSorted, List.mem_append] at hx
    rcases hx with hx | hx
    · exact Nat.le_of_eq (List.eq_of_mem_replicate hx).symm
    · exact Nat.le_trans (Nat.le_succ i) (buildSorted_all_ge cs (i + 1) x hx)

/-- `buildSorted` produces a sorted list. -/
theorem buildSorted_sorted :
    (counts : List Nat) → (i : Nat) → IsSorted (buildSorted counts i)
  | [], _ => List.Pairwise.nil
  | c :: cs, i => by
    simp only [buildSorted]
    apply List.pairwise_append.mpr
    refine ⟨List.pairwise_replicate.mpr (Or.inr (Nat.le_refl i)),
            buildSorted_sorted cs (i + 1), fun a ha b hb => ?_⟩
    have h_eq := List.eq_of_mem_replicate ha
    have h_ge := buildSorted_all_ge cs (i + 1) b hb
    omega

/-- Count of elements < start index in `buildSorted` is zero. -/
theorem buildSorted_count_lt :
    (counts : List Nat) → (i a : Nat) → a < i → (buildSorted counts i).count a = 0
  | [], _, _, _ => rfl
  | c :: cs, i, a, h_lt => by
    simp only [buildSorted]
    rw [List.count_append, count_replicate_ne _ _ _ (by omega), Nat.zero_add]
    exact buildSorted_count_lt cs (i + 1) a (by omega)

/-- Count of element `i` at head position in `buildSorted`. -/
theorem buildSorted_count_head (c : Nat) (cs : List Nat) (i : Nat) :
    (buildSorted (c :: cs) i).count i = c := by
  simp only [buildSorted]
  rw [List.count_append, count_replicate_self,
      buildSorted_count_lt cs (i + 1) i (by omega)]
  omega

/-- Count of element `a > i` in `buildSorted (c :: cs) i` equals count in tail. -/
theorem buildSorted_count_tail (c : Nat) (cs : List Nat) (i a : Nat) (h : i < a) :
    (buildSorted (c :: cs) i).count a = (buildSorted cs (i + 1)).count a := by
  simp only [buildSorted]
  rw [List.count_append, count_replicate_ne _ _ _ (by omega), Nat.zero_add]

/-! ## Count characterization of buildSorted -/

/-- General count characterization: for `i ≤ a < i + counts.length`,
the count equals the corresponding entry. -/
theorem buildSorted_count (counts : List Nat) (i a : Nat) (h_ge : i ≤ a)
    (h_lt : a < i + counts.length) :
    (buildSorted counts i).count a = counts[a - i]'(by omega) := by
  induction counts generalizing i with
  | nil => simp only [List.length_nil] at h_lt; omega
  | cons c cs ih =>
    by_cases h_eq : a = i
    · subst h_eq
      simp only [buildSorted_count_head, Nat.sub_self, List.getElem_cons_zero]
    · have h_gt : i < a := by omega
      rw [buildSorted_count_tail c cs i a h_gt]
      rw [ih (i + 1) (by omega) (by simp only [List.length_cons] at h_lt; omega)]
      simp only [show a - i = (a - (i + 1)) + 1 from by omega,
        List.getElem_cons_succ]

/-- Count of element beyond the range is zero. -/
theorem buildSorted_count_ge (counts : List Nat) (i a : Nat) (h : i + counts.length ≤ a) :
    (buildSorted counts i).count a = 0 := by
  induction counts generalizing i with
  | nil => rfl
  | cons c cs ih =>
    have h_gt : i < a := by simp only [List.length_cons] at h; omega
    rw [buildSorted_count_tail c cs i a h_gt]
    exact ih (i + 1) (by simp only [List.length_cons] at h; omega)

/-! ## Permutation proof -/

/-- `countingSort` produces a permutation of its input. -/
theorem countingSort_perm (l : List Nat) : List.Perm (countingSort l) l := by
  match l with
  | [] => exact List.Perm.refl _
  | x :: xs =>
    simp only [countingSort]
    rw [List.perm_iff_count]
    intro a
    set m := findMax (x :: xs)
    set counts := (List.range (m + 1)).map (fun i => (x :: xs).count i)
    by_cases h_le : a ≤ m
    · have h_len : counts.length = m + 1 := by simp [counts]
      have h_lt : a < 0 + counts.length := by omega
      rw [buildSorted_count counts 0 a (Nat.zero_le a) h_lt]
      simp only [counts, Nat.sub_zero, List.getElem_map, List.getElem_range]
    · have h_fm : m < a := Nat.lt_of_not_le h_le
      rw [findMax_count_zero (x :: xs) a h_fm]
      by_cases h_lt : a < 0 + counts.length
      · rw [buildSorted_count counts 0 a (Nat.zero_le a) h_lt]
        simp only [counts, Nat.sub_zero, List.getElem_map, List.getElem_range]
        exact findMax_count_zero (x :: xs) a h_fm
      · exact buildSorted_count_ge counts 0 a (by omega)

/-- `countingSort` preserves length. -/
theorem countingSort_length (l : List Nat) :
    (countingSort l).length = l.length :=
  (countingSort_perm l).length_eq

/-! ## Sorted proof -/

/-- `countingSort` produces a sorted list. -/
theorem countingSort_sorted (l : List Nat) : IsSorted (countingSort l) := by
  match l with
  | [] => exact List.Pairwise.nil
  | _ :: _ => exact buildSorted_sorted _ 0

end Cslib.Algorithms.Sorting.CountingSort
