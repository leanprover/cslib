/-
Copyright (c) 2025 Brando Miranda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brando Miranda
-/

module

public import Cslib.Init

@[expose] public section

/-!
# Longest Common Subsequence

This file implements the longest common subsequence (LCS) algorithm on lists of natural numbers
and proves key correctness properties.

## Main definitions

- `lcs`: Fuel-based LCS computation.
- `longestCommonSubsequence`: Top-level LCS.

## Main results

- `lcs_sublist_left`: The LCS is a sublist of the first input.
- `lcs_sublist_right`: The LCS is a sublist of the second input.
- `lcs_length_le_left`: The LCS length is bounded by the first input length.
- `lcs_length_le_right`: The LCS length is bounded by the second input length.
- `lcs_self`: The LCS of a list with itself is the list.

## References

Adapted from the VeriBench benchmark (https://github.com/brandomiranda/veribench).
-/

set_option autoImplicit false

namespace Cslib.Algorithms.DynamicProgramming.LCS

/-- Fuel-based longest common subsequence. -/
def lcs : List Nat → List Nat → Nat → List Nat
  | _, _, 0 => []
  | [], _, _ => []
  | _, [], _ => []
  | x :: xs, y :: ys, fuel + 1 =>
    if x = y then x :: lcs xs ys fuel
    else
      let r1 := lcs (x :: xs) ys fuel
      let r2 := lcs xs (y :: ys) fuel
      if r1.length ≥ r2.length then r1 else r2

/-- Top-level LCS. Uses fuel = sum of input lengths. -/
def longestCommonSubsequence (l1 l2 : List Nat) : List Nat :=
  lcs l1 l2 (l1.length + l2.length)

/-! ## Tests -/

example : longestCommonSubsequence [1, 2, 3, 4] [1, 3, 5] = [1, 3] := by decide
example : longestCommonSubsequence [] [1, 2, 3] = ([] : List Nat) := by decide
example : longestCommonSubsequence [1, 2, 3] [] = ([] : List Nat) := by decide
example : longestCommonSubsequence [1, 2, 3] [1, 2, 3] = [1, 2, 3] := by decide
example : longestCommonSubsequence [1, 2, 3, 4, 5] [2, 4, 6] = [2, 4] := by decide
example : longestCommonSubsequence [3, 5, 7, 9] [1, 3, 6, 7, 8] = [3, 7] := by decide

/-! ## Sublist proofs -/

/-- `lcs l1 l2 fuel` is a sublist of `l1` when fuel ≥ l1.length + l2.length. -/
theorem lcs_sublist_left (l1 l2 : List Nat) (fuel : Nat)
    (hfuel : fuel ≥ l1.length + l2.length) :
    (lcs l1 l2 fuel).Sublist l1 := by
  induction fuel generalizing l1 l2 with
  | zero =>
    match l1 with
    | [] => exact List.Sublist.slnil
    | _ :: _ => exfalso; simp only [List.length_cons] at hfuel; omega
  | succ n ih =>
    match l1, l2 with
    | [], _ => exact List.Sublist.slnil
    | _ :: _, [] => exact List.nil_sublist _
    | x :: xs, y :: ys =>
      simp only [lcs]
      split
      · exact (ih xs ys (by simp only [List.length_cons] at hfuel ⊢; omega)).cons₂ _
      · split
        · exact ih (x :: xs) ys (by simp only [List.length_cons] at hfuel ⊢; omega)
        · exact (ih xs (y :: ys)
            (by simp only [List.length_cons] at hfuel ⊢; omega)).cons _

/-- `lcs l1 l2 fuel` is a sublist of `l2` when fuel ≥ l1.length + l2.length. -/
theorem lcs_sublist_right (l1 l2 : List Nat) (fuel : Nat)
    (hfuel : fuel ≥ l1.length + l2.length) :
    (lcs l1 l2 fuel).Sublist l2 := by
  induction fuel generalizing l1 l2 with
  | zero =>
    match l2 with
    | [] => exact List.Sublist.slnil
    | _ :: _ =>
      match l1 with
      | [] => exact List.nil_sublist _
      | _ :: _ => exfalso; simp only [List.length_cons] at hfuel; omega
  | succ n ih =>
    match l1, l2 with
    | [], _ => exact List.nil_sublist _
    | _ :: _, [] => exact List.Sublist.slnil
    | x :: xs, y :: ys =>
      simp only [lcs]
      split
      · rename_i h_eq; rw [h_eq]
        exact (ih xs ys (by simp only [List.length_cons] at hfuel ⊢; omega)).cons₂ _
      · split
        · exact (ih (x :: xs) ys
            (by simp only [List.length_cons] at hfuel ⊢; omega)).cons _
        · exact ih xs (y :: ys) (by simp only [List.length_cons] at hfuel ⊢; omega)

/-! ## Length bounds -/

/-- LCS length is bounded by the first input length. -/
theorem lcs_length_le_left (l1 l2 : List Nat) (fuel : Nat)
    (hfuel : fuel ≥ l1.length + l2.length) :
    (lcs l1 l2 fuel).length ≤ l1.length :=
  (lcs_sublist_left l1 l2 fuel hfuel).length_le

/-- LCS length is bounded by the second input length. -/
theorem lcs_length_le_right (l1 l2 : List Nat) (fuel : Nat)
    (hfuel : fuel ≥ l1.length + l2.length) :
    (lcs l1 l2 fuel).length ≤ l2.length :=
  (lcs_sublist_right l1 l2 fuel hfuel).length_le

/-! ## Self-LCS -/

/-- The LCS of a list with itself is the list itself. -/
theorem lcs_self (l : List Nat) (fuel : Nat) (hfuel : fuel ≥ l.length + l.length) :
    lcs l l fuel = l := by
  induction fuel generalizing l with
  | zero =>
    match l with
    | [] => rfl
    | _ :: _ => exfalso; simp only [List.length_cons] at hfuel; omega
  | succ n ih =>
    match l with
    | [] => rfl
    | x :: xs =>
      simp only [lcs, ite_true]
      congr 1
      exact ih xs (by simp only [List.length_cons] at hfuel; omega)

/-- Top-level: LCS of a list with itself. -/
theorem longestCommonSubsequence_self (l : List Nat) :
    longestCommonSubsequence l l = l :=
  lcs_self l (l.length + l.length) (Nat.le_refl _)

end Cslib.Algorithms.DynamicProgramming.LCS
