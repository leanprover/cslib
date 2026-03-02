/-
Copyright (c) 2025 Brando Miranda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brando Miranda
-/

module

public import Cslib.Init

@[expose] public section

/-!
# Edit Distance

This file implements the edit distance (Levenshtein distance) algorithm on lists of natural
numbers and proves key correctness properties.

## Main definitions

- `editDist`: Fuel-based edit distance computation.
- `editDistance`: Top-level edit distance.

## Main results

- `editDistance_self`: Edit distance from a list to itself is 0.
- `editDistance_nil_left`: Edit distance from empty list equals target length.
- `editDistance_nil_right`: Edit distance to empty list equals source length.
- `editDistance_le_sum`: Edit distance is bounded by the sum of input lengths.

## References

Adapted from the VeriBench benchmark (https://github.com/brandomiranda/veribench).
-/

set_option autoImplicit false

namespace Cslib.Algorithms.DynamicProgramming.EditDistance

/-- Fuel-based edit distance (Levenshtein distance). -/
def editDist : List Nat → List Nat → Nat → Nat
  | [], ys, _ => ys.length
  | xs, [], _ => xs.length
  | _, _, 0 => 0
  | x :: xs, y :: ys, fuel + 1 =>
    if x = y then editDist xs ys fuel
    else 1 + Nat.min (Nat.min
      (editDist xs (y :: ys) fuel)
      (editDist (x :: xs) ys fuel))
      (editDist xs ys fuel)

/-- Top-level edit distance. Uses fuel = sum of input lengths. -/
def editDistance (s1 s2 : List Nat) : Nat :=
  editDist s1 s2 (s1.length + s2.length)

/-! ## Tests -/

example : editDistance [1, 2, 3] [2, 2, 3] = 1 := by decide
example : editDistance [] ([] : List Nat) = 0 := by decide
example : editDistance [1, 2, 3] [1, 2, 3] = 0 := by decide
example : editDistance [1, 2, 3] [] = 3 := by decide
example : editDistance [] [1, 2, 3] = 3 := by decide
example : editDistance [1, 2, 3] [1, 2, 3, 4] = 1 := by decide
example : editDistance [1, 2, 3] [4, 5, 6] = 3 := by decide

/-! ## Reflexivity -/

/-- Edit distance from a list to itself is 0. -/
theorem editDist_self (l : List Nat) (fuel : Nat) (hfuel : fuel ≥ l.length + l.length) :
    editDist l l fuel = 0 := by
  induction fuel generalizing l with
  | zero =>
    match l with
    | [] => rfl
    | _ :: _ => exfalso; simp only [List.length_cons] at hfuel; omega
  | succ n ih =>
    match l with
    | [] => rfl
    | x :: xs =>
      simp only [editDist, ite_true]
      exact ih xs (by simp only [List.length_cons] at hfuel; omega)

/-- Top-level: edit distance from a list to itself is 0. -/
theorem editDistance_self (l : List Nat) : editDistance l l = 0 :=
  editDist_self l (l.length + l.length) (Nat.le_refl _)

/-! ## Empty list properties -/

/-- Edit distance from empty list equals target length. -/
theorem editDistance_nil_left (l : List Nat) : editDistance [] l = l.length := by
  simp [editDistance, editDist]

/-- Edit distance to empty list equals source length. -/
theorem editDistance_nil_right (l : List Nat) : editDistance l [] = l.length := by
  cases l <;> simp [editDistance, editDist]

/-! ## Upper bound -/

/-- Edit distance is bounded by the sum of input lengths. -/
theorem editDist_le_sum (l1 l2 : List Nat) (fuel : Nat)
    (hfuel : fuel ≥ l1.length + l2.length) :
    editDist l1 l2 fuel ≤ l1.length + l2.length := by
  induction fuel generalizing l1 l2 with
  | zero =>
    match l1, l2 with
    | [], [] => simp [editDist]
    | [], _ :: _ => simp only [editDist]; omega
    | _ :: _, _ => exfalso; simp only [List.length_cons] at hfuel; omega
  | succ n ih =>
    match l1, l2 with
    | [], _ => simp only [editDist]; omega
    | _ :: _, [] => simp only [editDist, List.length_cons]; omega
    | x :: xs, y :: ys =>
      simp only [editDist]
      split
      · -- x = y
        have := ih xs ys (by simp only [List.length_cons] at hfuel ⊢; omega)
        simp only [List.length_cons]; omega
      · -- x ≠ y: 1 + min3(del, ins, sub) ≤ l1.length + l2.length
        have h1 := ih xs (y :: ys) (by simp only [List.length_cons] at hfuel ⊢; omega)
        simp only [List.length_cons] at h1 ⊢
        have hmin : ((editDist xs (y :: ys) n).min (editDist (x :: xs) ys n)).min
            (editDist xs ys n) ≤ editDist xs (y :: ys) n :=
          Nat.le_trans (Nat.min_le_left _ _) (Nat.min_le_left _ _)
        omega

/-- Top-level: edit distance is bounded by the sum of input lengths. -/
theorem editDistance_le_sum (l1 l2 : List Nat) :
    editDistance l1 l2 ≤ l1.length + l2.length :=
  editDist_le_sum l1 l2 (l1.length + l2.length) (Nat.le_refl _)

end Cslib.Algorithms.DynamicProgramming.EditDistance
