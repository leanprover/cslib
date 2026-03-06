/-
Copyright (c) 2025 Brando Miranda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brando Miranda
-/

module

public import Cslib.Init

@[expose] public section

/-!
# Binary Search

This file defines a binary search algorithm on sorted lists and proves that when an index is
returned, it correctly points to the target element.

## Main definitions

- `binarySearchAux`: Recursive binary search with explicit bounds and fuel.
- `binarySearch`: Top-level binary search on a sorted `List Nat`.

## Main results

- `binarySearch_found`: If `binarySearch` returns `some idx`, then `arr[idx]? = some target`.
- `binarySearch_bounds`: If `binarySearch` returns `some idx`, then `idx < arr.length`.

## References

Adapted from the VeriBench benchmark (https://github.com/brandomiranda/veribench).
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Search.BinarySearch

/-- Recursive binary search helper with explicit left/right bounds.
Returns `some mid` when `arr[mid] = target`, `none` if not found.
The `fuel` parameter ensures termination. -/
def binarySearchAux (arr : List Nat) (target : Nat) (left right : Nat)
    (fuel : Nat) : Option Nat :=
  match fuel with
  | 0 => none
  | n + 1 =>
    if left > right then
      none
    else
      let mid := (left + right) / 2
      if h : mid < arr.length then
        let midVal := arr[mid]
        if midVal == target then
          some mid
        else if midVal < target then
          binarySearchAux arr target (mid + 1) right n
        else
          if mid == 0 then none else binarySearchAux arr target left (mid - 1) n
      else
        none

/-- Binary search for a target in a list. Returns `some idx` if `arr[idx] = target`,
or `none` if the target is not found. Assumes the list is sorted for correct behavior. -/
def binarySearch (arr : List Nat) (target : Nat) : Option Nat :=
  if arr.isEmpty then
    none
  else
    binarySearchAux arr target 0 (arr.length - 1) arr.length

/-! ## Tests -/

example : binarySearch [1, 2, 3, 4, 5] 3 = some 2 := by decide
example : binarySearch [] 1 = none := by decide
example : binarySearch [5] 5 = some 0 := by decide
example : binarySearch [1, 2, 3, 4, 5] 1 = some 0 := by decide
example : binarySearch [1, 2, 3, 4, 5] 5 = some 4 := by decide
example : binarySearch [1, 2, 3, 4, 5] 6 = none := by decide

/-! ## Soundness -/

/-- If `binarySearchAux` returns `some idx`, then `idx < arr.length` and
`arr[idx] = target`. -/
theorem binarySearchAux_found (arr : List Nat) (target left right : Nat) (fuel : Nat)
    (idx : Nat) (h : binarySearchAux arr target left right fuel = some idx) :
    ∃ (h_bound : idx < arr.length), arr[idx] = target := by
  induction fuel generalizing left right with
  | zero => simp [binarySearchAux] at h
  | succ n ih =>
    simp only [binarySearchAux] at h
    split at h
    · simp at h
    · split at h
      · split at h
        · rename_i h_bound h_eq
          have h_idx : idx = (left + right) / 2 := by simpa using h.symm
          subst h_idx
          exact ⟨h_bound, by
            have := beq_iff_eq.mp ‹_›
            exact this⟩
        · split at h
          · exact ih _ _ h
          · split at h
            · simp at h
            · exact ih _ _ h
      · simp at h

/-- If `binarySearch` returns `some idx`, then `arr[idx]? = some target`. -/
theorem binarySearch_found (arr : List Nat) (target idx : Nat)
    (h : binarySearch arr target = some idx) :
    arr[idx]? = some target := by
  unfold binarySearch at h
  split at h
  · simp at h
  · obtain ⟨h_bound, h_val⟩ := binarySearchAux_found arr target 0 (arr.length - 1) arr.length idx h
    simp [List.getElem?_eq_getElem h_bound, h_val]

/-- If `binarySearch` returns `some idx`, then `idx < arr.length`. -/
theorem binarySearch_bounds (arr : List Nat) (target idx : Nat)
    (h : binarySearch arr target = some idx) :
    idx < arr.length := by
  unfold binarySearch at h
  split at h
  · simp at h
  · exact (binarySearchAux_found arr target 0 (arr.length - 1) arr.length idx h).1

end Cslib.Algorithms.Search.BinarySearch
