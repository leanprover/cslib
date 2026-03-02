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
# Heap Sort

This file implements heap sort on lists of natural numbers and proves that the result
is a permutation of the input and preserves length.

## Main definitions

- `swap`: Swap two elements in a list.
- `findLargest`: Find the largest among a node and its children in a heap.
- `heapify`: Fuel-based sift-down to maintain max-heap property.
- `buildMaxHeap`: Build a max heap from a list.
- `heapSort`: Top-level heap sort.

## Main results

- `heapSort_perm`: The output is a permutation of the input.
- `heapSort_length`: The output has the same length as the input.

## References

Adapted from the VeriBench benchmark (https://github.com/brandomiranda/veribench).
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Sorting.HeapSort

/-- Left child index in a heap. -/
def leftChild (i : Nat) : Nat := 2 * i + 1

/-- Right child index in a heap. -/
def rightChild (i : Nat) : Nat := 2 * i + 2

/-- Swap two elements at given indices in a list. -/
def swap (l : List Nat) (i j : Nat) : List Nat :=
  match l[i]?, l[j]? with
  | some a, some b => (l.set i b).set j a
  | _, _ => l

/-- Find the index of the largest element among node `i` and its children. -/
def findLargest (l : List Nat) (i heapSize : Nat) : Nat :=
  let left := leftChild i
  let right := rightChild i
  let largest :=
    if left < heapSize ∧ left < l.length then
      match l[i]?, l[left]? with
      | some vi, some vl => if vl > vi then left else i
      | _, _ => i
    else i
  if right < heapSize ∧ right < l.length then
    match l[largest]?, l[right]? with
    | some vl, some vr => if vr > vl then right else largest
    | _, _ => largest
  else largest

/-- Fuel-based sift-down to maintain max-heap property. -/
def heapify (l : List Nat) (i : Nat) (heapSize fuel : Nat) : List Nat :=
  match fuel with
  | 0 => l
  | fuel' + 1 =>
    if i < heapSize ∧ i < l.length then
      let largest := findLargest l i heapSize
      if largest ≠ i then
        heapify (swap l i largest) largest heapSize fuel'
      else l
    else l

/-- Build max heap: sift down from last parent to root. -/
def buildMaxHeapAux (l : List Nat) (len : Nat) : Nat → List Nat
  | 0 => heapify l 0 len len
  | i + 1 => buildMaxHeapAux (heapify l (i + 1) len len) len i

/-- Build a max heap from a list. -/
def buildMaxHeap (l : List Nat) : List Nat :=
  if l.length ≤ 1 then l
  else buildMaxHeapAux l l.length ((l.length - 1 - 1) / 2)

/-- Extract-max loop: swap root with last unsorted, sift down, repeat. -/
def heapSortAux (l : List Nat) (heapSize fuel : Nat) : List Nat :=
  match fuel with
  | 0 => l
  | fuel' + 1 =>
    if heapSize ≤ 1 then l
    else
      let swapped := swap l 0 (heapSize - 1)
      let heapified := heapify swapped 0 (heapSize - 1) (heapSize - 1)
      heapSortAux heapified (heapSize - 1) fuel'

/-- Sort a list using heap sort. -/
def heapSort (l : List Nat) : List Nat :=
  if l.length ≤ 1 then l
  else
    let heap := buildMaxHeap l
    heapSortAux heap l.length l.length

/-! ## Tests -/

example : heapSort [3, 1, 2] = [1, 2, 3] := by decide
example : heapSort [] = ([] : List Nat) := by decide
example : heapSort [1] = [1] := by decide
example : heapSort [5, 2, 4, 6, 1, 3] = [1, 2, 3, 4, 5, 6] := by decide
example : heapSort [2, 1] = [1, 2] := by decide
example : heapSort [3, 1, 4, 1, 2, 3] = [1, 1, 2, 3, 3, 4] := by decide

/-! ## Swap properties -/

/-- Swap preserves length. -/
theorem swap_length (l : List Nat) (i j : Nat) :
    (swap l i j).length = l.length := by
  simp only [swap]
  cases l[i]? with
  | none => rfl
  | some _ =>
    cases l[j]? with
    | none => rfl
    | some _ => simp only [List.length_set]

/-- Swap always produces a permutation. -/
theorem swap_perm (l : List Nat) (i j : Nat) :
    List.Perm (swap l i j) l := by
  by_cases hi : i < l.length <;> by_cases hj : j < l.length
  · simp only [swap, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj]
    rw [List.perm_iff_count]; intro a
    have hj' : j < (l.set i l[j]).length := by rw [List.length_set]; exact hj
    rw [List.count_set hj', List.count_set hi]
    simp only [List.getElem_set, ite_self, beq_iff_eq]
    clear hj'
    by_cases hia : l[i] = a <;> by_cases hja : l[j] = a
    · simp only [hia, hja, ite_true]
      have := List.count_pos_iff.mpr (hia ▸ List.getElem_mem (h := hi)); omega
    · simp only [hia, hja, ite_true, ite_false]
      have := List.count_pos_iff.mpr (hia ▸ List.getElem_mem (h := hi)); omega
    · simp only [hia, hja, ite_true, ite_false]
      have := List.count_pos_iff.mpr (hja ▸ List.getElem_mem (h := hj)); omega
    · simp only [hia, hja, ite_false]; omega
  · simp only [swap]; cases l[i]? with
    | none => exact List.Perm.refl _
    | some _ => simp only [List.getElem?_eq_none (by omega : l.length ≤ j)]; exact List.Perm.refl _
  · simp only [swap, List.getElem?_eq_none (by omega : l.length ≤ i)]; exact List.Perm.refl _
  · simp only [swap, List.getElem?_eq_none (by omega : l.length ≤ i)]; exact List.Perm.refl _

/-! ## Heapify preserves length and permutation -/

/-- Heapify preserves length. -/
theorem heapify_length (l : List Nat) (i heapSize fuel : Nat) :
    (heapify l i heapSize fuel).length = l.length := by
  induction fuel generalizing l i with
  | zero => rfl
  | succ n ih =>
    simp only [heapify]
    split
    · split
      · exact (ih _ _).trans (swap_length l i _)
      · rfl
    · rfl

/-- Heapify produces a permutation. -/
theorem heapify_perm (l : List Nat) (i heapSize fuel : Nat) :
    List.Perm (heapify l i heapSize fuel) l := by
  induction fuel generalizing l i with
  | zero => exact List.Perm.refl _
  | succ n ih =>
    simp only [heapify]
    split
    · split
      · exact (ih _ _).trans (swap_perm l i _)
      · exact List.Perm.refl _
    · exact List.Perm.refl _

/-! ## BuildMaxHeap preserves length and permutation -/

/-- buildMaxHeapAux preserves length. -/
theorem buildMaxHeapAux_length (l : List Nat) (len : Nat) :
    (i : Nat) → (buildMaxHeapAux l len i).length = l.length
  | 0 => heapify_length l 0 len len
  | i + 1 => by
    simp only [buildMaxHeapAux]
    rw [buildMaxHeapAux_length, heapify_length]

/-- buildMaxHeap preserves length. -/
theorem buildMaxHeap_length (l : List Nat) :
    (buildMaxHeap l).length = l.length := by
  simp only [buildMaxHeap]
  split
  · rfl
  · exact buildMaxHeapAux_length l l.length _

/-- buildMaxHeapAux produces a permutation. -/
theorem buildMaxHeapAux_perm (l : List Nat) (len : Nat) :
    (i : Nat) → List.Perm (buildMaxHeapAux l len i) l
  | 0 => heapify_perm l 0 len len
  | i + 1 => by
    simp only [buildMaxHeapAux]
    exact (buildMaxHeapAux_perm _ len i).trans (heapify_perm l (i + 1) len len)

/-- buildMaxHeap produces a permutation. -/
theorem buildMaxHeap_perm (l : List Nat) :
    List.Perm (buildMaxHeap l) l := by
  simp only [buildMaxHeap]
  split
  · exact List.Perm.refl _
  · exact buildMaxHeapAux_perm l l.length _

/-! ## HeapSort preserves length and permutation -/

/-- heapSortAux preserves length. -/
theorem heapSortAux_length (l : List Nat) (heapSize fuel : Nat) :
    (heapSortAux l heapSize fuel).length = l.length := by
  induction fuel generalizing l heapSize with
  | zero => rfl
  | succ n ih =>
    simp only [heapSortAux]
    split
    · rfl
    · rw [ih, heapify_length, swap_length]

/-- `heapSort` preserves length. -/
theorem heapSort_length (l : List Nat) :
    (heapSort l).length = l.length := by
  simp only [heapSort]
  split
  · rfl
  · rw [heapSortAux_length, buildMaxHeap_length]

/-- heapSortAux produces a permutation. -/
theorem heapSortAux_perm (l : List Nat) (heapSize fuel : Nat) :
    List.Perm (heapSortAux l heapSize fuel) l := by
  induction fuel generalizing l heapSize with
  | zero => exact List.Perm.refl _
  | succ n ih =>
    simp only [heapSortAux]
    split
    · exact List.Perm.refl _
    · exact (ih _ _).trans ((heapify_perm _ 0 _ _).trans (swap_perm l 0 _))

/-- `heapSort` produces a permutation of its input. -/
theorem heapSort_perm (l : List Nat) :
    List.Perm (heapSort l) l := by
  simp only [heapSort]
  split
  · exact List.Perm.refl _
  · exact (heapSortAux_perm _ l.length l.length).trans (buildMaxHeap_perm l)

end Cslib.Algorithms.Sorting.HeapSort
