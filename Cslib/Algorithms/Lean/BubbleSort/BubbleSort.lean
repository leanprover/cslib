/-
Copyright (c) 2026 Robert Joseph George. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George
-/

module

public import Cslib.Algorithms.Lean.Sorting
public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Data.Nat.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Finiteness.Attr
public import Batteries.Data.List.Lemmas

/-!
# Stable bubble sort on lists

`bubbleSort` returns a `TimeM ℕ (List α)`: the return value is the sorted list, and the time
component counts comparisons.

Each pass moves one maximal element to the end. Stability comes from the strict swap test: equal
elements are copied forward in their original order instead of being exchanged.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

variable {α : Type*} [LinearOrder α]

/--
One stable bubbling pass. `bubbleMax candidate xs` returns a prefix and a final element.
The final element is maximal among `candidate :: xs`.

The pass swaps only when the next value is strictly smaller than the current candidate. Equal values
are therefore never swapped, which is the local reason the full sort is stable.
-/
def bubbleMax : α → List α → TimeM ℕ (List α × α)
  | candidate, [] => return ([], candidate)
  | candidate, x :: xs => do
    ✓ let swap := x < candidate
    if swap then
      let result ← bubbleMax candidate xs
      return (x :: result.1, result.2)
    else
      let result ← bubbleMax x xs
      return (candidate :: result.1, result.2)

/-- A bubbling pass keeps exactly one element out of the prefix. -/
@[simp, grind =]
private theorem bubbleMax_length (candidate : α) (xs : List α) :
    (⟪bubbleMax candidate xs⟫).1.length = xs.length := by
  induction xs generalizing candidate with
  | nil => simp [bubbleMax]
  | cons x xs ih =>
    simp [bubbleMax]
    split <;> simp [ih]

/-- A bubbling pass performs one comparison for each element it scans. -/
@[simp, grind =]
private theorem bubbleMax_time (candidate : α) (xs : List α) :
    (bubbleMax candidate xs).time = xs.length := by
  induction xs generalizing candidate with
  | nil => simp [bubbleMax]
  | cons x xs ih =>
    simp [bubbleMax]
    split <;> simp [ih, Nat.add_comm]

/-- Sorts a list using stable bubble sort, counting comparisons as time cost. -/
def bubbleSort : List α → TimeM ℕ (List α)
  | [] => return []
  | x :: xs =>
    let pass := bubbleMax x xs
    let sortedPrefix := bubbleSort pass.ret.1
    ⟨sortedPrefix.ret ++ [pass.ret.2], pass.time + sortedPrefix.time⟩
termination_by xs => xs.length
decreasing_by
  simp_wf

section Correctness

/-- The final element produced by a bubbling pass is at least the initial candidate. -/
@[simp]
private theorem bubbleMax_candidate_le_output (candidate : α) (xs : List α) :
    candidate ≤ (⟪bubbleMax candidate xs⟫).2 := by
  induction xs generalizing candidate with
  | nil => simp [bubbleMax]
  | cons x xs ih =>
    by_cases h : x < candidate
      <;> simp only [bubbleMax, h, ↓reduceIte, ret_bind, ret_pure]
      <;> grind

/-- Every element left in the prefix of a bubbling pass is bounded by the final element. -/
@[simp]
private theorem bubbleMax_prefix_le_output (candidate : α) (xs : List α) :
    ∀ z ∈ (⟪bubbleMax candidate xs⟫).1, z ≤ (⟪bubbleMax candidate xs⟫).2 := by
  induction xs generalizing candidate with
  | nil => simp [bubbleMax]
  | cons x xs ih =>
    by_cases h : x < candidate
      <;> simp only [bubbleMax, h, ↓reduceIte, ret_bind, ret_pure, List.mem_cons]
      <;> intro z hz
      <;> rcases hz with rfl | hz
    · exact le_trans (le_of_lt h) (bubbleMax_candidate_le_output candidate xs)
    · exact ih candidate z hz
    · exact le_trans (le_of_not_gt h) (bubbleMax_candidate_le_output x xs)
    · exact ih x z hz

/-- A bubbling pass is a permutation of the candidate and the remaining input. -/
@[simp]
private theorem bubbleMax_perm (candidate : α) (xs : List α) :
    ((⟪bubbleMax candidate xs⟫).1 ++ [(⟪bubbleMax candidate xs⟫).2]).Perm
      (candidate :: xs) := by
  induction xs generalizing candidate with
  | nil => simp [bubbleMax]
  | cons x xs ih =>
    by_cases h : x < candidate
    · simpa only [bubbleMax, h, ↓reduceIte, ret_bind, ret_pure, List.cons_append] using
        (List.Perm.cons x (ih candidate)).trans (List.Perm.swap candidate x xs)
    · simpa only [bubbleMax, h, ↓reduceIte, ret_bind, ret_pure, List.cons_append] using
        List.Perm.cons candidate (ih x)

/--
A bubbling pass is stable. Since equal values are never swapped, filtering by any value gives the
same subsequence before and after the pass.
-/
private theorem bubbleMax_stable (candidate : α) (xs : List α) :
    StableByValue (candidate :: xs)
      ((⟪bubbleMax candidate xs⟫).1 ++ [(⟪bubbleMax candidate xs⟫).2]) := by
  induction xs generalizing candidate with
  | nil => simp [StableByValue, bubbleMax]
  | cons x xs ih =>
    intro y
    by_cases h : x < candidate
    · have := ih candidate y
      by_cases hxy : x = y <;> by_cases hcy : candidate = y <;> grind [bubbleMax]
    · have := ih x y
      by_cases hcy : candidate = y <;> grind [bubbleMax]

/-- Bubble sort returns a permutation of its input. -/
theorem bubbleSort_perm (xs : List α) : (⟪bubbleSort xs⟫).Perm xs := by
  fun_induction bubbleSort xs with
  | case1 => simp
  | case2 x xs pass _ ih =>
    exact (List.Perm.append_right [pass.ret.2] ih).trans (by simp [pass])

/-- Bubble sort is stable: equal values occur in the same order after sorting. -/
theorem bubbleSort_stable (xs : List α) : StableByValue xs ⟪bubbleSort xs⟫ := by
  fun_induction bubbleSort xs with
  | case1 => simp [StableByValue]
  | case2 x xs pass _ ih =>
    intro y
    simp only [List.filter_append]
    rw [ih y]
    simpa [pass, List.filter_append] using bubbleMax_stable x xs y

/--
Bubble sort returns a sorted list. The recursive call sorts the prefix, and `bubbleMax` proves every
prefix element is below the final element appended at the end.
-/
theorem bubbleSort_sorted (xs : List α) : List.Pairwise (· ≤ ·) ⟪bubbleSort xs⟫ := by
  fun_induction bubbleSort xs with
  | case1 => simp
  | case2 x xs pass _ ih =>
    change ((bubbleSort pass.ret.1).ret ++ [pass.ret.2]).Pairwise (· ≤ ·)
    rw [List.pairwise_append]
    have hprefix := bubbleMax_prefix_le_output x xs
    have hperm := bubbleSort_perm pass.ret.1
    grind

/-- Bubble sort is functionally correct. -/
theorem bubbleSort_correct (xs : List α) : List.Pairwise (· ≤ ·) ⟪bubbleSort xs⟫ ∧
    (⟪bubbleSort xs⟫).Perm xs ∧ StableByValue xs ⟪bubbleSort xs⟫ := by
  exact ⟨bubbleSort_sorted xs, bubbleSort_perm xs, bubbleSort_stable xs⟩

end Correctness

section TimeComplexity

/-- Bubble sort performs at most a full bubbling pass for each output position. -/
theorem bubbleSort_time (xs : List α) :
    let n := xs.length
    (bubbleSort xs).time ≤ n * n := by
  fun_induction bubbleSort xs with
  | case1 => simp
  | case2 x xs pass _ ih =>
    simp only [List.length_cons]
    change pass.time + (bubbleSort pass.ret.1).time ≤ (xs.length + 1) * (xs.length + 1)
    have hpass : pass.ret.1.length = xs.length := by simp [pass]
    calc
      pass.time + (bubbleSort pass.ret.1).time
          ≤ pass.time + pass.ret.1.length * pass.ret.1.length := by omega
      _ = xs.length + pass.ret.1.length * pass.ret.1.length := by simp [pass]
      _ = xs.length + xs.length * xs.length := by rw [hpass]
      _ = xs.length * (xs.length + 1) := by simp [Nat.mul_succ, Nat.add_comm]
      _ ≤ (xs.length + 1) * (xs.length + 1) :=
        Nat.mul_le_mul_right (xs.length + 1) (Nat.le_succ xs.length)

end TimeComplexity

end Cslib.Algorithms.Lean.TimeM
