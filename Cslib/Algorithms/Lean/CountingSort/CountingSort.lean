/-
Copyright (c) 2026 Robert Joseph George. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George
-/

module

public import Cslib.Algorithms.Lean.Sorting
public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Data.Nat.Basic
public import Mathlib.Order.RelClasses
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Finiteness.Attr
public import Batteries.Data.List.Lemmas

/-!
# Counting sort on natural-number lists

`countingSort` sorts a `List ℕ` using an explicit upper bound `bound`. It scans the input once for
each key in `0, ..., bound` and returns a `TimeM ℕ (List ℕ)`.

The cost model counts one key comparison while scanning an input element. Constructing output
blocks, appending lists, arithmetic, and pattern matching are free.

The raw algorithm intentionally only emits keys in the range `0, ..., bound`; values above `bound`
are omitted. The correctness theorems therefore assume `BoundedBy bound xs`, which is the contract
that the supplied bound covers the input.

The definitions live in the `TimeM` namespace, matching the existing timed list algorithms in
`Cslib.Algorithms.Lean`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

/-- `xs` is bounded by `bound` when every entry is at most `bound`. -/
abbrev BoundedBy (bound : ℕ) (xs : List ℕ) : Prop := ∀ x ∈ xs, x ≤ bound

/-- Counts occurrences of one key, charging one tick for each inspected input element. -/
def countKey (key : ℕ) : List ℕ → TimeM ℕ ℕ
  | [] => return 0
  | x :: xs => do
    ✓ let hit := x == key
    let rest ← countKey key xs
    return rest + if hit then 1 else 0

/-- Builds the sorted blocks for keys `start, ..., start + fuel - 1`. -/
def buildCountedFrom (start fuel : ℕ) (xs : List ℕ) : TimeM ℕ (List ℕ) :=
  match fuel with
  | 0 => return []
  | fuel' + 1 => do
    let count ← countKey start xs
    let rest ← buildCountedFrom (start + 1) fuel' xs
    return List.replicate count start ++ rest

/--
Sorts natural-number lists by counting all keys from `0` through `bound`.
If the input contains values greater than `bound`, this raw version omits them; use the correctness
theorems with a `BoundedBy bound xs` hypothesis when treating the output as a sort of `xs`.
-/
def countingSort (bound : ℕ) (xs : List ℕ) : TimeM ℕ (List ℕ) :=
  buildCountedFrom 0 (bound + 1) xs

section Correctness

/-- Timed key counting computes `List.count`. -/
@[simp, grind =]
private theorem ret_countKey (key : ℕ) (xs : List ℕ) : ⟪countKey key xs⟫ = xs.count key := by
  induction xs with
  | nil => simp [countKey]
  | cons x xs ih =>
    by_cases h : x = key <;> simp [countKey, ih, h]

/-- Counting one key performs one comparison per input element. -/
@[simp, grind =]
private theorem countKey_time (key : ℕ) (xs : List ℕ) : (countKey key xs).time = xs.length := by
  induction xs with
  | nil => simp [countKey]
  | cons x xs ih => simp [countKey, ih, Nat.add_comm]

@[simp]
private theorem count_replicate_of_ne {key value count : ℕ} (h : value ≠ key) :
    (List.replicate count value).count key = 0 := by
  simp [List.count_replicate, h]

/-- The generated blocks contain no key below the requested start. -/
private theorem buildCountedFrom_start_le_of_mem {value start fuel : ℕ} {xs : List ℕ} :
    value ∈ ⟪buildCountedFrom start fuel xs⟫ → start ≤ value := by
  induction fuel generalizing start value with
  | zero => simp [buildCountedFrom]
  | succ fuel ih =>
    simp only [buildCountedFrom, ret_bind, ret_pure, ret_countKey, List.mem_append,
      List.mem_replicate]
    intro h
    rcases h with h | h
    · exact le_of_eq h.2.symm
    · exact le_trans (Nat.le_succ start) (ih h)

/--
The generated blocks contain the right number of copies for each key. This is the main counting
invariant: keys outside `start, ..., start + fuel - 1` occur zero times.
-/
@[grind =]
private theorem buildCountedFrom_count (key start fuel : ℕ) (xs : List ℕ) :
    (⟪buildCountedFrom start fuel xs⟫).count key =
      if start ≤ key ∧ key < start + fuel then xs.count key else 0 := by
  induction fuel generalizing start with
  | zero => simp [buildCountedFrom]
  | succ fuel ih =>
    by_cases hstart : start = key
    · subst key
      simp [buildCountedFrom, ih]
    · simp only [buildCountedFrom, ret_bind, ret_pure, ret_countKey, List.count_append]
      simp only [ne_eq, hstart, not_false_eq_true, count_replicate_of_ne, ih, Nat.zero_add]
      by_cases htotal : start ≤ key ∧ key < start + (fuel + 1)
      · have htail : start + 1 ≤ key ∧ key < start + 1 + fuel := by omega
        simp [htotal, htail]
      · have htail : ¬(start + 1 ≤ key ∧ key < start + 1 + fuel) := by omega
        rw [if_neg htail, if_neg htotal]

/-- In-range keys are counted exactly as in the input. -/
theorem countingSort_count_of_le_bound {bound key : ℕ} (xs : List ℕ) (hkey : key ≤ bound) :
    (⟪countingSort bound xs⟫).count key = xs.count key := by
  rw [countingSort, buildCountedFrom_count]
  split_ifs with h
  · rfl
  · omega

/-- Out-of-range keys never appear in the output. -/
theorem countingSort_count_of_bound_lt {bound key : ℕ} (xs : List ℕ) (hkey : bound < key) :
    (⟪countingSort bound xs⟫).count key = 0 := by
  rw [countingSort, buildCountedFrom_count]
  split_ifs with h
  · omega
  · rfl

/-- If the input is bounded, every out-of-range key has count zero in the input too. -/
private theorem bounded_count_eq_zero_of_bound_lt {bound key : ℕ} {xs : List ℕ}
    (hxs : BoundedBy bound xs) (hkey : bound < key) : xs.count key = 0 := by
  rw [List.count_eq_zero]
  intro hmem
  have := hxs key hmem
  omega

/-- Counting sort is a permutation because every key has the same count in input and output. -/
theorem countingSort_perm (bound : ℕ) (xs : List ℕ) (hxs : BoundedBy bound xs) :
    (⟪countingSort bound xs⟫).Perm xs := by
  rw [List.perm_iff_count]
  intro key
  by_cases hkey : key ≤ bound
  · exact countingSort_count_of_le_bound xs hkey
  · have hlt : bound < key := Nat.lt_of_not_ge hkey
    rw [countingSort_count_of_bound_lt xs hlt, bounded_count_eq_zero_of_bound_lt hxs hlt]

/-- Every generated block list is sorted because later blocks only contain larger keys. -/
private theorem buildCountedFrom_sorted (start fuel : ℕ) (xs : List ℕ) :
    List.Pairwise (· ≤ ·) ⟪buildCountedFrom start fuel xs⟫ := by
  induction fuel generalizing start with
  | zero => simp [buildCountedFrom]
  | succ fuel ih =>
    simp only [buildCountedFrom, ret_bind, ret_pure, ret_countKey]
    rw [List.pairwise_append]
    refine ⟨by simp [List.pairwise_replicate], ih (start + 1), ?_⟩
    intro a ha b hb
    have haEq : a = start := (List.mem_replicate.mp ha).2
    have hbLower : start + 1 ≤ b := buildCountedFrom_start_le_of_mem hb
    omega

/-- Counting sort returns a sorted list. -/
theorem countingSort_sorted (bound : ℕ) (xs : List ℕ) :
    List.Pairwise (· ≤ ·) ⟪countingSort bound xs⟫ := by
  exact buildCountedFrom_sorted 0 (bound + 1) xs

/-- Filtering a list by one value gives exactly `count` copies of that value. -/
private theorem filter_eq_replicate_count (key : ℕ) (xs : List ℕ) :
    xs.filter (fun x => decide (x = key)) = List.replicate (xs.count key) key := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    by_cases h : x = key
    · simp [h, ih, List.replicate_succ]
    · simp [h, ih]

/--
Counting sort is stable for natural numbers because every equal-value subsequence is just a block of
identical copies, and the count theorem proves that block has the same length as in the input.
-/
theorem countingSort_stable (bound : ℕ) (xs : List ℕ) (hxs : BoundedBy bound xs) :
    StableByValue xs ⟪countingSort bound xs⟫ := by
  intro key
  rw [filter_eq_replicate_count key ⟪countingSort bound xs⟫, filter_eq_replicate_count key xs]
  by_cases hkey : key ≤ bound
  · rw [countingSort_count_of_le_bound xs hkey]
  · have hlt : bound < key := Nat.lt_of_not_ge hkey
    rw [countingSort_count_of_bound_lt xs hlt, bounded_count_eq_zero_of_bound_lt hxs hlt]

/-- Counting sort is functionally correct for inputs covered by the supplied bound. -/
theorem countingSort_correct (bound : ℕ) (xs : List ℕ) (hxs : BoundedBy bound xs) :
    List.Pairwise (· ≤ ·) ⟪countingSort bound xs⟫ ∧ (⟪countingSort bound xs⟫).Perm xs ∧
      StableByValue xs ⟪countingSort bound xs⟫ := by
  exact ⟨countingSort_sorted bound xs, countingSort_perm bound xs hxs,
    countingSort_stable bound xs hxs⟩

end Correctness

section TimeComplexity

/-- Building counted blocks scans the input once for each generated key. -/
@[simp]
private theorem buildCountedFrom_time (start fuel : ℕ) (xs : List ℕ) :
    (buildCountedFrom start fuel xs).time = fuel * xs.length := by
  induction fuel generalizing start with
  | zero => simp [buildCountedFrom]
  | succ fuel ih => simp [buildCountedFrom, ih, Nat.succ_mul, Nat.add_comm]

/-- Time complexity of counting sort under the stated cost model. -/
theorem countingSort_time (bound : ℕ) (xs : List ℕ) :
    (countingSort bound xs).time = (bound + 1) * xs.length := by
  simp [countingSort]

/-- A convenient upper bound form of `countingSort_time`. -/
theorem countingSort_time_le (bound : ℕ) (xs : List ℕ) :
    let n := xs.length
    (countingSort bound xs).time ≤ (bound + 1) * n := by
  simp [countingSort_time]

end TimeComplexity

end Cslib.Algorithms.Lean.TimeM
