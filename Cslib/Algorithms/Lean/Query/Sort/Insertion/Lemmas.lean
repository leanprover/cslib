/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Shreyas Srinivas
-/
module

public import Cslib.Algorithms.Lean.Query.Bounds
public import Cslib.Algorithms.Lean.Query.Sort.IsSort
public import Cslib.Algorithms.Lean.Query.Sort.Insertion.Defs
public import Mathlib.Data.List.Sort
import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Group.Defs

/-! # Insertion Sort: Correctness and Upper Bound

Proofs that `insertionSort` is a correct comparison sort and uses at most `n²` queries.
All proofs are by plain equational reasoning on `FreeM.eval` and `FreeM.countQueries`.
-/

open Cslib Cslib.Query

public section

namespace Cslib.Query

variable {α : Type}

/-! ## Evaluation -/

/-- Evaluating query-based insertion agrees with `List.orderedInsert` using the relation
supplied by the oracle. -/
@[simp] theorem eval_orderedInsert (oracle : {ι : Type} → LEQuery α ι → ι)
    (x : α) (xs : List α) :
    (orderedInsert x xs).eval oracle =
      xs.orderedInsert (fun x y => oracle (.le x y)) x := by
  induction xs with
  | nil => simp [orderedInsert]
  | cons y ys ih =>
    simp [orderedInsert]
    split <;> simp_all

/-- Evaluating query-based insertion sort agrees with `List.insertionSort` using the relation
supplied by the oracle.

This is the essential correctness statement: it identifies the query program as *the*
insertion sort operation, so correctness properties (permutation, sortedness) transfer
directly from the `List.insertionSort` API rather than being restated here. -/
@[simp] theorem eval_insertionSort (oracle : {ι : Type} → LEQuery α ι → ι) (xs : List α) :
    (insertionSort xs).eval oracle =
      xs.insertionSort (fun x y => oracle (.le x y)) := by
  induction xs with
  | nil => simp [insertionSort]
  | cons x xs ih => simp [insertionSort, ih]

/-! ## Query count proofs -/

theorem orderedInsert_countQueries_le (oracle : {ι : Type} → LEQuery α ι → ι)
    (x : α) (xs : List α) :
    (orderedInsert x xs).countQueries oracle ≤ xs.length := by
  induction xs with
  | nil => simp [orderedInsert]
  | cons y ys ih =>
    unfold orderedInsert
    simp
    by_cases h : oracle (.le x y) = true
    · simp [h]
    · simp [h]
      omega

theorem insertionSort_countQueries_le (oracle : {ι : Type} → LEQuery α ι → ι)
    (xs : List α) :
    (insertionSort xs).countQueries oracle ≤ xs.length ^ 2 := by
  induction xs with
  | nil => simp [insertionSort]
  | cons x xs ih =>
    have hq : (insertionSort (x :: xs)).countQueries oracle =
        (insertionSort xs).countQueries oracle +
        (orderedInsert x ((insertionSort xs).eval oracle)).countQueries oracle := by
      simp [insertionSort]
    rw [hq]
    have hlen : ((insertionSort xs).eval oracle).length = xs.length := by
      rw [eval_insertionSort]
      exact (List.perm_insertionSort _ xs).length_eq
    have hord := orderedInsert_countQueries_le oracle x ((insertionSort xs).eval oracle)
    rw [hlen] at hord
    have h1 := Nat.add_le_add ih hord
    have hpow : xs.length ^ 2 + xs.length ≤ (xs.length + 1) ^ 2 := by
      have : (xs.length + 1) ^ 2 = xs.length ^ 2 + 2 * xs.length + 1 := by ring
      omega
    simp only [List.length_cons]
    exact Nat.le_trans h1 hpow

/-! ## UpperBound and IsSort instances -/

theorem insertionSort_upperBound :
    UpperBound (insertionSort (α := α)) List.length (· ^ 2) := by
  intro oracle n x hle
  exact Nat.le_trans (insertionSort_countQueries_le oracle x)
    (Nat.pow_le_pow_left hle 2)

theorem insertionSort_isSort : IsSort (insertionSort (α := α)) where
  perm xs oracle := by
    rw [eval_insertionSort]
    exact List.perm_insertionSort _ xs
  sorted := by
    intro xs oracle r _ _ _ horacle
    rw [eval_insertionSort]
    simpa only [horacle, decide_eq_true_eq] using List.pairwise_insertionSort r xs

end Cslib.Query
