/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Cslib.Algorithms.Lean.Query.Sort.Merge.Bounds
import Cslib.Algorithms.Lean.Query.Sort.Insertion.Lemmas
import Cslib.Algorithms.Lean.Query.Arith.Lemmas

/-! # Tests for the query complexity framework

Executable checks that the query programs compute, plus compile-time checks exercising
the public API (bound combinators, sort uniqueness, universe polymorphism).
-/

set_option linter.hashCommand false

open Cslib Cslib.Query

/-- The honest comparison oracle on `ℕ`. -/
def leOracle : {ι : Type} → LEQuery ℕ ι → ι :=
  LEQuery.oracleOf fun a b => decide (a ≤ b)

-- The query sorts compute, and agree with the reference sorts.
#guard (mergeSort [3, 1, 2]).eval leOracle == [1, 2, 3]
#guard (insertionSort [3, 1, 2]).eval leOracle == [1, 2, 3]

-- Query counts along the honest path.
#guard (mergeSort [3, 1, 2]).countQueries leOracle == 3
#guard (insertionSort [3, 1, 2]).countQueries leOracle == 3

-- The sharp insertion bound `n * (n - 1) / 2` is attained by the all-`false` oracle.
#guard (insertionSort [1, 2, 3]).countQueries (LEQuery.oracleOf fun _ _ => false) == 3

-- `mergeSort` is stable: with equal keys, payloads keep their input order.
#guard (mergeSort [(1, "b"), (0, "x"), (1, "a")]).eval
    (LEQuery.oracleOf fun p q => decide (p.1 ≤ q.1)) == [(0, "x"), (1, "b"), (1, "a")]

-- The complex multiplication examples compute.
#guard (complexMulNaive (1 : Int) 2 3 4).eval ArithQuery.honest == (-5, 10)
#guard (complexMulGauss (1 : Int) 2 3 4).eval ArithQuery.honest == (-5, 10)

-- All correct comparison sorts agree under a linear-order oracle (`IsSort.eval_eq`).
example (xs : List ℕ) :
    (mergeSort xs).eval leOracle = (insertionSort xs).eval leOracle :=
  mergeSort_isSort.eval_eq insertionSort_isSort (· ≤ ·) leOracle (fun _ _ => rfl) xs

-- The sharp triangular bound for insertion sort.
example (oracle : {ι : Type} → LEQuery ℕ ι → ι) (xs : List ℕ) :
    (insertionSort xs).countQueries oracle ≤ xs.length * (xs.length - 1) / 2 :=
  insertionSort_countQueries_le oracle xs

-- Upper and lower bounds compose via `LowerBound.le_upperBound`.
example (n : ℕ) : Nat.clog 2 (Nat.factorial n) ≤ n * Nat.clog 2 n :=
  (mergeSort_lowerBound (α := ℕ)).le_upperBound mergeSort_upperBound n

-- `UpperBound` is universe polymorphic in the query family.
example (Q : Type 1 → Type 2) (prog : Bool → FreeM Q PUnit.{2}) : Prop :=
  UpperBound prog (fun _ => 0) id
