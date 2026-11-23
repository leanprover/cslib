/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Cslib.Algorithms.Lean.Query.Sort.Merge.Bounds
import Cslib.Algorithms.Lean.Query.Sort.Insertion.Lemmas
import Cslib.Algorithms.Lean.Query.Arith.Lemmas
import Cslib.Algorithms.Lean.Query.Maximum
import Cslib.Algorithms.Lean.Query.MinMax

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

-- The linear scan finds the maximum with `n - 1` queries.
#guard (maximum [3, 1, 4, 1, 5, 9, 2, 6]).eval leOracle == some 9
#guard (maximum [3, 1, 4, 1, 5, 9, 2, 6]).countQueries leOracle == 7
#guard (maximum ([] : List ℕ)).eval leOracle == none
#guard (maximum [3, 1, 2]).countQueries (LEQuery.oracleOf fun _ _ => false) == 2

-- The comparisons asked along a run, and who lost each of them.
#guard comparisons leOracle (maximum [3, 1, 4]) == [(3, 1), (3, 4)]
#guard (comparisons leOracle (maximum [3, 1, 4])).map (loser leOracle) == [1, 3]

-- The linear scan is optimal among correct maximum finders on lists of distinct elements.
example (find : List ℕ → FreeM (LEQuery ℕ) (Option ℕ)) (hfind : IsMaxFinder find)
    (xs : List ℕ) (hxs : xs.Nodup) :
    (maximum xs).countQueries leOracle ≤ (find xs).countQueries leOracle :=
  maximum_optimal hfind xs hxs leOracle (· ≤ ·) fun _ _ => rfl

-- The lower and upper bounds for finding the maximum match.
example (n : ℕ) : n - 1 ≤ n - 1 :=
  (maximum_isMaxFinder (α := ℕ)).lowerBound.le_upperBound maximum_upperBound n

-- The pairwise scan finds both the minimum and the maximum with `⌈3n/2⌉ - 2` queries.
#guard (minMax [3, 1, 4, 1, 5, 9, 2, 6]).eval leOracle == some (1, 9)
#guard (minMax [3, 1, 4, 1, 5, 9, 2, 6]).countQueries leOracle == 10
#guard (minMax [5, 3, 8, 1, 9, 2, 7]).eval leOracle == some (1, 9)
#guard (minMax [5, 3, 8, 1, 9, 2, 7]).countQueries leOracle == 9
#guard (minMax [42]).eval leOracle == some (42, 42)
#guard (minMax ([] : List ℕ)).eval leOracle == none

-- The scan is optimal among correct min-max finders on lists of distinct elements.
example (find : List ℕ → FreeM (LEQuery ℕ) (Option (ℕ × ℕ))) (hfind : IsMinMaxFinder find)
    (xs : List ℕ) (hxs : xs.Nodup) :
    ∃ v : ℕ → ℤ, (minMax xs).countQueries leOracle ≤ (find xs).countQueries (valOracle v) :=
  (minMax_optimal hfind xs hxs).imp fun _ h => h leOracle

-- The lower and upper bounds for finding the minimum and the maximum match.
example (n : ℕ) : (3 * n + 1) / 2 - 2 ≤ (3 * n + 1) / 2 - 2 :=
  (minMax_isMinMaxFinder (α := ℕ)).lowerBound.le_upperBound minMax_upperBound n
