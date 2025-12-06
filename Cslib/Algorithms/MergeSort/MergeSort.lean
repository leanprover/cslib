/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

import Cslib.Algorithms.QueryModel

/-!
# Merge sort in the query model

This file implements merge sort as a program in the query model defined in
`Cslib.Algorithms.QueryModel`. The algorithm uses only comparison queries.

## Main definitions

- `merge`     : merge step using `Prog` comparisons
- `split`     : split a list in two by alternating elements
- `mergeSort` : merge sort expressed in the query model

We also provide simple example evaluations of `mergeSort` and its time cost.
-/

open Cslib

namespace Cslib.Algorithms.MergeSort.QueryBased

open Cslib.Algorithms

/-- Merge two sorted lists using comparisons in the query monad. -/
def merge : List Nat → List Nat → Prog (List Nat)
  | [], ys => pure ys
  | xs, [] => pure xs
  | x :: xs', y :: ys' => do
      let b ← cmpVal x y
      if b then
        let rest ← merge xs' (y :: ys')
        pure (x :: rest)
      else
        let rest ← merge (x :: xs') ys'
        pure (y :: rest)

/-- Split a list into two lists by alternating elements. -/
def split (xs : List Nat) : List Nat × List Nat :=
  let rec go : List Nat → List Nat → List Nat → List Nat × List Nat
    | [], accL, accR => (accL.reverse, accR.reverse)
    | [x], accL, accR => ((x :: accL).reverse, accR.reverse)
    | x :: y :: xs, accL, accR => go xs (x :: accL) (y :: accR)
  go xs [] []

/-- Merge sort expressed as a program in the query model.
TODO: Working version without partial -/
partial def mergeSort : List Nat → Prog (List Nat)
  | []      => pure []
  | [x]     => pure [x]
  | xs      =>
    let (left, right) := split xs
    do
      let sortedLeft  ← mergeSort left
      let sortedRight ← mergeSort right
      merge sortedLeft sortedRight

#eval evalProg (mergeSort [5,3,8,6,2,7,4,1])
#eval timeProg (mergeSort [5,3,8,6,2,7,4,1])

end Cslib.Algorithms.MergeSort.QueryBased
