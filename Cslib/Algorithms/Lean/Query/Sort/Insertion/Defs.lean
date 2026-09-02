/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Shreyas Srinivas, Eric Wieser
-/
module

public import Cslib.Algorithms.Lean.Query.Sort.LEQuery

/-! # Insertion Sort as a Query Program

Insertion sort implemented as a `FreeM (LEQuery α)`, making all comparison queries explicit.
-/

open Cslib Cslib.Query

public section

namespace List

variable {m} [Monad m] (cmp : α → α → m Bool)

/-- Insert `x` into a sorted list using monadic comparisons. -/
@[expose] def orderedInsertM (x : α) : List α → m (List α)
  | [] => return [x]
  | y :: ys => do
    let le ← cmp x y
    if le then
      return (x :: y :: ys)
    else do
      let rest ← orderedInsertM x ys
      return (y :: rest)

/-- Sort a list using insertion sort with monadic comparisons. -/
@[expose] def insertionSortM : List α → m (List α)
  | [] => return []
  | x :: xs => do
    let sorted ← insertionSortM xs
    orderedInsertM cmp x sorted

end List

namespace Cslib.Query

/-- Insert `x` into a sorted list using comparison queries. -/
abbrev orderedInsert (x : α) (xs : List α) : FreeM (LEQuery α) (List α) :=
  xs.orderedInsertM LEQuery.ask x

/-- Sort a list using insertion sort with comparison queries. -/
abbrev insertionSort (xs : List α) : FreeM (LEQuery α) (List α) :=
  xs.insertionSortM LEQuery.ask

end Cslib.Query
