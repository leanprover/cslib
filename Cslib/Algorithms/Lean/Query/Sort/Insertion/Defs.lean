/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Cslib.Algorithms.Lean.Query.Basic

namespace Cslib.Query

/-- Insert `x` into a sorted list, using the monadic comparator `cmp`. -/
@[expose] public def orderedInsert [Monad m] (cmp : α × α → m Bool) (x : α) :
    List α → m (List α)
  | [] => pure [x]
  | y :: ys => do
    let lt ← cmp (x, y)
    if lt then
      pure (x :: y :: ys)
    else
      let rest ← orderedInsert cmp x ys
      pure (y :: rest)

/-- Sort a list using insertion sort with the monadic comparator `cmp`. -/
@[expose] public def insertionSort [Monad m] (cmp : α × α → m Bool) :
    List α → m (List α)
  | [] => pure []
  | x :: xs => do
    let sorted ← insertionSort cmp xs
    orderedInsert cmp x sorted

end Cslib.Query
