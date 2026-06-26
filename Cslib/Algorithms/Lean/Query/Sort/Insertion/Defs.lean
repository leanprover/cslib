/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Shreyas Srinivas
-/
module

public import Cslib.Algorithms.Lean.Query.Sort.LEQuery

/-! # Insertion Sort as a Query Program

Insertion sort implemented as a `FreeM (LEQuery α)`, making all comparison queries explicit.
-/

open Cslib Cslib.Query

public section

namespace Cslib.Query

/-- Insert `x` into a sorted list using comparison queries. -/
@[expose] def orderedInsert (x : α) : List α → FreeM (LEQuery α) (List α)
  | [] => pure [x]
  | y :: ys => do
    let le ← LEQuery.ask x y
    if le then
      pure (x :: y :: ys)
    else do
      let rest ← orderedInsert x ys
      pure (y :: rest)

/-- Sort a list using insertion sort with comparison queries. -/
@[expose] def insertionSort : List α → FreeM (LEQuery α) (List α)
  | [] => pure []
  | x :: xs => do
    let sorted ← insertionSort xs
    orderedInsert x sorted

end Cslib.Query

end -- public section
