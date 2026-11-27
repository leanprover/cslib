/-
Copyright (c) 2026 Robert Joseph George. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George
-/
module

public import Cslib.Algorithms.Lean.Query.Sort.LEQuery
public import Cslib.Algorithms.Lean.Sort.Bubble

/-! # Bubble Sort as a Query Program

Bubble sort implemented as a `FreeM (LEQuery α)`, making all comparison queries explicit.

## Main definitions

* `Cslib.Query.bubblePass`: one pass of bubble sort with comparison queries.
* `Cslib.Query.bubbleSort`: bubble sort with comparison queries.
-/

open Cslib Cslib.Query

public section

namespace Cslib.Query

/-- One bubble sort pass over `x :: xs` using comparison queries. -/
abbrev bubblePass (x : α) (xs : List α) : FreeM (LEQuery α) (List α × α) :=
  xs.bubblePassM LEQuery.ask x

/-- Sort a list using bubble sort with comparison queries. -/
abbrev bubbleSort (xs : List α) : FreeM (LEQuery α) (List α) :=
  xs.bubbleSortM LEQuery.ask

end Cslib.Query
