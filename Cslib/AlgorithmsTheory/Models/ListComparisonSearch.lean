/-
Copyright (c) 2025 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Cslib.AlgorithmsTheory.QueryModel

@[expose] public section

/-!
# Query Type for Comparison Search in Lists

In this file we define a query type `ListSearch` for comparison based searching in Lists,
whose sole query `compare` compares the head of the list with a given argument. It
further defines a model `ListSearch.natCost` for this query.

--
## Definitions

- `ListSearch`: A query type for comparison based search in lists.
- `ListSearch.natCost`:  A model for this query with costs in `ℕ`.

-/

namespace Cslib

namespace Algorithms

open Prog

/--
A query type for searching elements in list. It supports exactly one query
`compare l val` which returns `true` if the head of the list `l` is equal to `val`
and returns `false` otherwise.
-/
inductive ListSearch (α : Type*) : Type → Type _ where
  | compare (a : List α) (val : α) : ListSearch α Bool


/-- A model of the `ListSearch` query type that assigns the cost as the number of queries. -/
@[simps]
def ListSearch.natCost [BEq α] : Model (ListSearch α) ℕ where
  evalQuery
    | .compare l x => some x == l.head?
  cost _ := 1

end Algorithms

end Cslib
