/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Eric Wieser, Shreyas Srinivas
-/
module

public import Cslib.Algorithms.Lean.Query.QueryTree

/-! # LowerBound: Query Complexity Lower Bounds via Decision Trees

`Query.LowerBound f size bound` asserts a worst-case lower bound on the number of queries
made by a monad-generic algorithm `f`.

## The decision tree argument

To prove lower bounds, we specialize the algorithm to the `QueryTree` monad (the free monad
over queries), which reifies the algorithm's query pattern as an explicit decision tree.
Each internal node corresponds to a query, and each leaf to a final result.

The predicate `LowerBound f size bound` states: for every input size `n`, there exists
an input `x` with `size x ≤ n` and an oracle such that the algorithm makes at least
`bound n` queries. This is the worst-case formulation — for each size we exhibit a hard
input, and choose the oracle after seeing the algorithm's strategy (the tree).
-/

open Cslib.Query

public section

namespace Cslib.Query

/-- `LowerBound f size bound` asserts that for every input size `n`, there exists
    an input `x` with `size x ≤ n` and an oracle making `f` perform at least `bound n` queries.

    The algorithm `f` is specialized to `QueryTree`, reifying its query pattern
    as a decision tree. The oracle determines which path through the tree is taken.
    Unlike `UpperBound` (upper bounds), no parametricity assumption is needed: the tree
    structure itself forces enough branching for correctness. -/
@[expose] def LowerBound
    (f : ∀ {m : Type → Type} [Monad m], (α → m β) → γ → m δ)
    (size : γ → Nat) (bound : Nat → Nat) : Prop :=
  ∀ n, ∃ x, size x ≤ n ∧ ∃ (oracle : α → β),
    (f QueryTree.ask x : QueryTree α β δ).queriesOn oracle ≥ bound n

end Cslib.Query

end -- public section
