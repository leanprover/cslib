/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Cslib.Algorithms.Lean.Query.Basic

/-! # UpperBound: Query Complexity Bounds via Monad Parametricity

`UpperBound f bound` (and its generalization `UpperBoundT`) assert that a monad-generic algorithm `f`
makes at most `bound x` queries on input `x`.

## The parametricity argument

An algorithm like
```
def insertionSort [Monad m] (cmp : α × α → m Bool) : List α → m (List α) := ...
```
is written generically over the monad `m`. To measure its query complexity, we specialize
`m` to `TimeM` (or `TimeT n` for algorithms with additional effects) and provide a
`cmp` implementation that calls `tick` once per invocation.

Because `insertionSort` is parametric in `m`, it **cannot observe the tick instrumentation**.
It must call `cmp` the same number of times regardless of which monad it runs in.
Therefore any upper bound proved via `TimeM` is a true bound on query count in all monads.

`UpperBoundT` handles algorithms that use a base monad `n` for their own effects
(e.g., `StateM` for accumulation). The function must be generic over monads extending `n`
via `MonadLiftT`, and we specialize to `TimeT n` which layers tick-counting on top of `n`.
The same parametricity argument applies: the algorithm cannot distinguish `TimeT n` from
any other monad that lifts `n`.

## Computability caveat

The parametricity argument is only valid for **computable** algorithms. A `noncomputable`
definition could use `Classical.choice` to inspect `m` or the query function and subvert
the instrumentation. Since Lean's type theory does not enforce parametricity, the soundness
guarantee is informal: `UpperBound` and `UpperBoundT` theorems should only be proved about computable
algorithms. This framework is designed for proving upper bounds on query complexity, not lower
bounds.
-/

open Std.Do Cslib.Query

public section

namespace Cslib.Query

/-- `UpperBoundT n f bound` asserts that when the monad-generic function `f`
    is specialized to `TimeT n`, with any query that calls `tick` at most once per invocation,
    the total number of ticks is bounded by `bound x`.

    The function `f` is generic over monads that extend `n` via `MonadLift`,
    ensuring it cannot observe the tick instrumentation. -/
@[expose] def UpperBoundT {n : Type → Type} {ps : PostShape} [Monad n] [WP n ps]
    (f : ∀ {m : Type → Type} [Monad m] [MonadLiftT n m], (α → m β) → γ → m δ)
    (bound : γ → Nat) : Prop :=
  ∀ (query : α → TimeT n β), (∀ a, TimeT.Costs (query a) 1) →
    ∀ x, TimeT.Costs (f query x) (bound x)

/-- `UpperBound f bound` asserts that when the monad-generic function `f` is specialized to `TimeM`,
    with any query that calls `tick` at most once per invocation,
    the total number of ticks is bounded by `bound x`. -/
@[expose] def UpperBound
    (f : ∀ {m : Type → Type} [Monad m], (α → m β) → γ → m δ)
    (bound : γ → Nat) : Prop :=
  ∀ (query : α → TimeM β), (∀ a, TimeT.Costs (query a) 1) →
    ∀ x, TimeT.Costs (f query x) (bound x)

end Cslib.Query

end -- public section
