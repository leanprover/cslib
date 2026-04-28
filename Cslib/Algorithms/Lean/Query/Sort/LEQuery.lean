/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf, Kim Morrison, Shreyas Srinivas
-/
module

public import Cslib.Algorithms.Lean.Query.FreeM

/-! # LEQuery: Comparison Queries for Sorting

`LEQuery α` is the query type for comparison-based sorting algorithms.
A query `LEQuery.le a b` asks whether `a ≤ b` and returns a `Bool`.
-/

public section

namespace Cslib.Query

/-- Comparison query: asks whether `a ≤ b`, returning a `Bool`. -/
inductive LEQuery (α : Type) : Type → Type where
  | le (a b : α) : LEQuery α Bool

/-- Lift `LEQuery.le a b` into a `FreeM` that returns the comparison result. -/
@[expose] def LEQuery.ask (a b : α) : FreeM (LEQuery α) Bool :=
  FreeM.lift (.le a b)

@[simp] theorem LEQuery.eval_ask (oracle : {ι : Type} → LEQuery α ι → ι) (a b : α) :
    (LEQuery.ask a b).eval oracle = oracle (.le a b) := rfl

end Cslib.Query

end -- public section
