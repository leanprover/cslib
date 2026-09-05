/-
Copyright (c) 2026 Robert Joseph George. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George
-/

module

public import Cslib.Init

/-!
# Sorting utilities

For stable list sorts, filtering the input and output by any value gives a compact way to state that
the output keeps the same per-value subsequence as the input. For plain values this is equivalent to
preserving the number of copies of each value; for richer element types it can express a stronger
order-preservation property.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

/-- `ys` preserves the order of equal values from `xs`. -/
abbrev StableByValue {α : Type*} [DecidableEq α] (xs ys : List α) : Prop :=
  ∀ value, ys.filter (fun x => decide (x = value)) = xs.filter (fun x => decide (x = value))

end Cslib.Algorithms.Lean
