/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Cslib.Algorithms.Lean.Query.Sort.LEQuery

/-! # IsSort: Specification for Comparison Sorts

`IsSort sort` asserts that `sort` is a correct comparison sort when viewed as a `Prog`
over `LEQuery α`. Correctness means: for any oracle, the result is a permutation of the
input; and for any oracle implementing a total order, the result is sorted.
-/

open Cslib.Query

public section

namespace Cslib.Query

/-- A `Prog`-based function is a correct comparison sort if it always produces a permutation
    of its input, and produces a sorted list when the oracle implements a total order. -/
structure IsSort (sort : List α → Prog (LEQuery α) (List α)) : Prop where
  /-- The sort produces a permutation of its input, for any oracle. -/
  perm : ∀ (xs : List α) (oracle : {ι : Type} → LEQuery α ι → ι),
    ((sort xs).eval oracle).Perm xs
  /-- The sort produces a sorted list, when the oracle implements a total order. -/
  sorted : ∀ (xs : List α) (oracle : {ι : Type} → LEQuery α ι → ι)
    (r : α → α → Prop) [DecidableRel r] [Std.Total r] [IsTrans α r]
    (_ : ∀ a b, oracle (.le a b) = decide (r a b)),
    ((sort xs).eval oracle).Pairwise r

end Cslib.Query

end -- public section
