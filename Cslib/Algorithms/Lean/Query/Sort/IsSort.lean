/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Shreyas Srinivas
-/
module

public import Cslib.Algorithms.Lean.Query.Sort.LEQuery
import Mathlib.Data.List.Sort

/-! # IsSort: Specification for Comparison Sorts

`IsSort sort` asserts that `sort` is a correct comparison sort when viewed as a `FreeM`
over `LEQuery α`. Correctness means: for any oracle, the result is a permutation of the
input; and for any oracle implementing a total order, the result is sorted.
-/

open Cslib Cslib.Query

public section

namespace Cslib.Query

/-- A `FreeM`-based function is a correct comparison sort if it always produces a permutation
    of its input, and produces a sorted list when the oracle implements a total order. -/
structure IsSort (sort : List α → FreeM (LEQuery α) (List α)) : Prop where
  /-- The sort produces a permutation of its input, for any oracle. -/
  perm : ∀ (xs : List α) (oracle : {ι : Type} → LEQuery α ι → ι),
    ((sort xs).eval oracle).Perm xs
  /-- The sort produces a sorted list, when the oracle implements a total order. -/
  sorted : ∀ (xs : List α) (oracle : {ι : Type} → LEQuery α ι → ι)
    (r : α → α → Prop) [DecidableRel r] [Std.Total r] [IsTrans α r]
    (_ : ∀ a b, oracle (.le a b) = decide (r a b)),
    ((sort xs).eval oracle).Pairwise r

/-- `IsSort` determines the output: under an oracle implementing an antisymmetric total
    transitive relation, all correct comparison sorts produce the same list. -/
theorem IsSort.eval_eq {sort₁ sort₂ : List α → FreeM (LEQuery α) (List α)}
    (h₁ : IsSort sort₁) (h₂ : IsSort sort₂)
    (r : α → α → Prop) [DecidableRel r] [Std.Total r] [IsTrans α r] [Std.Antisymm r]
    (oracle : {ι : Type} → LEQuery α ι → ι)
    (horacle : ∀ a b, oracle (.le a b) = decide (r a b)) (xs : List α) :
    (sort₁ xs).eval oracle = (sort₂ xs).eval oracle :=
  ((h₁.perm xs oracle).trans (h₂.perm xs oracle).symm).eq_of_pairwise'
    (h₁.sorted xs oracle r horacle) (h₂.sorted xs oracle r horacle)

end Cslib.Query
