/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Cslib.Algorithms.Lean.Query.Sort.Insertion.Lemmas
public import Cslib.Algorithms.Lean.Query.Sort.Merge.Lemmas

/-! # Monadic Comparison Sort Specification

`IsMonadicSort sort` asserts that a monad-generic function `sort` is a correct comparison sort:
for any non-failing comparator it produces a permutation, and for any comparator reflecting a
total order it produces a sorted list.

Because the function is polymorphic in the monad `m`, a computable `def` cannot observe any
instrumentation layered into `m` (see `UpperBound` for details). This allows us to combine
`IsMonadicSort` with `UpperBound` to state complexity claims about comparison sorts.

## Polynomial-time sorting example

`PolyNatSort k` packages an algorithm with proofs that it is a correct comparison sort using
at most `n ^ k` comparisons. We exhibit `insertionSort` as a `PolyNatSort 2`,
and assert that the framework is non-trivial in the sense that no adversary
can computably inhabit `PolyNatSort 1`.
-/

open Std.Do Cslib.Query

public section

namespace Cslib.Query

-- ## IsMonadicSort: correctness specification for comparison sorts

/-- A monad-generic function is a monadic comparison sort if it always produces a permutation
    of its input (for any non-failing comparator), and always produces a sorted list (for any
    comparator reflecting a total order `r`).

    The universal quantification over `r` in the `sorted` field is essential: it prevents the
    algorithm from using any built-in ordering on the element type (e.g., `Nat.ble`), forcing
    it to learn the ordering exclusively through comparator queries. -/
structure IsMonadicSort
    (sort : ∀ {m : Type → Type} [Monad m], (α × α → m Bool) → List α → m (List α)) : Prop where
  /-- The sort produces a permutation of its input, for any non-failing monadic comparator. -/
  perm : ∀ {m : Type → Type} {ps : PostShape} [Monad m] [WPMonad m ps]
    (cmp : α × α → m Bool) (_ : ∀ p, ⦃⌜True⌝⦄ cmp p ⦃⇓_ => ⌜True⌝⦄)
    (xs : List α),
    ⦃⌜True⌝⦄ sort cmp xs ⦃⇓result => ⌜result.Perm xs⌝⦄
  /-- The sort produces a sorted list, for any comparator with a pure return reflecting a
      total order `r`. -/
  sorted : ∀ (r : α → α → Prop) [DecidableRel r] [Std.Total r] [IsTrans α r]
    {m : Type → Type} {ps : PostShape} [Monad m] [WPMonad m ps]
    (cmp : α × α → m Bool) (_ : PureReturn cmp (fun p => decide (r p.1 p.2)))
    (xs : List α),
    ⦃⌜True⌝⦄ sort cmp xs ⦃⇓result => ⌜result.Pairwise r⌝⦄

/-- `insertionSort` is a monadic comparison sort. -/
public theorem insertionSort_isMonadicSort : IsMonadicSort (insertionSort (α := α)) where
  perm := insertionSort_perm
  sorted r := insertionSort_sorted r

-- ## Example: polynomial-time comparison sorting predicates

/-- A computable inhabitant of this type would demonstrate that lists of natural numbers
    can be sorted using at most `n^k` comparison queries.

    The `IsMonadicSort` component ensures the algorithm is a genuine comparison sort:
    it must produce a sorted permutation for *every* total order on `Nat` (not just `≤`),
    so it cannot bypass the comparator by using `Nat`'s built-in ordering.

    The `UpperBound` component, combined with monad parametricity and computability,
    ensures the algorithm makes at most `xs.length ^ k` comparator queries. -/
structure PolyNatSort (k : Nat) where
  /-- The sorting algorithm, generic over the monad. -/
  sort : ∀ {m : Type → Type} [Monad m], (Nat × Nat → m Bool) → List Nat → m (List Nat)
  /-- The algorithm is a correct comparison sort. -/
  isSort : IsMonadicSort sort
  /-- The algorithm uses at most `xs.length ^ k` comparisons. -/
  runsIn : UpperBound sort (fun xs => xs.length ^ k)

/-- `insertionSort` is a correct quadratic comparison sort. -/
public def insertionSort_quadraticNatSort : PolyNatSort 2 where
  sort := insertionSort
  isSort := insertionSort_isMonadicSort
  runsIn := insertionSort_runsIn

/-!
This is a non-trivial claim: `PolyNatSort 1` can not be computably inhabited!
Any approach to query complexity upper bounds should allow us
1. to write true upper bound statements, and inhabit them, and
2. to write false upper bound statements,
   without an adversary being able to (computably) inhabit them.
-/

end Cslib.Query

end -- public section
