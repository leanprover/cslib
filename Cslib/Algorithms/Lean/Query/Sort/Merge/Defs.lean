/-
Copyright (c) 2025 Sorrachai Yingchareonthawornhcai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornhcai, Kim Morrison
-/
module

public import Cslib.Algorithms.Lean.Query.Basic

namespace Cslib.Query

/-- Monad-generic merge: merges two lists using a monadic comparator `cmp`.
    At `m := Id`, this agrees with `List.merge` (see `id_run_merge`). -/
@[expose] public def merge [Monad m] (cmp : α × α → m Bool) :
    List α → List α → m (List α)
  | [], ys => pure ys
  | xs, [] => pure xs
  | x :: xs, y :: ys => do
    let le ← cmp (x, y)
    if le then
      let rest ← merge cmp xs (y :: ys)
      pure (x :: rest)
    else
      let rest ← merge cmp (x :: xs) ys
      pure (y :: rest)

open List.MergeSort.Internal in
/-- Monad-generic merge sort: sorts a list using a monadic comparator `cmp`.
    At `m := Id`, this agrees with `List.mergeSort` (see `id_run_mergeSort`). -/
@[expose] public def mergeSort [Monad m] (cmp : α × α → m Bool) :
    List α → m (List α)
  | [] => pure []
  | [a] => pure [a]
  | a :: b :: xs =>
    let lr := splitInTwo ⟨a :: b :: xs, rfl⟩
    have : lr.1.1.length < (a :: b :: xs).length := by simp [lr.1.2]; omega
    have : lr.2.1.length < (a :: b :: xs).length := by simp [lr.2.2]; omega
    do
      let left ← mergeSort cmp lr.1.1
      let right ← mergeSort cmp lr.2.1
      merge cmp left right
termination_by xs => xs.length

end Cslib.Query
