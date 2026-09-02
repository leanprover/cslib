/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Shreyas Srinivas, Sorrachai Yingchareonthawornchai
-/
module

public import Cslib.Algorithms.Lean.Query.Sort.LEQuery

/-! # Merge Sort as a Query Program

Merge sort implemented as a `FreeM (LEQuery α)`, making all comparison queries explicit.
The definitions mirror `List.merge` and `List.mergeSort` exactly: the list is split into
contiguous halves and the merge prefers the left element on ties. Consequently evaluating
the query program against any oracle produces literally the same list as `List.mergeSort`
with the comparator induced by the oracle (`eval_mergeSort` in
`Cslib.Algorithms.Lean.Query.Sort.Merge.Lemmas`); in particular the sort is stable.
The recursive calls of `mergeSort` are not structural, since the two halves are not
syntactic subterms, and are justified separately using their lengths.
-/

open Cslib Cslib.Query

public section

namespace Cslib.Query

/-- Split a list into contiguous halves; if the length is odd, the first half is one element
longer. This agrees with `List.MergeSort.Internal.splitInTwo`, so that `mergeSort` agrees
with `List.mergeSort`. -/
@[expose] def split (xs : List α) : List α × List α :=
  (xs.take ((xs.length + 1) / 2), xs.drop ((xs.length + 1) / 2))

@[simp] theorem split_fst_length_eq (xs : List α) :
    (split xs).1.length = (xs.length + 1) / 2 := by
  simp [split]
  omega

@[simp] theorem split_snd_length_eq (xs : List α) :
    (split xs).2.length = xs.length / 2 := by
  simp [split]
  omega

theorem split_fst_append_split_snd (xs : List α) : (split xs).1 ++ (split xs).2 = xs :=
  List.take_append_drop _ xs

/-- Merge two sorted lists using comparison queries. -/
@[expose] def merge (xs ys : List α) : FreeM (LEQuery α) (List α) :=
  match xs, ys with
  | [], ys => return ys
  | xs, [] => return xs
  | x :: xs', y :: ys' => do
    let le ← LEQuery.ask x y
    if le then do
      let rest ← merge xs' (y :: ys')
      return (x :: rest)
    else do
      let rest ← merge (x :: xs') ys'
      return (y :: rest)
termination_by xs.length + ys.length

/-- Sort a list using merge sort with comparison queries. -/
@[expose] def mergeSort (xs : List α) : FreeM (LEQuery α) (List α) :=
  match xs with
  | [] => return []
  | [x] => return [x]
  | x :: y :: zs => do
    let halves := split (x :: y :: zs)
    let sl ← mergeSort halves.1
    let sr ← mergeSort halves.2
    merge sl sr
termination_by xs.length
decreasing_by
  · simp only [split_fst_length_eq, List.length_cons]; omega
  · simp only [split_snd_length_eq, List.length_cons]; omega

end Cslib.Query
