/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Shreyas Srinivas, Sorrachai Yingchareonthawornchai
-/
module

public import Cslib.Algorithms.Lean.Query.Sort.LEQuery

/-! # Merge Sort as a Query Program

Merge sort implemented as a `FreeM (LEQuery α)`, making all comparison queries explicit.
The alternating split (odds/evens) is structurally recursive: each recursive call consumes
two constructors and operates directly on the remaining tail, so `split` needs no
well-founded recursion argument based on `List.length`. The recursive calls of `mergeSort`
itself are not structural, since the two halves are not syntactic subterms, and are justified
separately using their lengths.
-/

open Cslib Cslib.Query

public section

namespace Cslib.Query

/-- Split a list into two halves by alternating elements.

Unlike `List.MergeSort.Internal.splitInTwo`, which cuts the list at its midpoint, this
alternating split is structurally recursive, which makes the termination argument and the
proofs about `mergeSort` simpler. The price is that the split is not stable. -/
@[expose] def split : List α → List α × List α
  | [] => ([], [])
  | [x] => ([x], [])
  | x :: y :: zs =>
    let (l, r) := split zs
    (x :: l, y :: r)

@[simp] theorem split_nil : split (α := α) [] = ([], []) := rfl
@[simp] theorem split_singleton (x : α) : split [x] = ([x], []) := rfl
@[simp] theorem split_cons_cons (x y : α) (zs : List α) :
    split (x :: y :: zs) = ((split zs).1 |>.cons x, (split zs).2 |>.cons y) := by
  simp [split]

@[simp] theorem split_fst_length_eq : ∀ (xs : List α),
    (split xs).1.length = (xs.length + 1) / 2
  | [] => by simp [split]
  | [_] => by simp [split]
  | _ :: _ :: zs => by
    simp only [split_cons_cons, List.length_cons]
    have := split_fst_length_eq zs
    omega

@[simp] theorem split_snd_length_eq : ∀ (xs : List α),
    (split xs).2.length = xs.length / 2
  | [] => by simp [split]
  | [_] => by simp [split]
  | _ :: _ :: zs => by
    simp only [split_cons_cons, List.length_cons]
    have := split_snd_length_eq zs
    omega

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
