/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Shreyas Srinivas, Sorrachai Yingchareonthawornchai
-/
module

public import Cslib.Algorithms.Lean.Query.Sort.LEQuery

/-! # Merge Sort as a Query Program

Merge sort implemented as a `Prog (LEQuery α)`, making all comparison queries explicit.
Uses an alternating split (odds/evens) to avoid needing `List.length` in the termination
argument.
-/

open Cslib.Query

public section

namespace Cslib.Query

/-- Split a list into two halves by alternating elements. -/
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

theorem split_fst_length_eq : ∀ (xs : List α),
    (split xs).1.length = (xs.length + 1) / 2
  | [] => by simp [split]
  | [_] => by simp [split]
  | _ :: _ :: zs => by
    simp only [split_cons_cons, List.length_cons]
    have := split_fst_length_eq zs
    omega

theorem split_snd_length_eq : ∀ (xs : List α),
    (split xs).2.length = xs.length / 2
  | [] => by simp [split]
  | [_] => by simp [split]
  | _ :: _ :: zs => by
    simp only [split_cons_cons, List.length_cons]
    have := split_snd_length_eq zs
    omega

theorem split_fst_length_lt (x y : α) (zs : List α) :
    (split (x :: y :: zs)).1.length < (x :: y :: zs).length := by
  simp only [split_fst_length_eq, List.length_cons]; omega

theorem split_snd_length_lt (x y : α) (zs : List α) :
    (split (x :: y :: zs)).2.length < (x :: y :: zs).length := by
  simp only [split_snd_length_eq, List.length_cons]; omega

/-- Merge two sorted lists using comparison queries. -/
@[expose] def merge (xs ys : List α) : Prog (LEQuery α) (List α) :=
  match xs, ys with
  | [], ys => pure ys
  | xs, [] => pure xs
  | x :: xs', y :: ys' => do
    let le ← LEQuery.ask x y
    if le then do
      let rest ← merge xs' (y :: ys')
      pure (x :: rest)
    else do
      let rest ← merge (x :: xs') ys'
      pure (y :: rest)
termination_by xs.length + ys.length

/-- Sort a list using merge sort with comparison queries. -/
@[expose] def mergeSort (xs : List α) : Prog (LEQuery α) (List α) :=
  match xs with
  | [] => pure []
  | [x] => pure [x]
  | x :: y :: zs => do
    let sl ← mergeSort (split (x :: y :: zs)).1
    let sr ← mergeSort (split (x :: y :: zs)).2
    merge sl sr
termination_by xs.length
decreasing_by
  · exact split_fst_length_lt x y zs
  · exact split_snd_length_lt x y zs

end Cslib.Query

end -- public section
