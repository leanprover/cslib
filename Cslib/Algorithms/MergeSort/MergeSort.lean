/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

import Cslib.Algorithms.QueryModel

/-!
# Merge sort in the query model

This file implements merge sort as a program in the query model defined in
`Cslib.Algorithms.QueryModel`. The algorithm uses only comparison queries.

## Main definitions

- `merge`     : merge step using `Prog` comparisons
- `split`     : split a list in two by alternating elements
- `mergeSort` : merge sort expressed in the query model

We also provide simple example evaluations of `mergeSort` and its time cost.
-/

open Cslib

namespace Cslib.Algorithms.MergeSort.QueryBased

open Cslib.Algorithms Model


/-- The Model for comparison sorting natural-number registers.
-/
inductive ListSortOps (α : Type) : Type → Type  where
  | cmp :  (l : List α) → (i j : Fin l.length) → ListSortOps α Bool
  | write : (l : List α) → (i : Fin l.length) → (x : α) → ListSortOps α (List α)
  | read : (l : List α) → (i : Fin l.length) → ListSortOps α α


def ListSort_WorstCase [DecidableEq α] : Model (ListSortOps α) where
  evalQuery q :=
    match q with
    | .write l i x => l.set i x
    | .cmp l i j =>  l[i] == l[j]
    | .read l i => l.get i
  cost q :=
    match q with
    | .write l i x => l.length
    | .read l i =>  l.length
    | .cmp l i j => l.length

/--
The array version of the sort operations
-/
inductive ArraySortOps (α : Type) : Type → Type  where
  | swap : (a : Array α) → (i j : Fin a.size) → ArraySortOps α (Array α)
  | cmp :  (a : Array α) → (i j : Fin a.size) → ArraySortOps α Bool
  | write : (a : Array α) → (i : Fin a.size) → (x : α) → ArraySortOps α (Array α)
  | read : (a : Array α) → (i : Fin a.size) → ArraySortOps α α

def ArraySort_WorstCase [DecidableEq α] : Model (ArraySortOps α) where
  evalQuery q :=
    match q with
    | .write a i x => a.set i x
    | .cmp l i j =>  l[i] == l[j]
    | .read l i => l[i]
    | .swap l i j => l.swap i j
  cost q :=
    match q with
    | .write l i x => 1
    | .read l i =>  1
    | .cmp l i j => 1
    | .swap l i j => 1

def exampleCode (a : Array Int) (h : a.size > 0): Prog (ArraySortOps Int) (Int) := do
  for hi : i in [:a.size] do
    return ArraySortOps.write a ⟨i, by grind⟩ 1
  return (ArraySortOps.read a ⟨0, by grind⟩)

-- /-- Merge two sorted lists using comparisons in the query monad. -/
-- def merge (x y : List Nat) : Prog (ListSortOps Nat) (List Nat) := do
--   match x,y with
--   | [], ys => pure ys
--   | xs, [] => pure xs
--   | x :: xs', y :: ys' => do
--       if x ≤ y then
--         let rest ← merge xs' (y :: ys')
--         pure (x :: rest)
--       else
--         let rest ← merge (x :: xs') ys'
--         pure (y :: rest)

-- /-- Split a list into two lists by alternating elements. -/
-- def split (xs : List Nat) : List Nat × List Nat :=
--   let rec go : List Nat → List Nat → List Nat → List Nat × List Nat
--     | [], accL, accR => (accL.reverse, accR.reverse)
--     | [x], accL, accR => ((x :: accL).reverse, accR.reverse)
--     | x :: y :: xs, accL, accR => go xs (x :: accL) (y :: accR)
--   go xs [] []

-- /-- Merge sort expressed as a program in the query model.
-- TODO: Working version without partial -/
-- partial def mergeSort : List Nat → Prog (ListSortOps Nat) (List Nat)
--   | []      => pure []
--   | [x]     => pure [x]
--   | xs      =>
--     let (left, right) := split xs
--     do
--       let sortedLeft  ← mergeSort left
--       let sortedRight ← mergeSort right
--       merge sortedLeft sortedRight

-- #eval Prog.eval (mergeSort [5,3,8,6,2,7,4,1]) ListSort_WorstCase
-- #eval Prog.time (mergeSort [5,3,8,6,2,7,4,1]) ListSort_WorstCase

end Cslib.Algorithms.MergeSort.QueryBased
