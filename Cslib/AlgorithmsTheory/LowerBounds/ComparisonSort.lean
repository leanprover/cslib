/-
Copyright (c) 2025 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Cslib.AlgorithmsTheory.QueryModel
public import Cslib.AlgorithmsTheory.Models.ListComparisonSort
import all Init.Data.List.Sort.Basic

public import Mathlib

@[expose] public section

namespace Cslib

namespace Algorithms

open Prog

theorem cmpSort_lower_bound
    (P : List α → Prog (SortOps α) (List α)) (le : α → α → Bool)
    (l : List α)
    (hLen : l.length ≤ 1)
    [Std.Total (fun x y => le x y = true)] [IsTrans α (fun x y => le x y = true)] :
    ((P l).eval (sortModelNat le)).Pairwise (fun x y => le x y = true) →
    (P l).time (sortModelNat le) ≥ l.length * (Nat.log 2 l.length) := by
  intro _
  cases l with
  | nil =>
      simp
  | cons x xs =>
      cases xs with
      | nil =>
          simp
      | cons y ys =>
          simp at hLen



end Algorithms

end Cslib
