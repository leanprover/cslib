/-
Copyright (c) 2026 Christopher J. R. Lloyd. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher J. R. Lloyd
-/
module

public import Cslib.Algorithms.Lean.TimeM


/-!
# List Algorithms

In this file we prove `List.length` runs in eaxctly n steps using the
time monad over the list `TimeM Nat Nat`. The time complexity of
`List.length` is the length of the List.

--
## Main results

- `List.length_time`: `List.length` runs in exactly n steps

-/

namespace Cslib.Algorithms.Lean.ListLength

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM

/-- List.Length with TimeM Monad. -/
public def List.length : List α → TimeM Nat Nat
  | .nil => return 0
  | .cons _ as => do ✓ ((fun x => x + 1) <$> (List.length as))

section Correctness

/-- List.Length matches List.length in Batteries. -/
theorem ret_list_length : ∀ xs : List α, ⟪List.length xs⟫ = _root_.List.length xs := by
 intros
 fun_induction List.length with grind [List.length]

end Correctness

section TimeComplexity

/-- The recursive list length algorithm runs in `n` steps for a list of length `n`. -/
public theorem List.length_time (xs : List α) : (List.length xs).time = _root_.List.length xs := by
  fun_induction List.length with grind [List.length]

end TimeComplexity

end Cslib.Algorithms.Lean.ListLength
