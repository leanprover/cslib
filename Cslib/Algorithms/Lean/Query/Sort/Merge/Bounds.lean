/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Cslib.Algorithms.Lean.Query.Sort.LowerBound
public import Cslib.Algorithms.Lean.Query.Sort.Merge.Lemmas

/-! # Merge Sort: Combined Bounds

Instantiating the general comparison-sorting lower bound at `mergeSort`, and comparing it
with the `n * ⌈log₂ n⌉` upper bound. Since `LowerBound.le_upperBound` makes the two
bounds meet, the purely arithmetic fact `⌈log₂ n!⌉ ≤ n * ⌈log₂ n⌉` falls out of the
framework with no further work.
-/

open Cslib Cslib.Query

public section

namespace Cslib.Query

variable {α : Type}

/-- Merge sort has worst-case query complexity at least `⌈log₂(n!)⌉`. -/
theorem mergeSort_lowerBound [Infinite α] :
    LowerBound (mergeSort (α := α)) List.length (fun n => Nat.clog 2 (Nat.factorial n)) :=
  mergeSort_isSort.lowerBound_infinite

/-- Sanity check that the bounds compose: comparing merge sort's upper and lower bounds
    yields this arithmetic fact with no further work. -/
theorem clog_factorial_le_mul_clog (n : ℕ) :
    Nat.clog 2 (Nat.factorial n) ≤ n * Nat.clog 2 n :=
  (mergeSort_lowerBound (α := ℕ)).le_upperBound mergeSort_upperBound n

end Cslib.Query
