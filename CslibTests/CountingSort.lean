/-
Copyright (c) 2026 Robert Joseph George. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George
-/
import Cslib.Algorithms.Lean.Sort.Counting

/-! # Tests for counting sort

Executable checks that counting sort orders by key, keeps elements with equal keys in input
order, and charges one tick per element plus one per bucket.
-/

set_option linter.hashCommand false

open Cslib.Algorithms.Lean

/-- Pairs keyed by their first component, with the key `2` occurring twice. -/
def keyedPairs : List (Fin 3 × String) := [(2, "a"), (0, "b"), (2, "c"), (1, "d")]

-- Sorted by key, and the two pairs with key `2` keep their input order.
#guard keyedPairs.countingSort Prod.fst == [(0, "b"), (1, "d"), (2, "a"), (2, "c")]

-- The timed version returns the same list and charges 4 ticks for the elements plus 3 for
-- the buckets.
#guard (TimeM.countingSort Prod.fst keyedPairs).ret == keyedPairs.countingSort Prod.fst
#guard (TimeM.countingSort Prod.fst keyedPairs).time == 7

-- The charged cost is the length plus the number of keys, whatever the input.
example (l : List (Fin 3 × String)) : (TimeM.countingSort Prod.fst l).time = l.length + 3 :=
  TimeM.time_countingSort _ _
