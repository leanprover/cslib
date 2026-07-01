/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

import Cslib.Algorithms.Lean.UnionFind.Cost
import Cslib.Algorithms.Lean.UnionFind.Operations

namespace CslibTests

/-! # Tests for union-by-rank union-find

These tests exercise the public union-find API: the singleton forest is
well-formed, `find` on a singleton takes zero steps, linking two distinct roots
preserves well-formedness, and the `find_time_le_log` bound instantiates
concretely.
-/

open Cslib.Algorithms.Lean.UnionFind

-- `singleton` from this namespace is shadowed by the `{·}` set-builder `Singleton.singleton`,
-- so we expose the union-find constructor under an unambiguous local name.
open Cslib.Algorithms.Lean.UnionFind renaming singleton → ufSingleton

/-- The singleton forest is well-formed. -/
example : (ufSingleton 8).WellFormed := singleton_wellFormed

/-- In a singleton forest every node is already a root, so `find` takes zero steps. -/
example (i : Fin 8) : (ufSingleton 8).findDepth singleton_wellFormed i = 0 := by
  unfold findDepth
  rw [Nat.find_eq_zero]
  simp

/-- Linking two distinct singleton roots preserves well-formedness. -/
example : ((ufSingleton 3).link 0 1).WellFormed :=
  link_wellFormed (ufSingleton 3) singleton_wellFormed
    (singleton_isRoot 0) (singleton_isRoot 1) (by decide)

/-- The O(log n) bound instantiated: `find` on 8 elements costs at most `⌊log₂ 8⌋ = 3` ticks. -/
example (i : Fin 8) : ((ufSingleton 8).find singleton_wellFormed i).time ≤ Nat.log 2 8 :=
  find_time_le_log (ufSingleton 8) singleton_wellFormed i

end CslibTests
