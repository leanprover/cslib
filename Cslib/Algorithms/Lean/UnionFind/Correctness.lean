/-
Copyright (c) 2026 Juan Bono. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Bono
-/

module

public import Cslib.Algorithms.Lean.UnionFind.Operations
public import Mathlib.Data.Nat.Log

@[expose] public section

/-!
# Union-Find Correctness

Proves additional properties of `find` and `link` beyond what Operations.lean provides.

## Main results (in Operations.lean)
- `find_ret_isRoot`: `find` returns a root
- `find_ret_rank_eq`: `find` does not change ranks
- `find_ret_rootOf_eq`: `find` returns `rootOf`
- `find_preserves_roots`: `find` does not change which nodes are roots

## Main results (in Operations.lean)
- `find_preserves_rootOf`: `find` preserves `rootOf` for all nodes

## Main results (here)
- `link_rootOf`: link merges exactly two equivalence classes
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.UnionFind

open Cslib.Algorithms.Lean.TimeM

variable {n : ℕ}

/-! ### link correctness -/

/-- After linking rx and ry, the root of any node is either the old root
or the new combined root. -/
theorem link_rootOf (uf : UF n) (rx ry : Fin n)
    (hx : uf.isRoot rx) (hy : uf.isRoot ry) (hne : rx ≠ ry) (z : Fin n) :
    (link uf rx ry hx hy hne).rootOf z =
      if uf.rootOf z = rx ∨ uf.rootOf z = ry then
        if uf.rank rx < uf.rank ry then ry
        else rx
      else uf.rootOf z := by
  sorry

/-! ### Rank bound -/

/-- In any UF reachable from init via find/union, all ranks are ≤ log₂ n. -/
theorem rank_le_log_of_runOps (n : ℕ) (hn : 2 ≤ n) (ops : List (Op n)) (x : Fin n) :
    (⟪runOps (UF.init n) ops⟫).rank x ≤ Nat.log 2 n := by
  sorry

/-- Corollary: ranks are < n for reachable states. -/
theorem rank_lt_of_runOps (n : ℕ) (hn : 2 ≤ n) (ops : List (Op n)) (x : Fin n) :
    (⟪runOps (UF.init n) ops⟫).rank x < n := by
  sorry

end Cslib.Algorithms.Lean.UnionFind
