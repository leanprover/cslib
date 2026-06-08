/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module

public import Cslib.Init
public import Cslib.Algorithms.Lean.UnionFind.Basic
public import Mathlib.Data.Nat.Log

/-!
# Rank Bound for Union-Find

This file proves that in a well-formed union-by-rank forest, every rank is at
most `⌊log₂ n⌋`.

## Main results

* `UnionFind.rank_le_log`: In a well-formed forest, `rank i ≤ Nat.log 2 n` for all `i`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.UnionFind

variable {n : ℕ} (uf : UnionFind n)

/-- In a well-formed forest, every rank is at most `⌊log₂ n⌋`. -/
theorem rank_le_log (hwf : uf.WellFormed) (i : Fin n) : uf.rank i ≤ Nat.log 2 n := by
  have hsize_ge : 2 ^ uf.rank i ≤ uf.subtreeSize i := hwf.size_ge i
  have hsize_le : uf.subtreeSize i ≤ n := uf.subtreeSize_le i
  have h1 : uf.rank i ≤ Nat.log 2 (uf.subtreeSize i) :=
    Nat.le_log_of_pow_le (by omega) hsize_ge
  exact h1.trans (Nat.log_mono_right hsize_le)

end Cslib.Algorithms.Lean.UnionFind
