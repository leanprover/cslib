/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module

public import Cslib.Init
public import Cslib.Algorithms.Lean.UnionFind.RankBound
public import Cslib.Algorithms.Lean.TimeM

/-!
# Timed `find` for Union-Find

This file expresses the `find` operation of union-find in the `TimeM` cost monad,
charging one tick per parent dereference. We prove that `find` returns the correct
root (`find_ret`), that its tick cost equals the find depth (`find_time`), and that
in a well-formed union-by-rank forest it runs in at most `⌊log₂ n⌋` ticks
(`find_time_le_log`).

Following the `TimeM` convention, correctness is proved on `.ret` and complexity on
`.time`.

## Main definitions

* `UnionFind.findAux`: follow `k` parent pointers from `x`, charging one tick per hop.
* `UnionFind.find`: follow parent pointers to the root, charging one tick per dereference.

## Main results

* `UnionFind.find_ret`: `find` returns the root of `i`.
* `UnionFind.find_time`: `find`'s tick cost equals the find depth.
* `UnionFind.find_time_le_log`: `find` runs in at most `⌊log₂ n⌋` ticks.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.UnionFind

open Cslib.Algorithms.Lean (TimeM)

variable {n : ℕ} (uf : UnionFind n)

/-- Auxiliary for `find`: follow `k` parent pointers from `x`, charging one tick per hop. -/
def findAux (uf : UnionFind n) : ℕ → Fin n → TimeM ℕ (Fin n)
  | 0, x => pure x
  | (k + 1), x => do ✓ uf.findAux k (uf.parent x)

/-- The value returned by `findAux k x` is the `k`-th parent iterate of `x`. -/
@[simp] lemma findAux_ret (k : ℕ) (x : Fin n) : (uf.findAux k x).ret = uf.parent^[k] x := by
  induction k generalizing x with
  | zero => simp [findAux]
  | succ k ih => simp [findAux, ih]

/-- `findAux k x` costs exactly `k` ticks. -/
@[simp] lemma findAux_time (k : ℕ) (x : Fin n) : (uf.findAux k x).time = k := by
  induction k generalizing x with
  | zero => simp [findAux]
  | succ k ih => simp [findAux, ih]; omega

/-- `find i` follows parent pointers to `i`'s root, charging one tick per dereference. -/
noncomputable def find (hwf : uf.WellFormed) (i : Fin n) : TimeM ℕ (Fin n) :=
  uf.findAux (uf.findDepth hwf i) i

/-- `find` returns the root of `i`. -/
lemma find_ret (hwf : uf.WellFormed) (i : Fin n) : (uf.find hwf i).ret = uf.findRoot hwf i := by
  simp [find, findAux_ret, findRoot]

/-- `find`'s tick cost is exactly the find depth. -/
lemma find_time (hwf : uf.WellFormed) (i : Fin n) : (uf.find hwf i).time = uf.findDepth hwf i := by
  simp [find, findAux_time]

/-- `find` runs in at most `⌊log₂ n⌋` ticks. -/
theorem find_time_le_log (hwf : uf.WellFormed) (i : Fin n) :
    (uf.find hwf i).time ≤ Nat.log 2 n := by
  rw [uf.find_time hwf i]; exact uf.findDepth_le_log hwf i

end Cslib.Algorithms.Lean.UnionFind
