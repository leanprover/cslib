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
most `⌊log₂ n⌋`, and uses this bound to define the `find` traversal abstractly.

## Main definitions

* `UnionFind.findDepth`: The number of parent dereferences needed to reach the root from `i`.
* `UnionFind.findRoot`: The root reached from `i` by following `findDepth` parent pointers.

## Main results

* `UnionFind.rank_le_log`: In a well-formed forest, `rank i ≤ Nat.log 2 n` for all `i`.
* `UnionFind.exists_isRoot_iterate`: Following parent pointers from any node eventually
  reaches a root.
* `UnionFind.isRoot_findRoot`: `findRoot hwf i` is always a root.
* `UnionFind.not_isRoot_of_lt_findDepth`: Every step strictly before `findDepth` lands on
  a non-root.
* `UnionFind.rank_iterate_ge`: Along the find path, the rank grows by at least one per step.
* `UnionFind.findDepth_le_log`: In a well-formed forest, `find` dereferences at most
  `⌊log₂ n⌋` parent pointers.
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

/-- Following parent pointers from any node reaches a root in finitely many steps. -/
theorem exists_isRoot_iterate (hwf : uf.WellFormed) (i : Fin n) :
    ∃ k, uf.IsRoot (uf.parent^[k] i) := by
  by_contra h
  push Not at h
  set f : ℕ → ℕ := fun k => uf.rank (uf.parent^[k] i) with hf
  have hmono : StrictMono f := by
    apply strictMono_nat_of_lt_succ
    intro k
    have hk : ¬ uf.IsRoot (uf.parent^[k] i) := h k
    have := hwf.rank_lt (uf.parent^[k] i) hk
    simp only [hf]
    rw [Function.iterate_succ_apply']
    exact this
  have hle : ∀ k, k ≤ f k := by
    intro k
    induction k with
    | zero => exact Nat.zero_le _
    | succ m ih => exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (hmono (Nat.lt_succ_self m)))
  have hbound : ∀ k, f k ≤ Nat.log 2 n := fun k => uf.rank_le_log hwf _
  have h1 := hle (Nat.log 2 n + 1)
  have h2 := hbound (Nat.log 2 n + 1)
  omega

/-- The number of parent dereferences `find` performs to take `i` to its root. -/
noncomputable def findDepth (hwf : uf.WellFormed) (i : Fin n) : ℕ :=
  Nat.find (uf.exists_isRoot_iterate hwf i)

/-- The root that `find` returns for `i`. -/
noncomputable def findRoot (hwf : uf.WellFormed) (i : Fin n) : Fin n :=
  uf.parent^[uf.findDepth hwf i] i

/-- `findRoot` indeed lands on a root. -/
lemma isRoot_findRoot (hwf : uf.WellFormed) (i : Fin n) : uf.IsRoot (uf.findRoot hwf i) := by
  unfold findRoot findDepth
  exact Nat.find_spec (uf.exists_isRoot_iterate hwf i)

/-- Every step strictly before `findDepth` lands on a non-root. -/
lemma not_isRoot_of_lt_findDepth (hwf : uf.WellFormed) (i : Fin n) {k : ℕ}
    (hk : k < uf.findDepth hwf i) : ¬ uf.IsRoot (uf.parent^[k] i) := by
  unfold findDepth at hk
  exact Nat.find_min (uf.exists_isRoot_iterate hwf i) hk

/-- For every `k ≤ findDepth`, the rank has grown by at least `k` along the find path. -/
lemma rank_iterate_ge (hwf : uf.WellFormed) (i : Fin n) :
    ∀ k, k ≤ uf.findDepth hwf i → uf.rank i + k ≤ uf.rank (uf.parent^[k] i) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    intro hk
    have hk' : k < uf.findDepth hwf i := by omega
    have hkle : k ≤ uf.findDepth hwf i := by omega
    have hnot : ¬ uf.IsRoot (uf.parent^[k] i) := uf.not_isRoot_of_lt_findDepth hwf i hk'
    have hstep : uf.rank (uf.parent^[k] i) < uf.rank (uf.parent (uf.parent^[k] i)) :=
      hwf.rank_lt (uf.parent^[k] i) hnot
    have hih := ih hkle
    rw [Function.iterate_succ_apply']
    omega

/-- `find` dereferences at most `⌊log₂ n⌋` parent pointers. -/
theorem findDepth_le_log (hwf : uf.WellFormed) (i : Fin n) :
    uf.findDepth hwf i ≤ Nat.log 2 n := by
  have h := uf.rank_iterate_ge hwf i (uf.findDepth hwf i) le_rfl
  have hroot : uf.parent^[uf.findDepth hwf i] i = uf.findRoot hwf i := rfl
  rw [hroot] at h
  have hbound := uf.rank_le_log hwf (uf.findRoot hwf i)
  omega

end Cslib.Algorithms.Lean.UnionFind
