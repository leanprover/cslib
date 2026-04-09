/-
Copyright (c) 2026 Juan Bono. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Bono
-/

module

public import Cslib.Algorithms.Lean.UnionFind.Basic
public import Cslib.Algorithms.Lean.TimeM

@[expose] public section

/-!
# Union-Find Operations in TimeM

Defines `find` (with path compression), `link` (union by rank), and `union`
as operations in the `TimeM ℕ` monad, where each parent-pointer traversal
in `find` costs 1 tick.

## Cost Model
- Each parent-pointer follow in `find`: 1 tick
- Everything else (comparisons, pointer writes): free
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.UnionFind

open Cslib.Algorithms.Lean.TimeM

variable {n : ℕ}

/-- Rank of any non-root x is less than rank of its rootOf. -/
theorem rank_lt_rootOf (uf : UF n) (x : Fin n) (h : ¬uf.parent x = x) :
    uf.rank x < uf.rank (uf.rootOf x) := by
  unfold UF.rootOf; simp [h]
  have h_lt := uf.rank_lt x h
  by_cases hp : uf.parent (uf.parent x) = uf.parent x
  · rw [UF.rootOf_root uf (uf.parent x) hp]; exact h_lt
  · exact Nat.lt_trans h_lt (rank_lt_rootOf uf (uf.parent x) hp)
termination_by uf.rankMax - uf.rank x
decreasing_by
  have := uf.rank_lt x h
  have := uf.rank_le_max (uf.parent x)
  omega

/-- Find the root of `x` with path compression, counting parent-pointer traversals.
Returns `(root, compressed_uf)`. -/
def find (uf : UF n) (x : Fin n) : TimeM ℕ (Fin n × UF n) :=
  if h : uf.parent x = x then
    pure (x, uf)
  else do
    ✓ let _ := ()
    let (root, uf') ← find uf (uf.parent x)
    have h_rank : uf'.rank x < uf'.rank root := by sorry
    pure (root, uf'.setParent x root h_rank)
termination_by uf.rankMax - uf.rank x
decreasing_by
  have h1 := uf.rank_lt x h
  have h2 := uf.rank_le_max (uf.parent x)
  omega

/-- Link two distinct roots by rank. Does not cost any ticks.
Attaches the lower-ranked root under the higher-ranked one.
On equal rank, attaches `ry` under `rx` and increments `rx`'s rank. -/
def link (uf : UF n) (rx ry : Fin n)
    (hx : uf.isRoot rx) (hy : uf.isRoot ry)
    (hne : rx ≠ ry) : UF n :=
  if h : uf.rank rx < uf.rank ry then
    { parent := fun z => if z = rx then ry else uf.parent z
      rank := uf.rank
      rankMax := uf.rankMax
      rank_lt := by
        intro z hz
        split_ifs at hz ⊢ with heq
        · subst heq; exact h
        · exact uf.rank_lt z hz
      rank_le_max := uf.rank_le_max }
  else if h2 : uf.rank ry < uf.rank rx then
    { parent := fun z => if z = ry then rx else uf.parent z
      rank := uf.rank
      rankMax := uf.rankMax
      rank_lt := by
        intro z hz
        split_ifs at hz ⊢ with heq
        · subst heq; exact h2
        · exact uf.rank_lt z hz
      rank_le_max := uf.rank_le_max }
  else
    have heq : uf.rank rx = uf.rank ry := by omega
    { parent := fun z => if z = ry then rx else uf.parent z
      rank := fun z => if z = rx then uf.rank rx + 1 else uf.rank z
      rankMax := uf.rankMax + 1
      rank_lt := by
        intro z hz
        simp only [ne_eq] at hz ⊢
        by_cases h_zy : z = ry
        · simp only [h_zy, ite_true] at hz ⊢
          have hne' : (ry : Fin n) ≠ rx := hne.symm
          simp only [hne', ite_false]
          omega
        · simp only [h_zy, ite_false] at hz ⊢
          have h_rank_lt := uf.rank_lt z hz
          by_cases h_zx : z = rx
          · subst h_zx
            exact absurd hx hz
          · simp only [h_zx, ite_false]
            by_cases h_px : uf.parent z = rx
            · rw [if_pos h_px]; rw [h_px] at h_rank_lt; omega
            · rw [if_neg h_px]; exact h_rank_lt
      rank_le_max := by
        intro z
        by_cases h_zx : z = rx
        · simp only [h_zx, ↓reduceIte]; have := uf.rank_le_max rx; omega
        · simp only [h_zx, ↓reduceIte]; have := uf.rank_le_max z; omega }

/-- Union two elements: find both roots, then link them. -/
def union (uf : UF n) (x y : Fin n) : TimeM ℕ (UF n) := do
  let (rx, uf₁) ← find uf x
  let (ry, uf₂) ← find uf₁ y
  if h : rx = ry then
    pure uf₂
  else
    have hx : uf₂.isRoot rx := by sorry
    have hy : uf₂.isRoot ry := by sorry
    pure (link uf₂ rx ry hx hy h)

/-- An operation on a union-find of `n` elements. -/
inductive Op (n : ℕ) where
  | find  : Fin n → Op n
  | union : Fin n → Fin n → Op n

/-- Execute a single operation. -/
def runOp (uf : UF n) : Op n → TimeM ℕ (UF n)
  | .find x => do let (_, uf') ← find uf x; pure uf'
  | .union x y => union uf x y

/-- Execute a sequence of operations, threading state and accumulating time. -/
def runOps (uf : UF n) : List (Op n) → TimeM ℕ (UF n)
  | [] => pure uf
  | op :: ops => do
    let uf' ← runOp uf op
    runOps uf' ops

@[simp] theorem runOps_nil (uf : UF n) : runOps uf [] = pure uf := rfl

theorem runOps_cons (uf : UF n) (op : Op n) (ops : List (Op n)) :
    runOps uf (op :: ops) = (runOp uf op) >>= (fun uf' => runOps uf' ops) := rfl

end Cslib.Algorithms.Lean.UnionFind
