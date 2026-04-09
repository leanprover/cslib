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
theorem rank_lt_rootOf (uf : UF n) (x : Fin n) (hx : ¬uf.isRoot x) :
    uf.rank x < uf.rank (uf.rootOf x) := by
  unfold UF.rootOf; simp [UF.isRoot] at hx; simp [hx]
  have h_lt := uf.rank_lt x hx
  by_cases hp : uf.isRoot (uf.parent x)
  · rw [UF.rootOf_root uf (uf.parent x) hp]; exact h_lt
  · exact Nat.lt_trans h_lt (rank_lt_rootOf uf (uf.parent x) hp)
termination_by uf.rankMax - uf.rank x
decreasing_by
  have := uf.rank_lt x hx
  have := uf.rank_le_max (uf.parent x)
  omega

/-- Internal find that carries rank-preservation, rankMax-preservation, and rootOf
    proofs through the recursion, avoiding circular dependencies with Correctness.lean. -/
def findAux (uf : UF n) (x : Fin n) :
    { tm : TimeM ℕ (Fin n × UF n) //
      tm.ret.2.rank = uf.rank ∧
      tm.ret.2.rankMax = uf.rankMax ∧
      tm.ret.1 = uf.rootOf x ∧
      (∀ y : Fin n, uf.isRoot y → tm.ret.2.isRoot y) ∧
      (∀ y : Fin n, tm.ret.2.rootOf y = uf.rootOf y) } :=
  if h : uf.parent x = x then
    ⟨pure (x, uf),
     rfl, rfl,
     by simp [UF.rootOf, h],
     fun _ hy => hy,
     fun _ => rfl⟩
  else
    let ih := findAux uf (uf.parent x)
    let root := ih.val.ret.1
    let uf' := ih.val.ret.2
    let h_rank_eq : uf'.rank = uf.rank := ih.property.1
    let h_max_eq : uf'.rankMax = uf.rankMax := ih.property.2.1
    let h_root_eq : root = uf.rootOf (uf.parent x) := ih.property.2.2.1
    let h_pres := ih.property.2.2.2.1
    let h_rootOf := ih.property.2.2.2.2
    have h_rank : uf'.rank x < uf'.rank root := by
      rw [h_rank_eq]
      conv => rhs; rw [h_root_eq]
      rw [UF.rootOf_parent uf x h]
      exact rank_lt_rootOf uf x h
    have h_ne : x ≠ root := by
      intro heq
      have := h_rank
      rw [heq] at this
      omega
    have h_root_in_uf' : uf'.rootOf x = root := by
      rw [h_rootOf x]
      conv_lhs => rw [UF.rootOf]; simp [h]
      exact h_root_eq.symm
    ⟨⟨(root, uf'.setParent x root h_rank), 1 + ih.val.time⟩,
     by show (uf'.setParent x root h_rank).rank = uf.rank
        rw [UF.setParent_rank]; exact h_rank_eq,
     by show (uf'.setParent x root h_rank).rankMax = uf.rankMax
        rw [UF.setParent_rankMax]; exact h_max_eq,
     by show root = uf.rootOf x
        rw [h_root_eq, UF.rootOf_parent uf x h],
     fun y hy => by
        show (uf'.setParent x root h_rank).isRoot y
        by_cases hyx : y = x
        · exfalso; rw [hyx] at hy; exact h hy
        · exact UF.setParent_isRoot_of_ne uf' x root h_rank y (h_pres y hy) hyx,
     fun y => by
        show (uf'.setParent x root h_rank).rootOf y = uf.rootOf y
        rw [UF.setParent_preserves_rootOf uf' x root h_rank h_root_in_uf' y]
        exact h_rootOf y⟩
termination_by uf.rankMax - uf.rank x
decreasing_by
  have h1 := uf.rank_lt x h
  have h2 := uf.rank_le_max (uf.parent x)
  omega

/-- Find the root of `x` with path compression, counting parent-pointer traversals.
Returns `(root, compressed_uf)`. -/
def find (uf : UF n) (x : Fin n) : TimeM ℕ (Fin n × UF n) :=
  (findAux uf x).val

/-- `find` does not change the rank function. -/
theorem find_ret_rank_eq (uf : UF n) (x : Fin n) :
    (⟪find uf x⟫).2.rank = uf.rank :=
  (findAux uf x).property.1

/-- `find` does not change rankMax. -/
theorem find_ret_rankMax_eq (uf : UF n) (x : Fin n) :
    (⟪find uf x⟫).2.rankMax = uf.rankMax :=
  (findAux uf x).property.2.1

/-- `find` returns the same root as the pure `rootOf`. -/
theorem find_ret_rootOf_eq (uf : UF n) (x : Fin n) :
    (⟪find uf x⟫).1 = uf.rootOf x :=
  (findAux uf x).property.2.2.1

/-- `find` returns a root of the (possibly compressed) UF. -/
theorem find_ret_isRoot (uf : UF n) (x : Fin n) :
    (⟪find uf x⟫).2.isRoot (⟪find uf x⟫).1 := by
  have h3 := (findAux uf x).property.2.2.1  -- ret.1 = rootOf x
  have h5 := (findAux uf x).property.2.2.2.2  -- preserves rootOf
  -- (compressed).isRoot ((compressed).rootOf x)
  have hir := UF.rootOf_isRoot (findAux uf x).val.ret.2 x
  -- (compressed).rootOf x = uf.rootOf x
  have heq : (findAux uf x).val.ret.2.rootOf x = (findAux uf x).val.ret.1 := by
    rw [h5 x]; exact h3.symm
  rwa [heq] at hir

/-- `find` preserves root status of other nodes. -/
theorem find_preserves_roots (uf : UF n) (x y : Fin n)
    (hy : uf.isRoot y) : (⟪find uf x⟫).2.isRoot y :=
  (findAux uf x).property.2.2.2.1 y hy

/-- `find` preserves `rootOf` for all nodes. -/
theorem find_preserves_rootOf (uf : UF n) (x y : Fin n) :
    (⟪find uf x⟫.2).rootOf y = uf.rootOf y :=
  (findAux uf x).property.2.2.2.2 y

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
def union (uf : UF n) (x y : Fin n) : TimeM ℕ (UF n) :=
  let res₁ := find uf x
  let rx := res₁.ret.1
  let uf₁ := res₁.ret.2
  let res₂ := find uf₁ y
  let ry := res₂.ret.1
  let uf₂ := res₂.ret.2
  if h : rx = ry then
    ⟨uf₂, res₁.time + res₂.time⟩
  else
    have hx : uf₂.isRoot rx := find_preserves_roots uf₁ y rx (find_ret_isRoot uf x)
    have hy : uf₂.isRoot ry := find_ret_isRoot uf₁ y
    ⟨link uf₂ rx ry hx hy h, res₁.time + res₂.time⟩

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
