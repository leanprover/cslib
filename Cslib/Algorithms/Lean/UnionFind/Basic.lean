/-
Copyright (c) 2026 Juan Bono. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Bono
-/

module

public import Cslib.Init

@[expose] public section

/-!
# Union-Find Data Structure

Functional representation of a union-find (disjoint-set) forest on `n` elements,
with parent pointers and ranks. Used as the substrate for the amortized complexity
analysis with the `TimeM` monad.

## Design

- `parent : Fin n → Fin n` — forest structure (roots have `parent x = x`)
- `rank : Fin n → ℕ` — upper bound on subtree height
- `rankMax` — global upper bound on rank (for termination of `find`)
- `rank_lt` — ranks strictly increase toward the root (implies acyclicity)
- `rank_le_max` — all ranks bounded by `rankMax`
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.UnionFind

variable {n : ℕ}

/-- A union-find forest on `n` elements. -/
structure UF (n : ℕ) where
  /-- Parent pointer: roots satisfy `parent x = x`. -/
  parent : Fin n → Fin n
  /-- Rank: upper bound on subtree height. -/
  rank : Fin n → ℕ
  /-- Global upper bound on all ranks (for termination). -/
  rankMax : ℕ
  /-- Ranks strictly increase along non-trivial parent edges. -/
  rank_lt : ∀ x, parent x ≠ x → rank x < rank (parent x)
  /-- All ranks are bounded by `rankMax`. -/
  rank_le_max : ∀ x, rank x ≤ rankMax

/-- A node is a root when it is its own parent. -/
def UF.isRoot (uf : UF n) (x : Fin n) : Prop := uf.parent x = x

/-- Decidable root check. -/
instance (uf : UF n) (x : Fin n) : Decidable (uf.isRoot x) :=
  inferInstanceAs (Decidable (uf.parent x = x))

/-- The initial union-find: every element is its own root with rank 0. -/
def UF.init (n : ℕ) : UF n where
  parent x := x
  rank _ := 0
  rankMax := 0
  rank_lt _ h := absurd rfl h
  rank_le_max _ := Nat.le_refl 0

@[simp] theorem UF.init_parent (x : Fin n) : (UF.init n).parent x = x := rfl
@[simp] theorem UF.init_rank (x : Fin n) : (UF.init n).rank x = 0 := rfl
@[simp] theorem UF.init_isRoot (x : Fin n) : (UF.init n).isRoot x := rfl

/-- Pure (non-monadic) root computation, for use in specifications.
Follows parent pointers to the root. -/
def UF.rootOf (uf : UF n) (x : Fin n) : Fin n :=
  if h : uf.parent x = x then x
  else uf.rootOf (uf.parent x)
termination_by uf.rankMax - uf.rank x
decreasing_by
  have h1 := uf.rank_lt x h
  have h2 := uf.rank_le_max (uf.parent x)
  omega

theorem UF.rootOf_root (uf : UF n) (x : Fin n) (h : uf.isRoot x) :
    uf.rootOf x = x := by
  unfold rootOf
  simp [isRoot] at *
  simp [h]

theorem UF.rootOf_isRoot (uf : UF n) (x : Fin n) : uf.isRoot (uf.rootOf x) := by
  sorry

/-- Update the parent of node `x` to `r`, preserving invariants.
Precondition: `rank x < rank r`. -/
def UF.setParent (uf : UF n) (x r : Fin n)
    (h_rank : uf.rank x < uf.rank r) : UF n where
  parent y := if y = x then r else uf.parent y
  rank := uf.rank
  rankMax := uf.rankMax
  rank_lt y hy := by
    split_ifs at hy ⊢ with h
    · subst h; exact h_rank
    · exact uf.rank_lt y hy
  rank_le_max := uf.rank_le_max

@[simp] theorem UF.setParent_rank (uf : UF n) (x r : Fin n) (h : uf.rank x < uf.rank r) :
    (uf.setParent x r h).rank = uf.rank := rfl

@[simp] theorem UF.setParent_rankMax (uf : UF n) (x r : Fin n) (h : uf.rank x < uf.rank r) :
    (uf.setParent x r h).rankMax = uf.rankMax := rfl

end Cslib.Algorithms.Lean.UnionFind
