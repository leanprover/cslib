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
  unfold rootOf
  split
  · assumption
  · rename_i h
    exact UF.rootOf_isRoot uf (uf.parent x)
termination_by uf.rankMax - uf.rank x
decreasing_by
  have h1 := uf.rank_lt x ‹_›
  have h2 := uf.rank_le_max (uf.parent x)
  omega

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

/-- `rootOf` steps through parents: for a non-root `x`, `rootOf (parent x) = rootOf x`. -/
theorem UF.rootOf_parent (uf : UF n) (x : Fin n) (h : ¬uf.isRoot x) :
    uf.rootOf (uf.parent x) = uf.rootOf x := by
  conv_rhs => unfold rootOf
  simp [UF.isRoot] at h
  simp [h]

/-- `setParent` does not change the parent of nodes other than `x`. -/
@[simp] theorem UF.setParent_parent_ne (uf : UF n) (x r : Fin n) (h : uf.rank x < uf.rank r)
    (y : Fin n) (hyx : y ≠ x) :
    (uf.setParent x r h).parent y = uf.parent y := by
  simp [setParent, hyx]

/-- `setParent x r` sets the parent of `x` to `r`. -/
@[simp] theorem UF.setParent_parent_eq (uf : UF n) (x r : Fin n) (h : uf.rank x < uf.rank r) :
    (uf.setParent x r h).parent x = r := by
  simp [setParent]

/-- If `y` is a root and `y ≠ x`, then `y` is still a root after `setParent x r`. -/
theorem UF.setParent_isRoot_of_ne (uf : UF n) (x r : Fin n) (h : uf.rank x < uf.rank r)
    (y : Fin n) (hy : uf.isRoot y) (hyx : y ≠ x) :
    (uf.setParent x r h).isRoot y := by
  simp [isRoot, setParent, hyx]
  exact hy

/-- If `r` is the root of `x` in `uf`, then `setParent x r` preserves `rootOf` for all nodes. -/
theorem UF.setParent_preserves_rootOf (uf : UF n) (x r : Fin n)
    (h_rank : uf.rank x < uf.rank r)
    (h_root : uf.rootOf x = r) (y : Fin n) :
    (uf.setParent x r h_rank).rootOf y = uf.rootOf y := by
  have h_isRoot : uf.isRoot r := h_root ▸ UF.rootOf_isRoot uf x
  set uf' := uf.setParent x r h_rank with huf'
  have h_ne : x ≠ r := by intro heq; subst heq; omega
  by_cases hyx : y = x
  · rw [hyx]
    have h_px : uf'.parent x = r := by simp [huf', UF.setParent]
    have h_root_r : uf'.isRoot r := by
      rw [UF.isRoot, huf']
      show (if r = x then r else uf.parent r) = r
      rw [if_neg (Ne.symm h_ne)]
      exact h_isRoot
    have h_not_root' : ¬(uf'.parent x = x) := by
      rw [h_px]; exact Ne.symm h_ne
    have step1 : uf'.rootOf x = uf'.rootOf (uf'.parent x) := by
      conv_lhs => unfold UF.rootOf
      rw [dif_neg h_not_root']
    rw [step1, h_px, UF.rootOf_root _ r h_root_r, h_root.symm]
  · have h_par_eq : uf'.parent y = uf.parent y := by
      simp [huf', UF.setParent, hyx]
    by_cases h_par : uf.parent y = y
    · have h_root_new : uf'.isRoot y := by
        rw [UF.isRoot, h_par_eq, h_par]
      rw [UF.rootOf_root _ y h_root_new, UF.rootOf_root _ y h_par]
    · have h_not_root_new : ¬(uf'.parent y = y) := by
        rw [h_par_eq]; exact h_par
      have step_lhs : uf'.rootOf y = uf'.rootOf (uf.parent y) := by
        conv_lhs => unfold UF.rootOf; rw [dif_neg h_not_root_new]
        rw [h_par_eq]
      have step_rhs : uf.rootOf y = uf.rootOf (uf.parent y) := by
        conv_lhs => unfold UF.rootOf; rw [dif_neg h_par]
      rw [step_lhs, step_rhs]
      exact UF.setParent_preserves_rootOf uf x r h_rank h_root (uf.parent y)
termination_by uf.rankMax - uf.rank y
decreasing_by
  have h1 := uf.rank_lt y h_par
  have h2 := uf.rank_le_max (uf.parent y)
  omega

end Cslib.Algorithms.Lean.UnionFind
