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

Proves that `find` and `link` preserve the union-find invariants
and that `find` returns the correct root.

## Main results
- `find_ret_isRoot`: `find` returns a root
- `find_ret_rank_eq`: `find` does not change ranks
- `find_ret_rootOf_eq`: `find` returns `rootOf`
- `find_preserves_roots`: `find` does not change which nodes are roots
- `find_rank_lt_root`: the rank precondition for path compression
- `link_rootOf`: link merges exactly two equivalence classes
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.UnionFind

open Cslib.Algorithms.Lean.TimeM

variable {n : ℕ}

/-! ### find correctness -/

/-- `find` returns a root of the (possibly compressed) UF. -/
theorem find_ret_isRoot (uf : UF n) (x : Fin n) :
    (⟪find uf x⟫.2).isRoot ⟪find uf x⟫.1 := by
  unfold find
  split
  case isTrue h =>
    simp [UF.isRoot, h]
  case isFalse h =>
    simp [UF.isRoot, UF.setParent]
    have ih := find_ret_isRoot uf (uf.parent x)
    simp [UF.isRoot] at ih
    intro _
    exact ih
termination_by uf.rankMax - uf.rank x
decreasing_by
  have h1 := uf.rank_lt x ‹_›
  have h2 := uf.rank_le_max (uf.parent x)
  omega

/-- `find` does not change the rank function. -/
theorem find_ret_rank_eq (uf : UF n) (x : Fin n) :
    (⟪find uf x⟫.2).rank = uf.rank := by
  unfold find
  split
  · simp
  · rename_i h
    simp
    have ih := find_ret_rank_eq uf (uf.parent x)
    simp [ih]
termination_by uf.rankMax - uf.rank x
decreasing_by
  have h1 := uf.rank_lt x ‹_›
  have h2 := uf.rank_le_max (uf.parent x)
  omega

/-- `find` does not change rankMax. -/
theorem find_ret_rankMax_eq (uf : UF n) (x : Fin n) :
    (⟪find uf x⟫.2).rankMax = uf.rankMax := by
  unfold find
  split
  · simp
  · rename_i h
    simp
    have ih := find_ret_rankMax_eq uf (uf.parent x)
    simp [ih]
termination_by uf.rankMax - uf.rank x
decreasing_by
  have h1 := uf.rank_lt x ‹_›
  have h2 := uf.rank_le_max (uf.parent x)
  omega

/-- `find` returns the same root as the pure `rootOf`. -/
theorem find_ret_rootOf_eq (uf : UF n) (x : Fin n) :
    ⟪find uf x⟫.1 = uf.rootOf x := by
  unfold find UF.rootOf
  split
  · simp
  · rename_i h
    simp
    exact find_ret_rootOf_eq uf (uf.parent x)
termination_by uf.rankMax - uf.rank x
decreasing_by
  have h1 := uf.rank_lt x ‹_›
  have h2 := uf.rank_le_max (uf.parent x)
  omega

/-- `find` preserves root status of other nodes. -/
theorem find_preserves_roots (uf : UF n) (x y : Fin n)
    (hy : uf.isRoot y) : (⟪find uf x⟫.2).isRoot y := by
  unfold find
  split
  case isTrue h =>
    simp
    exact hy
  case isFalse h =>
    simp [UF.isRoot, UF.setParent]
    have ih := find_preserves_roots uf (uf.parent x) y hy
    simp [UF.isRoot] at ih hy
    by_cases hyx : y = x
    · subst hyx; exact absurd hy h
    · simp [hyx]; exact ih
termination_by uf.rankMax - uf.rank x
decreasing_by
  have h1 := uf.rank_lt x ‹_›
  have h2 := uf.rank_le_max (uf.parent x)
  omega

/-- The rank precondition for setParent in find: rank of any node on the
path is less than rank of the root. -/
theorem find_rank_lt_root (uf : UF n) (x : Fin n) (hx : ¬uf.isRoot x) :
    uf.rank x < uf.rank (uf.rootOf x) := by
  simp [UF.isRoot] at hx
  unfold UF.rootOf
  simp [hx]
  have h_lt := uf.rank_lt x hx
  by_cases hp : uf.isRoot (uf.parent x)
  · simp [UF.isRoot] at hp
    rw [UF.rootOf_root uf (uf.parent x) hp]
    exact h_lt
  · have ih := find_rank_lt_root uf (uf.parent x) hp
    exact Nat.lt_trans h_lt ih
termination_by uf.rankMax - uf.rank x
decreasing_by
  have := uf.rank_lt x hx
  have := uf.rank_le_max (uf.parent x)
  omega

/-- If `r` is the root of `x` in `uf`, then `setParent x r` preserves `rootOf` for all nodes. -/
private theorem setParent_preserves_rootOf (uf : UF n) (x r : Fin n)
    (h_rank : uf.rank x < uf.rank r)
    (h_root : uf.rootOf x = r) (h_isRoot : uf.isRoot r) (y : Fin n) :
    (uf.setParent x r h_rank).rootOf y = uf.rootOf y := by
  set uf' := uf.setParent x r h_rank with huf'
  have h_ne : x ≠ r := by intro heq; subst heq; omega
  by_cases hyx : y = x
  · -- y = x: rootOf x in uf' should be r (since uf'.parent x = r and r is root)
    rw [hyx]
    -- In uf', parent x = r and r is a root
    have h_px : uf'.parent x = r := by simp [huf', UF.setParent]
    have h_root_r : uf'.isRoot r := by
      rw [UF.isRoot, huf']
      show (if r = x then r else uf.parent r) = r
      rw [if_neg (Ne.symm h_ne)]
      exact h_isRoot
    have h_not_root : ¬uf'.isRoot x := by
      rw [UF.isRoot, h_px]
      exact Ne.symm h_ne
    have h_not_root' : ¬(uf'.parent x = x) := h_not_root
    have step1 : uf'.rootOf x = uf'.rootOf (uf'.parent x) := by
      conv_lhs => unfold UF.rootOf
      rw [dif_neg h_not_root']
    rw [step1, h_px, UF.rootOf_root _ r h_root_r, h_root.symm]
  · -- y ≠ x: parent y unchanged
    have h_par_eq : uf'.parent y = uf.parent y := by
      simp [huf', UF.setParent, hyx]
    by_cases h_par : uf.parent y = y
    · -- y is root in both
      have h_root_new : uf'.isRoot y := by
        rw [UF.isRoot, h_par_eq, h_par]
      rw [UF.rootOf_root _ y h_root_new, UF.rootOf_root _ y h_par]
    · -- y is not root. Recurse on parent y.
      have h_not_root_new : ¬(uf'.parent y = y) := by
        rw [h_par_eq]; exact h_par
      have step_lhs : uf'.rootOf y = uf'.rootOf (uf.parent y) := by
        conv_lhs => unfold UF.rootOf; rw [dif_neg h_not_root_new]
        rw [h_par_eq]
      have step_rhs : uf.rootOf y = uf.rootOf (uf.parent y) := by
        conv_lhs => unfold UF.rootOf; rw [dif_neg h_par]
      rw [step_lhs, step_rhs]
      exact setParent_preserves_rootOf uf x r h_rank h_root h_isRoot (uf.parent y)
termination_by uf.rankMax - uf.rank y
decreasing_by
  have h1 := uf.rank_lt y h_par
  have h2 := uf.rank_le_max (uf.parent y)
  omega

/-- `find` preserves `rootOf` for all nodes. -/
theorem find_preserves_rootOf (uf : UF n) (x y : Fin n) :
    (⟪find uf x⟫.2).rootOf y = uf.rootOf y := by
  unfold find
  split
  case isTrue h => simp
  case isFalse h =>
    simp only [bind, TimeM.bind, Bind.bind, ret_pure]
    -- Goal is about (uf_rec.setParent x root _).rootOf y = uf.rootOf y
    -- where uf_rec = ⟪find uf (parent x)⟫.2, root = ⟪find uf (parent x)⟫.1
    -- By IH: uf_rec.rootOf y = uf.rootOf y
    -- By helper: setParent preserves rootOf when root is rootOf x in uf_rec
    have ih_y : (⟪find uf (uf.parent x)⟫.2).rootOf y = uf.rootOf y :=
      find_preserves_rootOf uf (uf.parent x) y
    have ih_root : ⟪find uf (uf.parent x)⟫.1 = uf.rootOf (uf.parent x) :=
      find_ret_rootOf_eq uf (uf.parent x)
    have ih_isRoot : (⟪find uf (uf.parent x)⟫.2).isRoot ⟪find uf (uf.parent x)⟫.1 :=
      find_ret_isRoot uf (uf.parent x)
    have h_rootOf_step : uf.rootOf x = uf.rootOf (uf.parent x) := by
      conv_lhs => rw [UF.rootOf]; simp [h]
    have h_root_in_rec : (⟪find uf (uf.parent x)⟫.2).rootOf x = ⟪find uf (uf.parent x)⟫.1 := by
      rw [find_preserves_rootOf uf (uf.parent x) x, h_rootOf_step, ih_root]
    rw [setParent_preserves_rootOf _ x _ _ h_root_in_rec ih_isRoot y, ih_y]
termination_by (uf.rankMax - uf.rank x, 0)
decreasing_by
  all_goals (apply Prod.Lex.left; have h1 := uf.rank_lt x ‹_›; have h2 := uf.rank_le_max (uf.parent x); omega)

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
