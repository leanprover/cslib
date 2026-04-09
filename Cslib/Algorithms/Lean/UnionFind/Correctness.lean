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

/-- Helper: when one root `ra` is redirected to another root `rb` (which remains a root),
the new `rootOf` maps every node whose old root was `ra` to `rb`, and leaves others unchanged. -/
private theorem rootOf_redirect (uf uf' : UF n) (ra rb : Fin n)
    (ha : uf.isRoot ra) (hb : uf.isRoot rb) (hne : ra ≠ rb)
    (hp : ∀ z, uf'.parent z = if z = ra then rb else uf.parent z)
    (hrk : ∀ z, uf'.rank z ≥ uf.rank z)
    (z : Fin n) :
    uf'.rootOf z = if uf.rootOf z = ra then rb else uf.rootOf z := by
  by_cases hz : uf.parent z = z
  · -- z is a root in uf, so rootOf z = z
    have hrz : uf.rootOf z = z := UF.rootOf_root uf z hz
    by_cases hza : z = ra
    · -- z = ra: parent'(ra) = rb, and rb is a root in uf'
      subst hza
      simp [hrz]
      have hp_z : uf'.parent z = rb := by rw [hp]; simp
      have hb' : uf'.isRoot rb := by
        show uf'.parent rb = rb; rw [hp]; simp [Ne.symm hne]; exact hb
      have h_not_root : uf'.parent z ≠ z := by rw [hp_z]; exact Ne.symm hne
      have : uf'.rootOf z = uf'.rootOf (uf'.parent z) := by
        conv_lhs => unfold UF.rootOf; rw [dif_neg h_not_root]
      rw [this, hp_z, UF.rootOf_root uf' rb hb']
    · -- z ≠ ra: z is still a root in uf'
      have hp_z : uf'.parent z = uf.parent z := by rw [hp]; simp [hza]
      have hz' : uf'.isRoot z := by show uf'.parent z = z; rw [hp_z]; exact hz
      rw [UF.rootOf_root uf' z hz', hrz]; simp [hza]
  · -- z is not a root in uf
    have h_not_root_uf : ¬uf.isRoot z := hz
    have hza : z ≠ ra := fun heq => by subst heq; exact hz ha
    have hp_z : uf'.parent z = uf.parent z := by rw [hp]; simp [hza]
    have hz' : uf'.parent z ≠ z := by rw [hp_z]; exact hz
    have step : uf'.rootOf z = uf'.rootOf (uf.parent z) := by
      conv_lhs => unfold UF.rootOf; rw [dif_neg hz']; rw [hp_z]
    rw [step, rootOf_redirect uf uf' ra rb ha hb hne hp hrk (uf.parent z),
        UF.rootOf_parent uf z h_not_root_uf]
termination_by uf.rankMax - uf.rank z
decreasing_by
  have h1 := uf.rank_lt z hz
  have h2 := uf.rank_le_max (uf.parent z)
  omega

-- Auxiliary lemmas about link's parent function
private theorem link_parent_case1 (uf : UF n) (rx ry : Fin n)
    (hx : uf.isRoot rx) (hy : uf.isRoot ry) (hne : rx ≠ ry)
    (h_lt : uf.rank rx < uf.rank ry) (w : Fin n) :
    (link uf rx ry hx hy hne).parent w = if w = rx then ry else uf.parent w := by
  unfold link; simp [h_lt]

private theorem link_rank_case1 (uf : UF n) (rx ry : Fin n)
    (hx : uf.isRoot rx) (hy : uf.isRoot ry) (hne : rx ≠ ry)
    (h_lt : uf.rank rx < uf.rank ry) (w : Fin n) :
    (link uf rx ry hx hy hne).rank w = uf.rank w := by
  unfold link; simp [h_lt]

private theorem link_parent_case2 (uf : UF n) (rx ry : Fin n)
    (hx : uf.isRoot rx) (hy : uf.isRoot ry) (hne : rx ≠ ry)
    (h_nlt : ¬uf.rank rx < uf.rank ry) (h_lt2 : uf.rank ry < uf.rank rx) (w : Fin n) :
    (link uf rx ry hx hy hne).parent w = if w = ry then rx else uf.parent w := by
  unfold link; simp [h_nlt, h_lt2]

private theorem link_rank_case2 (uf : UF n) (rx ry : Fin n)
    (hx : uf.isRoot rx) (hy : uf.isRoot ry) (hne : rx ≠ ry)
    (h_nlt : ¬uf.rank rx < uf.rank ry) (h_lt2 : uf.rank ry < uf.rank rx) (w : Fin n) :
    (link uf rx ry hx hy hne).rank w = uf.rank w := by
  unfold link; simp [h_nlt, h_lt2]

private theorem link_parent_case3 (uf : UF n) (rx ry : Fin n)
    (hx : uf.isRoot rx) (hy : uf.isRoot ry) (hne : rx ≠ ry)
    (h_nlt : ¬uf.rank rx < uf.rank ry) (h_nlt2 : ¬uf.rank ry < uf.rank rx) (w : Fin n) :
    (link uf rx ry hx hy hne).parent w = if w = ry then rx else uf.parent w := by
  unfold link; simp [h_nlt, h_nlt2]

private theorem link_rank_case3 (uf : UF n) (rx ry : Fin n)
    (hx : uf.isRoot rx) (hy : uf.isRoot ry) (hne : rx ≠ ry)
    (h_nlt : ¬uf.rank rx < uf.rank ry) (h_nlt2 : ¬uf.rank ry < uf.rank rx) (w : Fin n) :
    (link uf rx ry hx hy hne).rank w = if w = rx then uf.rank rx + 1 else uf.rank w := by
  unfold link; simp [h_nlt, h_nlt2]

/-- After linking rx and ry, the root of any node is either the old root
or the new combined root. -/
theorem link_rootOf (uf : UF n) (rx ry : Fin n)
    (hx : uf.isRoot rx) (hy : uf.isRoot ry) (hne : rx ≠ ry) (z : Fin n) :
    (link uf rx ry hx hy hne).rootOf z =
      if uf.rootOf z = rx ∨ uf.rootOf z = ry then
        if uf.rank rx < uf.rank ry then ry
        else rx
      else uf.rootOf z := by
  set uf' := link uf rx ry hx hy hne
  by_cases h_lt : uf.rank rx < uf.rank ry
  · -- Case 1: rank rx < rank ry, rx points to ry
    have hp : ∀ w, uf'.parent w = if w = rx then ry else uf.parent w :=
      link_parent_case1 uf rx ry hx hy hne h_lt
    have hrk : ∀ w, uf'.rank w ≥ uf.rank w := fun w =>
      le_of_eq (link_rank_case1 uf rx ry hx hy hne h_lt w).symm
    rw [rootOf_redirect uf uf' rx ry hx hy hne hp hrk]
    simp only [h_lt, ite_true]
    by_cases h1 : uf.rootOf z = rx
    · simp [h1]
    · by_cases h2 : uf.rootOf z = ry
      · simp [h2]
      · simp [h1, h2]
  · by_cases h_lt2 : uf.rank ry < uf.rank rx
    · -- Case 2: rank ry < rank rx, ry points to rx
      have hp : ∀ w, uf'.parent w = if w = ry then rx else uf.parent w :=
        link_parent_case2 uf rx ry hx hy hne h_lt h_lt2
      have hrk : ∀ w, uf'.rank w ≥ uf.rank w := fun w =>
        le_of_eq (link_rank_case2 uf rx ry hx hy hne h_lt h_lt2 w).symm
      rw [rootOf_redirect uf uf' ry rx hy hx (Ne.symm hne) hp hrk]
      simp only [h_lt, ite_false]
      by_cases h1 : uf.rootOf z = ry
      · simp [h1]
      · by_cases h2 : uf.rootOf z = rx
        · simp [h2]
        · simp [h1, h2]
    · -- Case 3: equal rank, ry points to rx, rank rx incremented
      have hp : ∀ w, uf'.parent w = if w = ry then rx else uf.parent w :=
        link_parent_case3 uf rx ry hx hy hne h_lt h_lt2
      have hrk : ∀ w, uf'.rank w ≥ uf.rank w := by
        intro w; rw [link_rank_case3 uf rx ry hx hy hne h_lt h_lt2]
        by_cases hwx : w = rx
        · subst hwx; simp
        · simp [hwx]
      rw [rootOf_redirect uf uf' ry rx hy hx (Ne.symm hne) hp hrk]
      simp only [h_lt, ite_false]
      by_cases h1 : uf.rootOf z = ry
      · simp [h1]
      · by_cases h2 : uf.rootOf z = rx
        · simp [h2]
        · simp [h1, h2]

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
