/-
Copyright (c) 2026 Juan Bono. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Bono
-/

module

public import Cslib.Algorithms.Lean.UnionFind.Basic
public import Cslib.Algorithms.Lean.UnionFind.Ackermann
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Basic

@[expose] public section

/-!
# Potential Function for Union-Find Amortized Analysis

Defines the potential function Φ used in the CLRS amortized analysis.
For each non-root node x with rank ≥ 1:
- `level x` = max { k : A k (rank x) ≤ rank (parent x) }
- `iter x` = max { i ≥ 1 : A_{level x}^{(i)}(rank x) ≤ rank (parent x) }

The node potential is:
- `phi x = alpha(n) * rank(x)` if x is root or rank(x) = 0
- `phi x = (alpha(n) - level(x)) * rank(x) - iter(x)` otherwise

## References
- [CLRS] Chapter 19, Lemmas 19.10–19.14
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.UnionFind

variable {n : ℕ}

/-! ### level and iter -/

/-- Existence of the first k where A k (rank x) > rank (parent x).
Used to define `level` via `Nat.find`. -/
theorem exists_level (uf : UF n) (x : Fin n) (hx : ¬uf.isRoot x)
    (hr : 1 ≤ uf.rank x) :
    ∃ k, ¬(A k (uf.rank x) ≤ uf.rank (uf.parent x)) := by
  use uf.rank (uf.parent x)
  have h1 : uf.rank (uf.parent x) + 2 ≤ A (uf.rank (uf.parent x)) 1 := A_one_ge _
  have h2 : A (uf.rank (uf.parent x)) 1 ≤ A (uf.rank (uf.parent x)) (uf.rank x) :=
    (A_strictMono_right _).monotone hr
  omega

/-- `level x` = max { k : A k (rank x) ≤ rank (parent x) }.
Defined as `(Nat.find ...) - 1` where Nat.find gives the first k that fails. -/
noncomputable def level (uf : UF n) (x : Fin n) (hx : ¬uf.isRoot x)
    (hr : 1 ≤ uf.rank x) : ℕ :=
  Nat.find (exists_level uf x hx hr) - 1

/-- Existence of the first i where iterating A_{level} more than i times exceeds
rank (parent x). Used to define `iter` via `Nat.find`. -/
theorem exists_iter (uf : UF n) (x : Fin n) (hx : ¬uf.isRoot x)
    (hr : 1 ≤ uf.rank x) :
    ∃ i, ¬(iterFn (A (level uf x hx hr)) (i + 1) (uf.rank x) ≤ uf.rank (uf.parent x)) := by
  -- We show that Nat.find(exists_level) ≥ 1, so level + 1 = Nat.find(exists_level)
  set F := Nat.find (exists_level uf x hx hr) with hF_def
  -- First show F ≥ 1: F = 0 would mean A 0 (rank x) > rank (parent x), i.e. rank x + 1 > rank (parent x)
  -- But rank_lt gives rank x < rank (parent x), so rank x + 1 ≤ rank (parent x). Contradiction.
  have hF_pos : 0 < F := by
    rw [Nat.pos_iff_ne_zero, Ne, Nat.find_eq_zero]
    push Not
    have := uf.rank_lt x (by rwa [UF.isRoot] at hx)
    simp [A_zero]
    omega
  -- So level = F - 1 and F = level + 1
  have hlevel : level uf x hx hr = F - 1 := rfl
  have hF_eq : F = level uf x hx hr + 1 := by omega
  -- Nat.find_spec gives: ¬(A F (rank x) ≤ rank (parent x))
  have hspec := Nat.find_spec (exists_level uf x hx hr)
  -- Rewrite Nat.find to F, then to level + 1
  rw [← hF_def] at hspec
  rw [hF_eq] at hspec
  rw [A_succ] at hspec
  -- Take i = rank x
  exact ⟨uf.rank x, hspec⟩

/-- `iter x` = max { i ≥ 1 : iterFn (A (level x)) i (rank x) ≤ rank (parent x) }.
Defined via `Nat.find` giving the first i where iteration i+1 fails. -/
noncomputable def iter (uf : UF n) (x : Fin n) (hx : ¬uf.isRoot x)
    (hr : 1 ≤ uf.rank x) : ℕ :=
  Nat.find (exists_iter uf x hx hr)

/-! ### Bounds on level and iter -/

/-- level(x) < alpha(n) (strictly less than alpha). -/
theorem level_lt_alpha (uf : UF n) (x : Fin n) (hx : ¬uf.isRoot x)
    (hr : 1 ≤ uf.rank x) (hn : uf.rank (uf.parent x) < n) :
    level uf x hx hr < alpha n := by
  -- level = Nat.find(exists_level) - 1. We need Nat.find - 1 < alpha n.
  -- Suffices: Nat.find ≤ alpha n.
  -- By Nat.find_min' (= find_le), it suffices to show alpha n satisfies the predicate,
  -- i.e., ¬(A (alpha n) (rank x) ≤ rank (parent x)).
  -- We have: A (alpha n) (rank x) ≥ A (alpha n) 1 ≥ n > rank (parent x).
  unfold level
  set F := Nat.find (exists_level uf x hx hr) with hF_def
  -- Need: F - 1 < alpha n, i.e., F ≤ alpha n (since alpha n ≥ 1 as shown below)
  have hF_le : F ≤ alpha n := by
    rw [hF_def]
    apply Nat.find_min'
    -- Goal: ¬(A (alpha n) (rank x) ≤ rank (parent x))
    intro hle
    have h1 : n ≤ A (alpha n) 1 := A_alpha_ge n
    have h2 : A (alpha n) 1 ≤ A (alpha n) (uf.rank x) :=
      (A_strictMono_right _).monotone hr
    exact Nat.not_lt.mpr (le_trans (le_trans h1 h2) hle) hn
  -- Now show alpha n ≥ 1 so that F - 1 < alpha n
  have hrank_parent : 2 ≤ uf.rank (uf.parent x) := by
    have := uf.rank_lt x (by rwa [UF.isRoot] at hx); omega
  have hn3 : 3 ≤ n := by omega
  have halpha_pos : 1 ≤ alpha n := by
    -- alpha n ≥ 1 because A 0 1 = 2 < 3 ≤ n, so alpha n > 0
    by_contra h'
    push Not at h'
    have halpha0 : alpha n = 0 := by omega
    have h0 := A_alpha_ge n
    rw [halpha0, A_zero] at h0
    omega
  -- F ≥ 1 (same argument as in exists_iter)
  have hF_pos : 0 < F := by
    rw [hF_def, Nat.find_pos]
    have := uf.rank_lt x (by rwa [UF.isRoot] at hx)
    simp [A_zero]; omega
  -- F ≤ alpha n and F ≥ 1 imply F - 1 < alpha n
  exact Nat.lt_of_lt_of_le (Nat.sub_one_lt (by omega)) hF_le

/-- 1 ≤ iter(x) (because iteration 1 always succeeds by definition of level). -/
theorem one_le_iter (uf : UF n) (x : Fin n) (hx : ¬uf.isRoot x)
    (hr : 1 ≤ uf.rank x) :
    1 ≤ iter uf x hx hr := by
  -- iter = Nat.find(exists_iter). We need Nat.find ≥ 1, i.e., ¬P(0).
  -- P(0) is ¬(iterFn (A level) 1 (rank x) ≤ rank (parent x))
  -- But iterFn (A level) 1 (rank x) = A level (rank x)
  -- And by Nat.find_min for exists_level, A level (rank x) ≤ rank (parent x)
  unfold iter
  suffices h : 0 < Nat.find (exists_iter uf x hx hr) by omega
  rw [Nat.find_pos]
  -- Goal: ¬¬(iterFn (A (level ..)) 1 (rank x) ≤ rank (parent x))
  simp only [iterFn_succ, iterFn_zero, not_not]
  -- Goal: A (level ..) (rank x) ≤ rank (parent x)
  -- By definition, level = Nat.find(exists_level) - 1
  -- Nat.find_min says: for m < Nat.find, ¬¬(A m (rank x) ≤ rank (parent x))
  set F := Nat.find (exists_level uf x hx hr) with hF_def
  have hF_pos : 0 < F := by
    rw [Nat.find_pos]
    have := uf.rank_lt x (by rwa [UF.isRoot] at hx)
    simp [A_zero]; omega
  have hlt : F - 1 < F := Nat.sub_one_lt (by omega)
  have := Nat.find_min (exists_level uf x hx hr) hlt
  push Not at this
  convert this using 2

/-- iter(x) ≤ rank(x). -/
theorem iter_le_rank (uf : UF n) (x : Fin n) (hx : ¬uf.isRoot x)
    (hr : 1 ≤ uf.rank x) :
    iter uf x hx hr ≤ uf.rank x := by
  -- iter = Nat.find(exists_iter). By Nat.find_le (= find_min'), if rank x satisfies
  -- the predicate, then Nat.find ≤ rank x.
  -- The predicate at i = rank x: ¬(iterFn (A level) (rank x + 1) (rank x) ≤ rank (parent x))
  -- This was shown in exists_iter: A (level + 1) (rank x) = iterFn (A level) (rank x + 1) (rank x)
  -- and this exceeds rank (parent x).
  unfold iter
  apply Nat.find_le
  -- Goal: ¬(iterFn (A level) (rank x + 1) (rank x) ≤ rank (parent x))
  set F := Nat.find (exists_level uf x hx hr) with hF_def
  have hF_pos : 0 < F := by
    rw [Nat.find_pos]
    have := uf.rank_lt x (by rwa [UF.isRoot] at hx)
    simp [A_zero]; omega
  have hF_eq : F = level uf x hx hr + 1 := by
    unfold level; omega
  have hspec := Nat.find_spec (exists_level uf x hx hr)
  rw [← hF_def, hF_eq, A_succ] at hspec
  exact hspec

/-! ### Node potential and total potential -/

/-- Node potential. Returns `alpha(n) * rank(x)` for roots/rank-0 nodes,
and `(alpha(n) - level(x)) * rank(x) - iter(x)` otherwise.
Uses `n` (from `UF n`) for `alpha`. -/
noncomputable def phi (uf : UF n) (x : Fin n) : ℕ :=
  if hx : uf.isRoot x then
    alpha n * uf.rank x
  else if hr : uf.rank x = 0 then
    0
  else
    have hr' : 1 ≤ uf.rank x := by omega
    (alpha n - level uf x hx hr') * uf.rank x - iter uf x hx hr'

/-- Total potential over all nodes. -/
noncomputable def Phi (uf : UF n) : ℕ :=
  ∑ x : Fin n, phi uf x

/-! ### Potential properties -/

/-- The ℕ subtraction in `phi` doesn't truncate for valid states. -/
theorem phi_sub_no_truncation (uf : UF n) (x : Fin n)
    (hx : ¬uf.isRoot x) (hr : 1 ≤ uf.rank x)
    (hn : uf.rank (uf.parent x) < n) :
    iter uf x hx hr ≤ (alpha n - level uf x hx hr) * uf.rank x := by
  -- iter ≤ rank x (by iter_le_rank)
  -- level < alpha n (by level_lt_alpha), so alpha n - level ≥ 1
  -- Therefore (alpha n - level) * rank x ≥ 1 * rank x = rank x ≥ iter
  have h_iter := iter_le_rank uf x hx hr
  have h_level := level_lt_alpha uf x hx hr hn
  have h_diff : 1 ≤ alpha n - level uf x hx hr := by omega
  calc iter uf x hx hr
      ≤ uf.rank x := h_iter
    _ = 1 * uf.rank x := (Nat.one_mul _).symm
    _ ≤ (alpha n - level uf x hx hr) * uf.rank x :=
        Nat.mul_le_mul_right _ h_diff

/-- Initial potential is zero (all ranks 0, all roots). -/
theorem Phi_init : Phi (UF.init n) = 0 := by
  unfold Phi
  apply Finset.sum_eq_zero
  intro x _
  -- phi (init n) x = alpha n * rank x = alpha n * 0 = 0 (since init n is all roots)
  simp [phi, UF.init_isRoot, UF.init_rank]

end Cslib.Algorithms.Lean.UnionFind
