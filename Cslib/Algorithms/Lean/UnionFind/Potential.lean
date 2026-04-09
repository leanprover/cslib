/-
Copyright (c) 2026 Juan Bono. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Bono
-/

module

public import Cslib.Algorithms.Lean.UnionFind.Basic
public import Cslib.Algorithms.Lean.UnionFind.Ackermann
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
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
    (hr : 1 ≤ uf.rank x) (hn : uf.rank (uf.parent x) < n) :
    ∃ k, ¬(A k (uf.rank x) ≤ uf.rank (uf.parent x)) := by
  sorry

/-- `level x` = max { k : A k (rank x) ≤ rank (parent x) }.
Defined as `(Nat.find ...) - 1` where Nat.find gives the first k that fails. -/
noncomputable def level (uf : UF n) (x : Fin n) (hx : ¬uf.isRoot x)
    (hr : 1 ≤ uf.rank x) (hn : uf.rank (uf.parent x) < n) : ℕ :=
  Nat.find (exists_level uf x hx hr hn) - 1

/-- Existence of the first i where iterating A_{level} more than i times exceeds
rank (parent x). Used to define `iter` via `Nat.find`. -/
theorem exists_iter (uf : UF n) (x : Fin n) (hx : ¬uf.isRoot x)
    (hr : 1 ≤ uf.rank x) (hn : uf.rank (uf.parent x) < n) :
    ∃ i, ¬(iterFn (A (level uf x hx hr hn)) (i + 1) (uf.rank x) ≤ uf.rank (uf.parent x)) := by
  sorry

/-- `iter x` = max { i ≥ 1 : iterFn (A (level x)) i (rank x) ≤ rank (parent x) }.
Defined via `Nat.find` giving the first i where iteration i+1 fails. -/
noncomputable def iter (uf : UF n) (x : Fin n) (hx : ¬uf.isRoot x)
    (hr : 1 ≤ uf.rank x) (hn : uf.rank (uf.parent x) < n) : ℕ :=
  Nat.find (exists_iter uf x hx hr hn)

/-! ### Bounds on level and iter -/

/-- level(x) < alpha(n) (strictly less than alpha). -/
theorem level_lt_alpha (uf : UF n) (x : Fin n) (hx : ¬uf.isRoot x)
    (hr : 1 ≤ uf.rank x) (hn : uf.rank (uf.parent x) < n) :
    level uf x hx hr hn < alpha n := by
  sorry

/-- 1 ≤ iter(x) (because iteration 1 always succeeds by definition of level). -/
theorem one_le_iter (uf : UF n) (x : Fin n) (hx : ¬uf.isRoot x)
    (hr : 1 ≤ uf.rank x) (hn : uf.rank (uf.parent x) < n) :
    1 ≤ iter uf x hx hr hn := by
  sorry

/-- iter(x) ≤ rank(x). -/
theorem iter_le_rank (uf : UF n) (x : Fin n) (hx : ¬uf.isRoot x)
    (hr : 1 ≤ uf.rank x) (hn : uf.rank (uf.parent x) < n) :
    iter uf x hx hr hn ≤ uf.rank x := by
  sorry

/-! ### Node potential and total potential -/

/-- Node potential. Returns `alpha(n) * rank(x)` for roots/rank-0 nodes,
and `(alpha(n) - level(x)) * rank(x) - iter(x)` otherwise.
Uses `n` (from `UF n`) for `alpha`. -/
noncomputable def phi (uf : UF n) (x : Fin n)
    (hn : ∀ y, uf.rank y < n) : ℕ :=
  if hx : uf.isRoot x then
    alpha n * uf.rank x
  else if hr : uf.rank x = 0 then
    0
  else
    have hr' : 1 ≤ uf.rank x := by omega
    have hn' : uf.rank (uf.parent x) < n := hn (uf.parent x)
    (alpha n - level uf x hx hr' hn') * uf.rank x - iter uf x hx hr' hn'

/-- Total potential over all nodes. -/
noncomputable def Phi (uf : UF n) (hn : ∀ y, uf.rank y < n) : ℕ :=
  ∑ x : Fin n, phi uf x hn

/-! ### Potential properties -/

/-- The ℕ subtraction in `phi` doesn't truncate for valid states. -/
theorem phi_sub_no_truncation (uf : UF n) (x : Fin n)
    (hn : ∀ y, uf.rank y < n) (hx : ¬uf.isRoot x) (hr : 1 ≤ uf.rank x)
    (hn' : uf.rank (uf.parent x) < n) :
    iter uf x hx hr hn' ≤ (alpha n - level uf x hx hr hn') * uf.rank x := by
  sorry

/-- Initial potential is zero (all ranks 0, all roots). -/
theorem Phi_init (hn : ∀ y, (UF.init n).rank y < n) :
    Phi (UF.init n) hn = 0 := by
  sorry

end Cslib.Algorithms.Lean.UnionFind
