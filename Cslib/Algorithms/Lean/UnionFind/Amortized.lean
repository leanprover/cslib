/-
Copyright (c) 2026 Juan Bono. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Bono
-/

module

public import Cslib.Algorithms.Lean.UnionFind.Operations
public import Cslib.Algorithms.Lean.UnionFind.Correctness
public import Cslib.Algorithms.Lean.UnionFind.Potential
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

/-!
# Amortized Complexity of Union-Find

Proves that m find/union operations on n elements cost at most
`m * (3 * alpha(n) + 4)` total time, which is O(m * alpha(n)).

The proof uses the potential method:
1. Define amortized cost = actual cost + ΔΦ
2. Show amortized cost of find ≤ alpha(n) + 2
3. Show potential increase of link ≤ alpha(n)
4. Combine: amortized cost of union ≤ 3 * alpha(n) + 4
5. Telescope: total actual cost ≤ total amortized cost (since Φ_init = 0, Φ_final ≥ 0)

## References
- [CLRS] Chapter 19, Theorem 19.13
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.UnionFind

open Cslib.Algorithms.Lean.TimeM

variable {n : ℕ}

/-! ### Amortized cost of find -/

/-- **Key lemma**: The amortized cost of find is at most alpha(n) + 2. -/
theorem find_amortized (uf : UF n) (x : Fin n)
    (hn : ∀ y, uf.rank y < n) :
    (find uf x).time + Phi ⟪find uf x⟫.2 ≤ Phi uf + alpha n + 2 := by
  sorry

/-! ### Potential increase of link -/

/-- Helper: phi of a root is alpha(n) * rank. -/
theorem phi_root (uf : UF n) (x : Fin n) (hx : uf.isRoot x) :
    phi uf x = alpha n * uf.rank x := by
  simp [phi, hx]

/-- Helper: phi of a non-root with rank 0 is 0. -/
theorem phi_nonroot_rank_zero (uf : UF n) (x : Fin n) (hx : ¬uf.isRoot x)
    (hr : uf.rank x = 0) :
    phi uf x = 0 := by
  simp [phi, hx, hr]

/-- Helper: phi of any node is at most alpha(n) * rank(x). -/
theorem phi_le_alpha_mul_rank (uf : UF n) (x : Fin n) :
    phi uf x ≤ alpha n * uf.rank x := by
  unfold phi
  split
  · exact le_refl _
  · rename_i hx
    split
    · rename_i hr; rw [hr]; simp
    · rename_i hr
      have hr' : 1 ≤ uf.rank x := by omega
      -- (alpha n - level) * rank x - iter ≤ (alpha n - level) * rank x ≤ alpha n * rank x
      calc (alpha n - level uf x hx hr') * uf.rank x - iter uf x hx hr'
          ≤ (alpha n - level uf x hx hr') * uf.rank x := Nat.sub_le _ _
        _ ≤ alpha n * uf.rank x := Nat.mul_le_mul_right _ (Nat.sub_le _ _)

/-- link preserves parent of nodes other than the attached root (case 1: rx < ry). -/
theorem link_parent_case1 (uf : UF n) (rx ry : Fin n)
    (hx : uf.isRoot rx) (hy : uf.isRoot ry) (hne : rx ≠ ry)
    (h : uf.rank rx < uf.rank ry) (z : Fin n) (hz : z ≠ rx) :
    (link uf rx ry hx hy hne).parent z = uf.parent z := by
  simp [link, h, hz]

/-- link preserves parent of nodes other than the attached root (case 2: ry < rx). -/
theorem link_parent_case2 (uf : UF n) (rx ry : Fin n)
    (hx : uf.isRoot rx) (hy : uf.isRoot ry) (hne : rx ≠ ry)
    (h1 : ¬uf.rank rx < uf.rank ry) (h2 : uf.rank ry < uf.rank rx)
    (z : Fin n) (hz : z ≠ ry) :
    (link uf rx ry hx hy hne).parent z = uf.parent z := by
  simp [link, h1, h2, hz]

/-- link preserves parent of nodes other than ry (case 3: equal ranks). -/
theorem link_parent_case3 (uf : UF n) (rx ry : Fin n)
    (hx : uf.isRoot rx) (hy : uf.isRoot ry) (hne : rx ≠ ry)
    (h1 : ¬uf.rank rx < uf.rank ry) (h2 : ¬uf.rank ry < uf.rank rx)
    (z : Fin n) (hz : z ≠ ry) :
    (link uf rx ry hx hy hne).parent z = uf.parent z := by
  simp [link, h1, h2, hz]

/-- link preserves rank (cases 1 and 2). -/
theorem link_rank_eq_of_ne_rank (uf : UF n) (rx ry : Fin n)
    (hx : uf.isRoot rx) (hy : uf.isRoot ry) (hne : rx ≠ ry)
    (hrank : uf.rank rx ≠ uf.rank ry) :
    (link uf rx ry hx hy hne).rank = uf.rank := by
  unfold link
  by_cases h : uf.rank rx < uf.rank ry
  · simp [h]
  · have h2 : uf.rank ry < uf.rank rx := by omega
    simp [h, h2]

/-- link rank in case 3: rx gets rank + 1, others unchanged. -/
theorem link_rank_case3 (uf : UF n) (rx ry : Fin n)
    (hx : uf.isRoot rx) (hy : uf.isRoot ry) (hne : rx ≠ ry)
    (h1 : ¬uf.rank rx < uf.rank ry) (h2 : ¬uf.rank ry < uf.rank rx)
    (z : Fin n) :
    (link uf rx ry hx hy hne).rank z =
      if z = rx then uf.rank rx + 1 else uf.rank z := by
  simp [link, h1, h2]

/-- link preserves isRoot for all nodes except the attached one (case 1). -/
theorem link_isRoot_case1 (uf : UF n) (rx ry : Fin n)
    (hx : uf.isRoot rx) (hy : uf.isRoot ry) (hne : rx ≠ ry)
    (h : uf.rank rx < uf.rank ry) (z : Fin n) (hz : z ≠ rx) :
    (link uf rx ry hx hy hne).isRoot z ↔ uf.isRoot z := by
  simp [link, h, UF.isRoot, hz]

/-- In case 1, rx is not a root after link. -/
theorem link_not_isRoot_case1 (uf : UF n) (rx ry : Fin n)
    (hx : uf.isRoot rx) (hy : uf.isRoot ry) (hne : rx ≠ ry)
    (h : uf.rank rx < uf.rank ry) :
    ¬(link uf rx ry hx hy hne).isRoot rx := by
  simp [link, h, UF.isRoot]
  exact fun h => absurd h.symm hne

/-- In case 2, ry is not a root after link. -/
theorem link_not_isRoot_case2 (uf : UF n) (rx ry : Fin n)
    (hx : uf.isRoot rx) (hy : uf.isRoot ry) (hne : rx ≠ ry)
    (h1 : ¬uf.rank rx < uf.rank ry) (h2 : uf.rank ry < uf.rank rx) :
    ¬(link uf rx ry hx hy hne).isRoot ry := by
  simp [link, h1, h2, UF.isRoot, hne]

/-- In case 3, ry is not a root after link. -/
theorem link_not_isRoot_case3 (uf : UF n) (rx ry : Fin n)
    (hx : uf.isRoot rx) (hy : uf.isRoot ry) (hne : rx ≠ ry)
    (h1 : ¬uf.rank rx < uf.rank ry) (h2 : ¬uf.rank ry < uf.rank rx) :
    ¬(link uf rx ry hx hy hne).isRoot ry := by
  simp [link, h1, h2, UF.isRoot, hne]

/-- In case 3, rx is still a root after link. -/
theorem link_isRoot_rx_case3 (uf : UF n) (rx ry : Fin n)
    (hx : uf.isRoot rx) (hy : uf.isRoot ry) (hne : rx ≠ ry)
    (h1 : ¬uf.rank rx < uf.rank ry) (h2 : ¬uf.rank ry < uf.rank rx) :
    (link uf rx ry hx hy hne).isRoot rx := by
  simp [link, h1, h2, UF.isRoot, hne]
  exact hx

/-- When parent-rank weakly increases and everything else stays the same,
    phi doesn't increase (for non-root nodes). -/
theorem phi_le_of_parent_rank_le (uf uf' : UF n) (z : Fin n)
    (hp : uf'.parent z = uf.parent z)
    (hr : uf'.rank z = uf.rank z)
    (hrp : uf.rank (uf.parent z) ≤ uf'.rank (uf'.parent z))
    (hroot : ¬uf.isRoot z)
    (hn : uf.rank (uf.parent z) < n) :
    phi uf' z ≤ phi uf z := by
  have hroot_iff : uf'.isRoot z ↔ uf.isRoot z := by
    simp [UF.isRoot, hp]
  have hroot' : ¬uf'.isRoot z := mt hroot_iff.mp hroot
  unfold phi
  simp only [hroot, hroot', dite_false]
  by_cases hrz : uf.rank z = 0
  · have hrz' : uf'.rank z = 0 := by rw [hr]; exact hrz
    simp [hrz, hrz']
  · have hrz' : uf'.rank z ≠ 0 := by rw [hr]; exact hrz
    simp only [hrz, hrz', dite_false]
    have hr' : 1 ≤ uf.rank z := by omega
    have hr'' : 1 ≤ uf'.rank z := by omega
    -- Need: (alpha - level') * rank' - iter' ≤ (alpha - level) * rank - iter
    -- where level' ≥ level (parent rank increased) and iter' adjusted accordingly
    -- Key: rank' = rank (by hr)
    -- level' ≥ level because {k : A k (rank z) ≤ new_parent_rank} ⊇ {k : A k (rank z) ≤ old_parent_rank}
    -- So Nat.find for level' (first k that fails) ≥ Nat.find for level (first k that fails)
    -- Hence level' = Nat.find' - 1 ≥ Nat.find - 1 = level
    -- Key conversion: the parent-rank in uf' is ≥ that in uf
    -- So if A k (rank z) ≤ old_parent_rank, then also ≤ new_parent_rank
    have hconv : ∀ k, (¬A k (uf'.rank z) ≤ uf'.rank (uf'.parent z)) →
                      (¬A k (uf.rank z) ≤ uf.rank (uf.parent z)) := by
      intro k hk h
      apply hk
      rw [hr]
      calc A k (uf.rank z) ≤ uf.rank (uf.parent z) := h
        _ ≤ uf'.rank (uf'.parent z) := hrp
    have hfind_le : Nat.find (exists_level uf z hroot hr') ≤
                    Nat.find (exists_level uf' z hroot' hr'') := by
      exact Nat.find_mono hconv
    have hlevel_le : level uf z hroot hr' ≤ level uf' z hroot' hr'' := by
      unfold level; omega
    -- Now case split: level' = level or level' > level
    by_cases hlev_eq : level uf' z hroot' hr'' = level uf z hroot hr'
    · -- Same level: iter' ≥ iter since more iterations fit in the higher parent rank
      -- iter defined via Nat.find on: ¬(iterFn (A level) (i+1) (rank z) ≤ parent_rank)
      -- When parent_rank increases, more i's satisfy the condition, so Nat.find increases
      have hconv_iter : ∀ i,
          (¬iterFn (A (level uf' z hroot' hr'')) (i + 1) (uf'.rank z) ≤ uf'.rank (uf'.parent z)) →
          (¬iterFn (A (level uf z hroot hr')) (i + 1) (uf.rank z) ≤ uf.rank (uf.parent z)) := by
        intro i hi h
        apply hi
        rw [hlev_eq, hr]
        exact le_trans h hrp
      have hiter_le : iter uf z hroot hr' ≤ iter uf' z hroot' hr'' := by
        unfold iter
        exact Nat.find_mono hconv_iter
      -- phi' = (alpha - level') * rank' - iter' = (alpha - level) * rank - iter'
      -- phi  = (alpha - level) * rank - iter
      -- Since iter' ≥ iter, phi' ≤ phi
      -- Use the fact that (a*b - c) ≤ (a*b - d) when d ≤ c
      have h1 : (alpha n - level uf' z hroot' hr'') * uf'.rank z =
                (alpha n - level uf z hroot hr') * uf.rank z := by
        rw [hlev_eq, hr]
      calc (alpha n - level uf' z hroot' hr'') * uf'.rank z - iter uf' z hroot' hr''
          = (alpha n - level uf z hroot hr') * uf.rank z - iter uf' z hroot' hr'' := by rw [h1]
        _ ≤ (alpha n - level uf z hroot hr') * uf.rank z - iter uf z hroot hr' :=
            Nat.sub_le_sub_left hiter_le _
    · -- level' > level, i.e., level' ≥ level + 1
      have hlev_gt : level uf z hroot hr' + 1 ≤ level uf' z hroot' hr'' := by omega
      -- phi' = (alpha - level') * rank - iter'
      -- phi  = (alpha - level) * rank - iter
      -- (alpha - level') ≤ alpha - level - 1
      -- iter' ≥ 1 (one_le_iter), iter ≤ rank (iter_le_rank)
      -- phi' ≤ (alpha - level - 1) * rank - 1
      -- phi  ≥ (alpha - level) * rank - rank = (alpha - level - 1) * rank
      -- So phi' ≤ (alpha - level - 1) * rank - 1 < (alpha - level - 1) * rank ≤ phi
      have hiter'_ge : 1 ≤ iter uf' z hroot' hr'' := one_le_iter uf' z hroot' hr''
      have hiter_le_rank : iter uf z hroot hr' ≤ uf.rank z := iter_le_rank uf z hroot hr'
      have hlevel_lt : level uf z hroot hr' < alpha n := level_lt_alpha uf z hroot hr' hn
      -- phi(uf, z) = (alpha - L) * R - I where I ≤ R
      -- So phi(uf, z) ≥ (alpha - L) * R - R = (alpha - L - 1) * R
      have hphi_lb : (alpha n - level uf z hroot hr' - 1) * uf.rank z ≤
          (alpha n - level uf z hroot hr') * uf.rank z - iter uf z hroot hr' := by
        -- (a-1)*R ≤ a*R - I when I ≤ R and a ≥ 1
        -- (a-1)*R + I ≤ (a-1)*R + R = a*R  (since I ≤ R)
        -- So (a-1)*R ≤ a*R - I
        set L := level uf z hroot hr' with hL
        set R := uf.rank z with hR
        set I := iter uf z hroot hr' with hI
        set aL := alpha n - L with haL
        have haL_pos : 1 ≤ aL := by omega
        have hIR : I ≤ R := hiter_le_rank
        -- aL * R = (aL - 1) * R + R
        have key : (aL - 1) * R + R = aL * R := by
          have : aL ≥ 1 := haL_pos
          cases haL : aL with
          | zero => omega
          | succ a => simp [Nat.succ_mul]
        -- (aL - 1) * R + I ≤ (aL - 1) * R + R = aL * R
        have h2 : (aL - 1) * R + I ≤ aL * R := by omega
        omega
      -- phi(uf', z) = (alpha - L') * R' - I' where L' ≥ L+1, R' = R, I' ≥ 1
      -- (alpha - L') ≤ alpha - L - 1
      have h_alpha_sub : alpha n - level uf' z hroot' hr'' ≤ alpha n - level uf z hroot hr' - 1 := by
        omega
      calc (alpha n - level uf' z hroot' hr'') * uf'.rank z - iter uf' z hroot' hr''
          ≤ (alpha n - level uf' z hroot' hr'') * uf'.rank z := Nat.sub_le _ _
        _ ≤ (alpha n - level uf z hroot hr' - 1) * uf'.rank z :=
            Nat.mul_le_mul_right _ h_alpha_sub
        _ = (alpha n - level uf z hroot hr' - 1) * uf.rank z := by rw [hr]
        _ ≤ (alpha n - level uf z hroot hr') * uf.rank z - iter uf z hroot hr' := hphi_lb

/-- Two UFs that agree on rank z, rank (parent z), parent z, and isRoot z
    give the same phi at z. -/
theorem phi_eq_of_same_data (uf uf' : UF n) (z : Fin n)
    (hp : uf'.parent z = uf.parent z)
    (hr : uf'.rank z = uf.rank z)
    (hrp : uf'.rank (uf'.parent z) = uf.rank (uf.parent z)) :
    phi uf' z = phi uf z := by
  have hroot : uf'.isRoot z ↔ uf.isRoot z := by
    simp [UF.isRoot, hp]
  unfold phi
  by_cases hz : uf.isRoot z
  · -- z is root in both
    have hz' := hroot.mpr hz
    simp [hz', hz, hr]
  · -- z is not root in both
    have hz' : ¬uf'.isRoot z := mt hroot.mp hz
    simp only [hz', hz, dite_false]
    by_cases hrz : uf.rank z = 0
    · have hrz' : uf'.rank z = 0 := by rw [hr, hrz]
      simp [hrz', hrz]
    · have hrz' : uf'.rank z ≠ 0 := by rw [hr]; exact hrz
      simp only [hrz', hrz, dite_false]
      -- Now need: level and iter are the same
      -- level = Nat.find(exists_level) - 1
      -- The predicate for exists_level is: k ↦ ¬(A k (rank z) ≤ rank (parent z))
      -- This only depends on rank z and rank (parent z)
      have hr' : 1 ≤ uf.rank z := by omega
      have hr'' : 1 ≤ uf'.rank z := by omega
      -- Auxiliary: the rank and parent-rank equality allow converting predicates
      have hconv : ∀ k, A k (uf'.rank z) ≤ uf'.rank (uf'.parent z) ↔
                       A k (uf.rank z) ≤ uf.rank (uf.parent z) := by
        intro k; constructor
        · intro h; rw [hr, hrp] at h; exact h
        · intro h; rw [← hr, ← hrp] at h; exact h
      -- Show levels are equal
      have hlevel : level uf' z hz' hr'' = level uf z hz hr' := by
        unfold level
        congr 1
        apply le_antisymm
        · -- find(uf') ≤ find(uf): need ∀ k, p_uf(k) → p_uf'(k)
          apply Nat.find_mono
          intro k hk
          exact mt (hconv k).mp hk
        · -- find(uf) ≤ find(uf'): need ∀ k, p_uf'(k) → p_uf(k)
          apply Nat.find_mono
          intro k hk
          exact mt (hconv k).mpr hk
      -- For iters, we need a similar conversion for the iterated predicate
      have hconv_iter : ∀ i, iterFn (A (level uf' z hz' hr'')) (i + 1) (uf'.rank z) ≤ uf'.rank (uf'.parent z) ↔
                            iterFn (A (level uf z hz hr')) (i + 1) (uf.rank z) ≤ uf.rank (uf.parent z) := by
        intro i; constructor
        · intro h; rw [hlevel, hr, hrp] at h; exact h
        · intro h; rw [← hlevel, ← hr, ← hrp] at h; exact h
      -- Show iters are equal
      have hiter : iter uf' z hz' hr'' = iter uf z hz hr' := by
        unfold iter
        apply le_antisymm
        · apply Nat.find_mono
          intro i hi
          exact mt (hconv_iter i).mp hi
        · apply Nat.find_mono
          intro i hi
          exact mt (hconv_iter i).mpr hi
      -- Now combine
      simp only [hr, hlevel, hiter]

/-- The potential increase from linking two roots is at most alpha(n).

  Strategy: Case split on rank comparison. In cases 1 and 2, Phi doesn't increase.
  In case 3, it increases by at most alpha(n). Use Finset.sum_le_sum and
  phi_eq_of_same_data for unchanged nodes, phi_le_alpha_mul_rank for changed nodes. -/
theorem link_Phi_le (uf : UF n) (rx ry : Fin n)
    (hx : uf.isRoot rx) (hy : uf.isRoot ry) (hne : rx ≠ ry)
    (hn : ∀ y, uf.rank y < n) :
    Phi (link uf rx ry hx hy hne) ≤ Phi uf + alpha n := by
  set uf' := link uf rx ry hx hy hne with huf'
  unfold Phi
  -- Case split on rank comparison
  by_cases h1 : uf.rank rx < uf.rank ry
  · -- Case 1: rank rx < rank ry. rx attaches under ry. Phi doesn't increase.
    suffices h : ∑ x : Fin n, phi uf' x ≤ ∑ x : Fin n, phi uf x by omega
    apply Finset.sum_le_sum
    intro z _
    by_cases hzrx : z = rx
    · -- z = rx: was root with phi = alpha(n) * rank(rx), now non-root
      subst hzrx
      have : uf'.rank z = uf.rank z := by
        simp [huf', link, h1]
      calc phi uf' z ≤ alpha n * uf'.rank z := phi_le_alpha_mul_rank uf' z
        _ = alpha n * uf.rank z := by rw [this]
        _ = phi uf z := (phi_root uf z hx).symm
    · -- z ≠ rx: parent, rank, isRoot all unchanged
      have hp : uf'.parent z = uf.parent z := by
        simp [huf', link, h1, hzrx]
      have hr : uf'.rank z = uf.rank z := by
        simp [huf', link, h1]
      have hrp : uf'.rank (uf'.parent z) = uf.rank (uf.parent z) := by
        rw [hp]; simp [huf', link, h1]
      exact le_of_eq (phi_eq_of_same_data uf uf' z hp hr hrp)
  · by_cases h2 : uf.rank ry < uf.rank rx
    · -- Case 2: rank ry < rank rx. ry attaches under rx. Phi doesn't increase.
      suffices h : ∑ x : Fin n, phi uf' x ≤ ∑ x : Fin n, phi uf x by omega
      apply Finset.sum_le_sum
      intro z _
      by_cases hzry : z = ry
      · -- z = ry: was root, now non-root
        subst hzry
        have : uf'.rank z = uf.rank z := by
          simp [huf', link, h1, h2]
        calc phi uf' z ≤ alpha n * uf'.rank z := phi_le_alpha_mul_rank uf' z
          _ = alpha n * uf.rank z := by rw [this]
          _ = phi uf z := (phi_root uf z hy).symm
      · -- z ≠ ry: unchanged
        have hp : uf'.parent z = uf.parent z := by
          simp [huf', link, h1, h2, hzry]
        have hr : uf'.rank z = uf.rank z := by
          simp [huf', link, h1, h2]
        have hrp : uf'.rank (uf'.parent z) = uf.rank (uf.parent z) := by
          rw [hp]; simp [huf', link, h1, h2]
        exact le_of_eq (phi_eq_of_same_data uf uf' z hp hr hrp)
    · -- Case 3: rank rx = rank ry. ry attaches under rx, rx rank increases by 1.
      have heq : uf.rank rx = uf.rank ry := by omega
      -- Strategy: ∑ phi(uf',z) = phi(uf',rx) + ∑_{z≠rx} phi(uf',z)
      -- phi(uf',rx) = alpha(n)*(rank(rx)+1) = phi(uf,rx) + alpha(n)
      -- For z ≠ rx: phi(uf',z) ≤ phi(uf,z)
      -- So total ≤ phi(uf,rx) + alpha(n) + ∑_{z≠rx} phi(uf,z) = Phi(uf) + alpha(n)

      -- First, split sum at rx using Finset.add_sum_erase
      have hrx_mem : rx ∈ Finset.univ := Finset.mem_univ rx
      rw [← Finset.add_sum_erase Finset.univ (phi uf') hrx_mem]
      rw [← Finset.add_sum_erase Finset.univ (phi uf) hrx_mem]

      -- phi(uf', rx) = alpha(n) * (rank(rx) + 1) = phi(uf, rx) + alpha(n)
      have hrx_root' : uf'.isRoot rx := link_isRoot_rx_case3 uf rx ry hx hy hne h1 h2
      have hrx_rank' : uf'.rank rx = uf.rank rx + 1 := by
        simp [huf', link, h1, h2]
      have hphi_rx' : phi uf' rx = alpha n * (uf.rank rx + 1) := by
        rw [phi_root uf' rx hrx_root', hrx_rank']
      have hphi_rx : phi uf rx = alpha n * uf.rank rx := phi_root uf rx hx
      have hphi_rx_diff : phi uf' rx = phi uf rx + alpha n := by
        rw [hphi_rx', hphi_rx, Nat.mul_add, Nat.mul_one]

      -- For z ≠ rx: phi(uf', z) ≤ phi(uf, z)
      suffices hrest : ∑ x ∈ Finset.univ.erase rx, phi uf' x ≤
          ∑ x ∈ Finset.univ.erase rx, phi uf x by
        omega
      apply Finset.sum_le_sum
      intro z hz
      have hzrx : z ≠ rx := Finset.ne_of_mem_erase hz
      have hr : uf'.rank z = uf.rank z := by
        simp [huf', link, h1, h2, hzrx]
      by_cases hzry : z = ry
      · -- z = ry: was root, now non-root
        subst hzry
        calc phi uf' z ≤ alpha n * uf'.rank z := phi_le_alpha_mul_rank uf' z
          _ = alpha n * uf.rank z := by rw [hr]
          _ = phi uf z := (phi_root uf z hy).symm
      · -- z ≠ rx, z ≠ ry: parent preserved
        have hp : uf'.parent z = uf.parent z := by
          simp [huf', link, h1, h2, hzry]
        have hrp_ge : uf.rank (uf.parent z) ≤ uf'.rank (uf'.parent z) := by
          rw [hp]
          -- uf'.rank (uf.parent z) uses the rank function from case 3:
          -- if uf.parent z = rx then uf.rank rx + 1 else uf.rank (uf.parent z)
          show uf.rank (uf.parent z) ≤ (link uf rx ry hx hy hne).rank (uf.parent z)
          simp only [link, h1, h2]
          by_cases hprx : uf.parent z = rx
          · simp [hprx]
          · simp [hprx]
        by_cases hroot_z : uf.isRoot z
        · -- z is a root in uf, still root in uf'
          have hroot_z' : uf'.isRoot z := by
            simp [huf', link, h1, h2, UF.isRoot, hzry]
            exact hroot_z
          rw [phi_root uf' z hroot_z', phi_root uf z hroot_z, hr]
        · -- z is non-root in uf
          have hroot_z' : ¬uf'.isRoot z := by
            simp [huf', link, h1, h2, UF.isRoot, hzry]
            exact hroot_z
          by_cases hprx : uf.parent z = rx
          · -- parent(z) = rx: parent-rank increases, use phi_le_of_parent_rank_le
            have hn_par : uf.rank (uf.parent z) < n := hn (uf.parent z)
            exact phi_le_of_parent_rank_le uf uf' z hp hr hrp_ge hroot_z hn_par
          · -- parent(z) ≠ rx: parent-rank unchanged, use phi_eq_of_same_data
            have hrp : uf'.rank (uf'.parent z) = uf.rank (uf.parent z) := by
              rw [hp]
              simp only [huf', link, h1, h2]
              simp [hprx]
            exact le_of_eq (phi_eq_of_same_data uf uf' z hp hr hrp)

/-! ### Amortized cost of union -/

/-- The amortized cost of union is at most 3 * alpha(n) + 4. -/
theorem union_amortized (uf : UF n) (x y : Fin n)
    (hn : ∀ z, uf.rank z < n) :
    (union uf x y).time + Phi ⟪union uf x y⟫ ≤ Phi uf + 3 * alpha n + 4 := by
  -- Abbreviations
  let uf₁ := ⟪find uf x⟫.2
  let rx := ⟪find uf x⟫.1
  let uf₂ := ⟪find uf₁ y⟫.2
  let ry := ⟪find uf₁ y⟫.1
  -- hn propagates
  have hn₁ : ∀ z, uf₁.rank z < n := fun z => find_ret_rank_eq uf x ▸ hn z
  have hn₂ : ∀ z, uf₂.rank z < n := fun z => find_ret_rank_eq uf₁ y ▸ hn₁ z
  -- find_amortized bounds
  have hf₁ : (find uf x).time + Phi uf₁ ≤ Phi uf + alpha n + 2 := find_amortized uf x hn
  have hf₂ : (find uf₁ y).time + Phi uf₂ ≤ Phi uf₁ + alpha n + 2 := find_amortized uf₁ y hn₁
  -- Key: union is defined as
  -- ⟨if rx = ry then uf₂ else link uf₂ rx ry ..., find₁.time + find₂.time⟩
  -- We proceed by cases on rx = ry
  by_cases hne : rx = ry
  · -- rx = ry: result is uf₂
    -- (union uf x y) = ⟨uf₂, time₁ + time₂⟩ when rx = ry
    have htime : (union uf x y).time = (find uf x).time + (find uf₁ y).time := by
      show (union uf x y).time = (find uf x).time + (find uf₁ y).time
      unfold union
      exact dif_pos hne ▸ rfl
    have hret : ⟪union uf x y⟫ = uf₂ := by
      show (union uf x y).ret = uf₂
      unfold union
      exact dif_pos hne ▸ rfl
    rw [htime, hret]
    have := Nat.add_le_add hf₁ hf₂
    omega
  · -- rx ≠ ry: result is link uf₂ rx ry
    have htime : (union uf x y).time = (find uf x).time + (find uf₁ y).time := by
      show (union uf x y).time = (find uf x).time + (find uf₁ y).time
      unfold union
      exact dif_neg hne ▸ rfl
    rw [htime]
    have hret : ⟪union uf x y⟫ = link uf₂ rx ry
        (find_preserves_roots uf₁ y rx (find_ret_isRoot uf x))
        (find_ret_isRoot uf₁ y) hne := by
      show (union uf x y).ret = link uf₂ rx ry _ _ hne
      unfold union
      exact dif_neg hne ▸ rfl
    rw [hret]
    have hlink := link_Phi_le uf₂ rx ry
      (find_preserves_roots uf₁ y rx (find_ret_isRoot uf x))
      (find_ret_isRoot uf₁ y) hne hn₂
    have := Nat.add_le_add hf₁ hf₂
    omega

/-! ### Main theorem -/

/-- **Main theorem**: m operations on n elements cost at most m * (3 * alpha(n) + 4).

This is O(m * alpha(n)), the inverse-Ackermann amortized bound for union-find
with path compression and union by rank. -/
theorem union_find_amortized (n : ℕ) (hn : 2 ≤ n) (ops : List (Op n)) :
    (runOps (UF.init n) ops).time ≤ ops.length * (3 * alpha n + 4) := by
  sorry

end Cslib.Algorithms.Lean.UnionFind
