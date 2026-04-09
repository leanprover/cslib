/-
Copyright (c) 2026 Juan Bono. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Bono
-/

module

public import Cslib.Algorithms.Lean.UnionFind.Operations
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Fintype.Card

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
- `rank_le_log_of_runOps`: ranks are bounded by log₂ n
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

/-- Tree size: number of nodes whose root is `r`. -/
private noncomputable def treeSize (uf : UF n) (r : Fin n) : ℕ :=
  (Finset.univ.filter (fun x => uf.rootOf x = r)).card

/-- Tree filters for distinct roots are disjoint. -/
private theorem tree_disjoint (uf : UF n) (rx ry : Fin n) (hne : rx ≠ ry) :
    Disjoint
      (Finset.univ.filter (fun x : Fin n => uf.rootOf x = rx))
      (Finset.univ.filter (fun x : Fin n => uf.rootOf x = ry)) := by
  rw [Finset.disjoint_filter]; intro x _ h1 h2; exact hne (h1 ▸ h2)

/-- After link, the union of old tree filters is contained in the winner's filter. -/
private theorem link_filter_subset (uf : UF n) (rx ry : Fin n)
    (hx : uf.isRoot rx) (hy : uf.isRoot ry) (hne : rx ≠ ry)
    (w : Fin n) (hw : w = if uf.rank rx < uf.rank ry then ry else rx) :
    (Finset.univ.filter (fun x : Fin n => uf.rootOf x = rx)) ∪
    (Finset.univ.filter (fun x : Fin n => uf.rootOf x = ry)) ⊆
    (Finset.univ.filter (fun x : Fin n => (link uf rx ry hx hy hne).rootOf x = w)) := by
  intro z hz
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hz ⊢
  rw [link_rootOf uf rx ry hx hy hne z]
  rcases hz with h | h <;> simp [h, hw]

/-- After link, the winner's tree size is at least the sum of the old tree sizes. -/
private theorem link_treeSize_winner (uf : UF n) (rx ry : Fin n)
    (hx : uf.isRoot rx) (hy : uf.isRoot ry) (hne : rx ≠ ry)
    (w : Fin n) (hw : w = if uf.rank rx < uf.rank ry then ry else rx) :
    treeSize (link uf rx ry hx hy hne) w ≥ treeSize uf rx + treeSize uf ry := by
  unfold treeSize
  have h1 := Finset.card_union_of_disjoint (tree_disjoint uf rx ry hne)
  have h2 := Finset.card_le_card (link_filter_subset uf rx ry hx hy hne w hw)
  omega

/-- For roots other than rx and ry, tree size is preserved after link. -/
private theorem link_treeSize_other (uf : UF n) (rx ry : Fin n)
    (hx : uf.isRoot rx) (hy : uf.isRoot ry) (hne : rx ≠ ry) (r : Fin n)
    (hr_ne_rx : r ≠ rx) (hr_ne_ry : r ≠ ry) :
    treeSize (link uf rx ry hx hy hne) r = treeSize uf r := by
  unfold treeSize; congr 1; ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [link_rootOf uf rx ry hx hy hne z]
  by_cases h_or : uf.rootOf z = rx ∨ uf.rootOf z = ry
  · simp only [h_or, ite_true]
    constructor
    · intro h; split_ifs at h with h_lt
      · exact absurd h.symm hr_ne_ry
      · exact absurd h.symm hr_ne_rx
    · intro h; rw [h] at h_or
      rcases h_or with h1 | h1
      · exact absurd h1 hr_ne_rx
      · exact absurd h1 hr_ne_ry
  · simp only [h_or, ite_false]

/-- The counting invariant (2^rank ≤ treeSize) is preserved by link. -/
private theorem link_invariant (uf : UF n) (rx ry : Fin n)
    (hx : uf.isRoot rx) (hy : uf.isRoot ry) (hne : rx ≠ ry)
    (inv : ∀ r, uf.isRoot r → 2 ^ uf.rank r ≤ treeSize uf r)
    (r : Fin n) (hr : (link uf rx ry hx hy hne).isRoot r) :
    2 ^ (link uf rx ry hx hy hne).rank r ≤ treeSize (link uf rx ry hx hy hne) r := by
  by_cases h1 : uf.rank rx < uf.rank ry
  · -- Case 1: rx → ry, winner = ry
    have h_rx_nr : ¬(link uf rx ry hx hy hne).isRoot rx := by
      intro h; have := h; unfold link UF.isRoot at this; simp [h1] at this
      exact hne this.symm
    have hr_ne_rx : r ≠ rx := fun heq => h_rx_nr (heq ▸ hr)
    have h_rank : (link uf rx ry hx hy hne).rank r = uf.rank r := by
      unfold link; simp [h1]
    rw [h_rank]
    by_cases hr_ry : r = ry
    · rw [hr_ry]
      calc 2 ^ uf.rank ry ≤ treeSize uf ry := inv ry hy
        _ ≤ treeSize uf rx + treeSize uf ry := Nat.le_add_left _ _
        _ ≤ treeSize (link uf rx ry hx hy hne) ry :=
            link_treeSize_winner uf rx ry hx hy hne ry (by simp [h1])
    · rw [link_treeSize_other uf rx ry hx hy hne r hr_ne_rx hr_ry]
      exact inv r (by have := hr; unfold link UF.isRoot at this;
                      simp [h1, hr_ne_rx] at this; exact this)
  · -- Cases 2,3: rank rx ≥ rank ry, loser = ry, winner = rx
    have h_ry_nr : ¬(link uf rx ry hx hy hne).isRoot ry := by
      intro h; have := h; unfold link UF.isRoot at this
      split_ifs at this with h2
      · simp at this; exact hne this
      · simp at this; exact hne this
    have hr_ne_ry : r ≠ ry := fun heq => h_ry_nr (heq ▸ hr)
    by_cases hr_rx : r = rx
    · rw [hr_rx]
      by_cases h2 : uf.rank ry < uf.rank rx
      · -- Case 2: strict inequality, rank unchanged
        have h_rank : (link uf rx ry hx hy hne).rank rx = uf.rank rx := by
          unfold link; simp [h1, h2]
        rw [h_rank]
        calc 2 ^ uf.rank rx ≤ treeSize uf rx := inv rx hx
          _ ≤ treeSize uf rx + treeSize uf ry := Nat.le_add_right _ _
          _ ≤ treeSize (link uf rx ry hx hy hne) rx :=
              link_treeSize_winner uf rx ry hx hy hne rx (by simp [h1])
      · -- Case 3: equal rank, rank rx bumped
        have h_eq : uf.rank rx = uf.rank ry := by omega
        have h_rank : (link uf rx ry hx hy hne).rank rx = uf.rank rx + 1 := by
          unfold link; simp [h1, h2]
        rw [h_rank, h_eq]
        calc 2 ^ (uf.rank ry + 1)
            = 2 ^ uf.rank ry * 2 := Nat.pow_succ 2 _
          _ = 2 ^ uf.rank ry + 2 ^ uf.rank ry := by omega
          _ ≤ treeSize uf rx + treeSize uf ry :=
              Nat.add_le_add (h_eq ▸ inv rx hx) (inv ry hy)
          _ ≤ treeSize (link uf rx ry hx hy hne) rx :=
              link_treeSize_winner uf rx ry hx hy hne rx (by simp [h1])
    · -- Other root: rank and treeSize unchanged
      have h_rank : (link uf rx ry hx hy hne).rank r = uf.rank r := by
        unfold link; split_ifs <;> simp [hr_rx]
      rw [h_rank, link_treeSize_other uf rx ry hx hy hne r hr_rx hr_ne_ry]
      exact inv r (by have := hr; unfold link UF.isRoot at this
                      split_ifs at this with h2 <;> simp [hr_ne_ry] at this <;> exact this)

/-- find preserves the counting invariant: ranks and rootOf are unchanged. -/
private theorem find_preserves_invariant (uf : UF n) (x : Fin n)
    (inv : ∀ r, uf.isRoot r → 2 ^ uf.rank r ≤ treeSize uf r) :
    ∀ r, (⟪find uf x⟫).2.isRoot r →
      2 ^ (⟪find uf x⟫).2.rank r ≤ treeSize (⟪find uf x⟫).2 r := by
  intro r hr
  have h_rank : (⟪find uf x⟫).2.rank r = uf.rank r := congrFun (find_ret_rank_eq uf x) r
  have h_ts : treeSize (⟪find uf x⟫).2 r = treeSize uf r := by
    unfold treeSize; congr 1; ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [find_preserves_rootOf uf x z]
  rw [h_rank, h_ts]
  exact inv r (by by_contra h_nr
                  exact h_nr (by have h1 := UF.rootOf_isRoot uf r
                                 have h2 := UF.rootOf_root _ r hr
                                 rw [find_preserves_rootOf uf x r] at h2
                                 rw [h2] at h1; exact h1))

/-- Each operation (find or union) preserves the counting invariant. -/
private theorem op_preserves_invariant (uf : UF n) (op : Op n)
    (inv : ∀ r, uf.isRoot r → 2 ^ uf.rank r ≤ treeSize uf r) :
    ∀ r, (⟪runOp uf op⟫).isRoot r →
      2 ^ (⟪runOp uf op⟫).rank r ≤ treeSize (⟪runOp uf op⟫) r := by
  cases op with
  | find x => exact find_preserves_invariant uf x inv
  | union x y =>
    show ∀ r, (⟪union uf x y⟫).isRoot r →
      2 ^ (⟪union uf x y⟫).rank r ≤ treeSize (⟪union uf x y⟫) r
    intro r hr
    have inv₂ := find_preserves_invariant (⟪find uf x⟫).2 y
      (find_preserves_invariant uf x inv)
    by_cases h : ⟪find uf x⟫.1 = ⟪find ⟪find uf x⟫.2 y⟫.1
    · -- Roots equal: union returns uf₂ unchanged
      have key : ⟪union uf x y⟫ = ⟪find ⟪find uf x⟫.2 y⟫.2 := by
        show (union uf x y).ret = _; unfold union; simp [h]
      rw [key] at hr ⊢; exact inv₂ r hr
    · -- Roots different: union returns link uf₂ rx ry
      have key : ⟪union uf x y⟫ = link ⟪find ⟪find uf x⟫.2 y⟫.2
          ⟪find uf x⟫.1 ⟪find ⟪find uf x⟫.2 y⟫.1
          (find_preserves_roots ⟪find uf x⟫.2 y ⟪find uf x⟫.1 (find_ret_isRoot uf x))
          (find_ret_isRoot ⟪find uf x⟫.2 y) h := by
        show (union uf x y).ret = _; unfold union; simp [h]
      rw [key] at hr ⊢; exact link_invariant _ _ _ _ _ h inv₂ r hr

/-- The counting invariant holds for any sequence of operations starting from init. -/
private theorem counting_invariant (ops : List (Op n)) (uf : UF n)
    (inv : ∀ r, uf.isRoot r → 2 ^ uf.rank r ≤ treeSize uf r) :
    ∀ r, (⟪runOps uf ops⟫).isRoot r →
      2 ^ (⟪runOps uf ops⟫).rank r ≤ treeSize (⟪runOps uf ops⟫) r := by
  induction ops generalizing uf with
  | nil => exact inv
  | cons op ops ih =>
    show ∀ r, (⟪runOps (⟪runOp uf op⟫) ops⟫).isRoot r →
      2 ^ (⟪runOps (⟪runOp uf op⟫) ops⟫).rank r ≤
        treeSize (⟪runOps (⟪runOp uf op⟫) ops⟫) r
    exact ih (⟪runOp uf op⟫) (op_preserves_invariant uf op inv)

/-- The initial UF satisfies the counting invariant: each singleton tree has size 1 ≥ 2^0. -/
private theorem init_invariant :
    ∀ r : Fin n, (UF.init n).isRoot r →
      2 ^ (UF.init n).rank r ≤ treeSize (UF.init n) r := by
  intro r hr
  simp only [UF.init_rank, treeSize]
  apply Finset.card_pos.mpr
  exact ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ r, UF.rootOf_root _ r hr⟩⟩

/-- In any UF reachable from init via find/union, all ranks are ≤ log₂ n. -/
theorem rank_le_log_of_runOps (n : ℕ) (_hn : 2 ≤ n) (ops : List (Op n)) (x : Fin n) :
    (⟪runOps (UF.init n) ops⟫).rank x ≤ Nat.log 2 n := by
  set uf := ⟪runOps (UF.init n) ops⟫
  have inv := counting_invariant ops (UF.init n) init_invariant
  -- Step 1: rank x ≤ rank (rootOf x)
  have h_rank_le : uf.rank x ≤ uf.rank (uf.rootOf x) := by
    by_cases hx : uf.isRoot x
    · rw [UF.rootOf_root uf x hx]
    · exact Nat.le_of_lt (rank_lt_rootOf uf x hx)
  -- Step 2: 2^rank(rootOf x) ≤ treeSize(rootOf x) by the invariant
  have h_inv := inv (uf.rootOf x) (UF.rootOf_isRoot uf x)
  -- Step 3: treeSize ≤ n
  have h_ts_le : treeSize uf (uf.rootOf x) ≤ n := by
    unfold treeSize
    calc (Finset.univ.filter (fun z => uf.rootOf z = uf.rootOf x)).card
        ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
      _ = n := by rw [Finset.card_univ, Fintype.card_fin]
  -- Step 4: 2^(rank x) ≤ n, therefore rank x ≤ log₂ n
  have h_pow_le : 2 ^ uf.rank x ≤ n :=
    calc 2 ^ uf.rank x
        ≤ 2 ^ uf.rank (uf.rootOf x) := Nat.pow_le_pow_right (by omega) h_rank_le
      _ ≤ treeSize uf (uf.rootOf x) := h_inv
      _ ≤ n := h_ts_le
  by_contra h_gt
  push Not at h_gt
  have h5 := Nat.lt_pow_succ_log_self (by omega : 1 < 2) n
  have h6 : Nat.log 2 n + 1 ≤ uf.rank x := h_gt
  have h7 : 2 ^ (Nat.log 2 n + 1) ≤ 2 ^ uf.rank x := Nat.pow_le_pow_right (by omega) h6
  omega

/-- Corollary: ranks are < n for reachable states. -/
theorem rank_lt_of_runOps (n : ℕ) (hn : 2 ≤ n) (ops : List (Op n)) (x : Fin n) :
    (⟪runOps (UF.init n) ops⟫).rank x < n := by
  have h1 := rank_le_log_of_runOps n hn ops x
  have h2 : Nat.log 2 n < n := Nat.log_lt_of_lt_pow (by omega) (Nat.lt_pow_self (by omega : 1 < 2))
  omega

end Cslib.Algorithms.Lean.UnionFind
