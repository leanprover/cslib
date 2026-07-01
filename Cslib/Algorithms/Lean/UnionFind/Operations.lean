/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module

public import Cslib.Init
public import Cslib.Algorithms.Lean.UnionFind.Basic

/-!
# Union-Find Operations

This file constructs the initial `singleton` forest, in which every element is its own
root with rank `0`, and proves it well-formed. This witnesses that the `WellFormed`
hypothesis used throughout the rank-bound development is satisfiable, so the
`findDepth_le_log` bound is non-vacuous.

It also defines the `link` operation (union by rank) and the reusable helper lemmas about
reachability under a parent-pointer `Function.update` that underpin its correctness.

## Main definitions

* `UnionFind.singleton`: The forest where every element is its own root with rank `0`.
* `UnionFind.link`: Union by rank, attaching the lower-rank root under the higher-rank one.

## Main results

* `UnionFind.singleton_wellFormed`: The singleton forest is well-formed.
* `UnionFind.iterate_parent_isRoot`: Following parents from a root stays at that root.
* `UnionFind.reaches_root_unique`: Each node reaches a unique root.
* `UnionFind.iterate_update_eq_of_forall_ne`: Updating a parent pointer leaves a path
  unchanged as long as the path avoids the updated key.
* `UnionFind.subtree_subset_attach`: Attaching a root under another node only grows subtrees.
* `UnionFind.subtree_root_subset_attach`: After attaching root `a` under root `b`, every node of
  `a`'s old subtree lands in `b`'s new subtree.
* `UnionFind.subtreeSize_attach_ge`: After attaching root `a` under root `b`, the new subtree of
  `b` is at least as large as the two old subtrees combined.
* `UnionFind.link_wellFormed`: Union by rank preserves well-formedness — linking two distinct
  roots of a well-formed forest yields a well-formed forest. Consequently the `findDepth_le_log`
  bound applies to every forest built from singletons by unions.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.UnionFind

variable {n : ℕ} (uf : UnionFind n)

/-- The forest where every element is its own root with rank `0`. -/
def singleton (n : ℕ) : UnionFind n where
  parent := id
  rank := fun _ => 0

/-- The parent function of the singleton forest is the identity. -/
@[simp] lemma singleton_parent (i : Fin n) : (singleton n).parent i = i := rfl

/-- Every element of a singleton forest is a root. -/
@[simp] lemma singleton_isRoot (i : Fin n) : (singleton n).IsRoot i := rfl

/-- The singleton forest is well-formed, so the `WellFormed` hypothesis is satisfiable. -/
theorem singleton_wellFormed : (singleton n).WellFormed where
  rank_lt i h := absurd (singleton_isRoot i) h
  size_ge i := by
    change 2 ^ 0 ≤ (singleton n).subtreeSize i
    simp only [Nat.pow_zero]
    exact (singleton n).one_le_subtreeSize i

/-- Link two roots `a` and `b` using union by rank: attach the lower-rank root under the
  higher-rank one; on a tie, attach `a` under `b` and increment `b`'s rank. Only the parent of
  the demoted root, and (on a tie) the rank of `b`, change. -/
def link (uf : UnionFind n) (a b : Fin n) : UnionFind n :=
  if uf.rank a < uf.rank b then
    { uf with parent := Function.update uf.parent a b }
  else if uf.rank b < uf.rank a then
    { uf with parent := Function.update uf.parent b a }
  else
    { uf with
      parent := Function.update uf.parent a b
      rank := Function.update uf.rank b (uf.rank b + 1) }

/-- Following parents from a root stays at that root. -/
lemma iterate_parent_isRoot {x : Fin n} (hx : uf.IsRoot x) (m : ℕ) :
    uf.parent^[m] x = x := by
  induction m with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih]; exact hx

/-- A node reaches at most one root: the root reached by following parents is unique. -/
lemma reaches_root_unique {j r₁ r₂ : Fin n}
    (h₁ : uf.reaches j r₁) (hr₁ : uf.IsRoot r₁)
    (h₂ : uf.reaches j r₂) (hr₂ : uf.IsRoot r₂) : r₁ = r₂ := by
  obtain ⟨k₁, hk₁⟩ := h₁
  obtain ⟨k₂, hk₂⟩ := h₂
  rcases le_total k₁ k₂ with hle | hle
  · have heq : uf.parent^[k₂] j = uf.parent^[k₂ - k₁] (uf.parent^[k₁] j) := by
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel hle]
    rw [hk₁, uf.iterate_parent_isRoot hr₁] at heq
    rw [hk₂] at heq
    exact heq.symm
  · have heq : uf.parent^[k₁] j = uf.parent^[k₁ - k₂] (uf.parent^[k₂] j) := by
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel hle]
    rw [hk₂, uf.iterate_parent_isRoot hr₂] at heq
    rw [hk₁] at heq
    exact heq

/-- Iterating an updated parent function agrees with the original as long as the path from
`j` never visits the updated key `a` (within the first `k` steps). -/
lemma iterate_update_eq_of_forall_ne {p : Fin n → Fin n} {a b j : Fin n} {k : ℕ}
    (h : ∀ m, m < k → p^[m] j ≠ a) :
    (Function.update p a b)^[k] j = p^[k] j := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      ih (fun m hm => h m (by omega))]
    exact Function.update_of_ne (h k (by omega)) b p

/-- Attaching root `a` under another node `b` only grows subtrees: every old subtree
is contained in the corresponding subtree of the updated forest. -/
lemma subtree_subset_attach {a b : Fin n} (ha : uf.IsRoot a)
    (uf' : UnionFind n) (hp : uf'.parent = Function.update uf.parent a b) (i : Fin n) :
    uf.subtree i ⊆ uf'.subtree i := by
  classical
  intro j hj
  simp only [subtree, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  obtain ⟨k₀, hk₀⟩ := hj
  -- minimal step count reaching `i`
  let k := Nat.find (⟨k₀, hk₀⟩ : ∃ k, uf.parent^[k] j = i)
  have hk : uf.parent^[k] j = i := Nat.find_spec (⟨k₀, hk₀⟩ : ∃ k, uf.parent^[k] j = i)
  have hmin : ∀ m, m < k → ¬ (uf.parent^[m] j = i) :=
    fun m hm => Nat.find_min (⟨k₀, hk₀⟩ : ∃ k, uf.parent^[k] j = i) hm
  -- the path avoids `a` strictly before reaching `i`
  have key : ∀ m, m < k → uf.parent^[m] j ≠ a := by
    intro m hm hma
    -- if the path hits `a` at step m, then it stays at `a = i` from then on
    have hcancel : uf.parent^[k] j = uf.parent^[k - m] (uf.parent^[m] j) := by
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel hm.le]
    rw [hma, uf.iterate_parent_isRoot ha] at hcancel
    rw [hk] at hcancel
    -- so `i = a`, hence `uf.parent^[m] j = i`, contradicting minimality
    exact hmin m hm (by rw [hma, ← hcancel])
  refine ⟨k, ?_⟩
  rw [hp, iterate_update_eq_of_forall_ne key, hk]

/-- If `a`'s parent pointer is redirected to `b`, every node of `a`'s old subtree lands in
`b`'s new subtree. -/
lemma subtree_root_subset_attach {a b : Fin n}
    (uf' : UnionFind n) (hp : uf'.parent = Function.update uf.parent a b) :
    uf.subtree a ⊆ uf'.subtree b := by
  classical
  intro j hj
  simp only [subtree, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  obtain ⟨k₀, hk₀⟩ := hj
  -- minimal step count reaching `a`
  let k := Nat.find (⟨k₀, hk₀⟩ : ∃ k, uf.parent^[k] j = a)
  have hk : uf.parent^[k] j = a := Nat.find_spec (⟨k₀, hk₀⟩ : ∃ k, uf.parent^[k] j = a)
  have hmin : ∀ m, m < k → ¬ (uf.parent^[m] j = a) :=
    fun m hm => Nat.find_min (⟨k₀, hk₀⟩ : ∃ k, uf.parent^[k] j = a) hm
  have key := hmin
  -- after `k` steps in `uf'` we are at `a`; one more step lands at `b`
  have hk' : uf'.parent^[k] j = a := by
    rw [hp, iterate_update_eq_of_forall_ne key, hk]
  refine ⟨k + 1, ?_⟩
  rw [Function.iterate_succ_apply', hk', hp, Function.update_self]

/-- After attaching root `a` under root `b`, the new subtree of `b` is at least as large as the
two old subtrees combined. -/
lemma subtreeSize_attach_ge {a b : Fin n} (ha : uf.IsRoot a) (hb : uf.IsRoot b) (hab : a ≠ b)
    (uf' : UnionFind n) (hp : uf'.parent = Function.update uf.parent a b) :
    uf.subtreeSize b + uf.subtreeSize a ≤ uf'.subtreeSize b := by
  classical
  have hsub_b : uf.subtree b ⊆ uf'.subtree b := uf.subtree_subset_attach ha uf' hp b
  have hsub_a : uf.subtree a ⊆ uf'.subtree b := uf.subtree_root_subset_attach uf' hp
  have hdisj : Disjoint (uf.subtree b) (uf.subtree a) := by
    rw [Finset.disjoint_left]
    intro j hjb hja
    simp only [subtree, Finset.mem_filter, Finset.mem_univ, true_and] at hjb hja
    exact hab (uf.reaches_root_unique hja ha hjb hb)
  calc uf.subtreeSize b + uf.subtreeSize a
      = (uf.subtree b ∪ uf.subtree a).card := (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ (uf'.subtree b).card := Finset.card_le_card (Finset.union_subset hsub_b hsub_a)
    _ = uf'.subtreeSize b := rfl

/-- Subtree sizes only grow when a root `a` is attached under `b`. -/
private lemma subtreeSize_le_attach {a b : Fin n} (ha : uf.IsRoot a)
    (uf' : UnionFind n) (hp : uf'.parent = Function.update uf.parent a b) (i : Fin n) :
    uf.subtreeSize i ≤ uf'.subtreeSize i :=
  Finset.card_le_card (uf.subtree_subset_attach ha uf' hp i)

/-- Attaching a strictly-lower-rank root `a` under root `b` (ranks unchanged) preserves
well-formedness. -/
private lemma attach_lt_wellFormed (hwf : uf.WellFormed) {a b : Fin n}
    (ha : uf.IsRoot a) (hr : uf.rank a < uf.rank b) :
    ({ uf with parent := Function.update uf.parent a b }).WellFormed := by
  set uf' : UnionFind n := { uf with parent := Function.update uf.parent a b } with huf'
  refine ⟨fun i hi => ?_, fun i => ?_⟩
  · -- rank_lt
    by_cases hia : i = a
    · subst hia
      have hp : uf'.parent i = b := Function.update_self ..
      rw [hp]
      exact hr
    · have hp : uf'.parent i = uf.parent i := Function.update_of_ne hia b uf.parent
      have hnr : ¬ uf.IsRoot i := by
        intro hroot
        apply hi
        change uf'.parent i = i
        rw [hp]; exact hroot
      rw [hp]
      exact hwf.rank_lt i hnr
  · -- size_ge
    exact (hwf.size_ge i).trans (uf.subtreeSize_le_attach ha uf' rfl i)

/-- The tie case: attaching `a` under `b` and incrementing `b`'s rank preserves
well-formedness. -/
private lemma attach_eq_wellFormed (hwf : uf.WellFormed) {a b : Fin n}
    (ha : uf.IsRoot a) (hb : uf.IsRoot b) (hab : a ≠ b) (hr : uf.rank a = uf.rank b) :
    ({ uf with parent := Function.update uf.parent a b,
               rank := Function.update uf.rank b (uf.rank b + 1) }).WellFormed := by
  set uf' : UnionFind n :=
    { uf with parent := Function.update uf.parent a b,
              rank := Function.update uf.rank b (uf.rank b + 1) } with huf'
  have hba : b ≠ a := fun h => hab h.symm
  refine ⟨fun i hi => ?_, fun i => ?_⟩
  · -- rank_lt
    by_cases hia : i = a
    · subst hia
      have hpi : uf'.parent i = b := Function.update_self ..
      have hri : uf'.rank i = uf.rank i := Function.update_of_ne hab _ _
      have hrb : uf'.rank b = uf.rank b + 1 := Function.update_self ..
      rw [hpi, hri, hrb]
      omega
    · have hpi : uf'.parent i = uf.parent i := Function.update_of_ne hia b uf.parent
      have hnr : ¬ uf.IsRoot i := by
        intro hroot
        apply hi
        change uf'.parent i = i
        rw [hpi]; exact hroot
      have hlt := hwf.rank_lt i hnr
      by_cases hib : i = b
      · -- vacuous: b is a root in uf', contradicting hi
        exfalso
        apply hi
        change uf'.parent i = i
        rw [hpi, hib]
        exact hb
      · have hri : uf'.rank i = uf.rank i := Function.update_of_ne hib _ _
        rw [hpi, hri]
        by_cases hpb : uf.parent i = b
        · have hrp : uf'.rank (uf.parent i) = uf.rank b + 1 := by
            rw [hpb]; exact Function.update_self ..
          rw [hrp]
          rw [hpb] at hlt
          omega
        · have hrp : uf'.rank (uf.parent i) = uf.rank (uf.parent i) :=
            Function.update_of_ne hpb _ _
          rw [hrp]
          exact hlt
  · -- size_ge
    by_cases hib : i = b
    · subst hib
      have hri : uf'.rank i = uf.rank i + 1 := Function.update_self ..
      rw [hri]
      have hpow : 2 ^ (uf.rank i + 1) = 2 ^ uf.rank i + 2 ^ uf.rank i := by
        rw [Nat.pow_succ]; omega
      have hsb : 2 ^ uf.rank i ≤ uf.subtreeSize i := hwf.size_ge i
      have hsa : 2 ^ uf.rank i ≤ uf.subtreeSize a := by
        have := hwf.size_ge a
        rwa [hr] at this
      have hgrow : uf.subtreeSize i + uf.subtreeSize a ≤ uf'.subtreeSize i :=
        uf.subtreeSize_attach_ge ha hb hab uf' rfl
      rw [hpow]
      omega
    · have hri : uf'.rank i = uf.rank i := Function.update_of_ne hib _ _
      rw [hri]
      exact (hwf.size_ge i).trans (uf.subtreeSize_le_attach ha uf' rfl i)

/-- Union by rank preserves well-formedness: linking two distinct roots of a well-formed
forest yields a well-formed forest. -/
theorem link_wellFormed (hwf : uf.WellFormed) {a b : Fin n}
    (ha : uf.IsRoot a) (hb : uf.IsRoot b) (hab : a ≠ b) :
    (uf.link a b).WellFormed := by
  rw [link]
  split_ifs with h1 h2
  · exact uf.attach_lt_wellFormed hwf ha h1
  · exact uf.attach_lt_wellFormed hwf hb h2
  · exact uf.attach_eq_wellFormed hwf ha hb hab (by omega)

end Cslib.Algorithms.Lean.UnionFind
