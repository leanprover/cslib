/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module

public import Cslib.Init
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic

/-!
# Union-Find Forest Model

This file defines a mathematical model of a union-by-rank union-find forest over `Fin n`.

## Main definitions

* `UnionFind`: A forest over `n` elements given by parent and rank functions.
* `UnionFind.IsRoot`: A node is a root iff it is its own parent.
* `UnionFind.reaches`: Reachability by following parent pointers.
* `UnionFind.subtree`: The set of nodes that reach a given root.
* `UnionFind.subtreeSize`: The cardinality of a subtree.
* `UnionFind.WellFormed`: Well-formedness for union by rank.

## Main results

* `UnionFind.self_mem_subtree`: Every node belongs to its own subtree.
* `UnionFind.one_le_subtreeSize`: Every subtree is nonempty.
* `UnionFind.subtreeSize_le`: Every subtree has at most `n` nodes.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

variable {n : ℕ}

/-- A union-find forest over `n` elements, given by parent and rank functions. -/
structure UnionFind (n : ℕ) where
  /-- Parent pointer; roots point to themselves. -/
  parent : Fin n → Fin n
  /-- Rank (an upper bound on subtree height) of each node. -/
  rank : Fin n → ℕ

namespace UnionFind

variable (uf : UnionFind n)

/-- `i` is a root iff it is its own parent. -/
def IsRoot (i : Fin n) : Prop := uf.parent i = i

instance (i : Fin n) : Decidable (uf.IsRoot i) := by unfold IsRoot; infer_instance

/-- `j` reaches `i` by following parent pointers some number of times. -/
def reaches (j i : Fin n) : Prop := ∃ k, uf.parent^[k] j = i

open Classical in
/-- The set of all nodes `j` that reach `i` by following parent pointers. -/
noncomputable def subtree (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => uf.reaches j i)

/-- The number of nodes in the subtree rooted at `i`. -/
noncomputable def subtreeSize (i : Fin n) : ℕ := (uf.subtree i).card

/-- Well-formedness for union by rank: ranks increase toward roots, and a rank-`r` node
owns at least `2 ^ r` nodes. -/
structure WellFormed : Prop where
  /-- Non-root nodes have strictly smaller rank than their parent. -/
  rank_lt : ∀ i, ¬ uf.IsRoot i → uf.rank i < uf.rank (uf.parent i)
  /-- A rank-`r` node owns at least `2 ^ r` nodes. -/
  size_ge : ∀ i, 2 ^ uf.rank i ≤ uf.subtreeSize i

/-- Every node reaches itself in zero steps. -/
@[simp] lemma reaches_self (i : Fin n) : uf.reaches i i := ⟨0, rfl⟩

open Classical in
/-- A node is always in its own subtree. -/
@[simp] lemma self_mem_subtree (i : Fin n) : i ∈ uf.subtree i := by
  simp only [subtree, Finset.mem_filter, Finset.mem_univ, reaches_self, and_self]

/-- Every subtree is nonempty. -/
@[simp] lemma one_le_subtreeSize (i : Fin n) : 1 ≤ uf.subtreeSize i := by
  unfold subtreeSize
  exact Finset.card_pos.mpr ⟨i, uf.self_mem_subtree i⟩

open Classical in
/-- A subtree has at most `n` nodes. -/
lemma subtreeSize_le (i : Fin n) : uf.subtreeSize i ≤ n := by
  unfold subtreeSize subtree
  have hle : (Finset.univ.filter (fun j => uf.reaches j i)).card ≤ Finset.univ.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have huniv : (Finset.univ : Finset (Fin n)).card = n := by
    simp [Finset.card_def, Fin.univ_def, List.length_finRange]
  omega

end UnionFind

end Cslib.Algorithms.Lean
