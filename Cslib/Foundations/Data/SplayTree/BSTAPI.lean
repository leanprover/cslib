/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov, Antoine du Fresne von Hohenesche,
  Sorrachai Yingchareonthawornchai
-/

import Cslib.Foundations.Data.SplayTree.Complexity
import Cslib.Foundations.Data.SplayTree.Correctness

/-!
# Splay Tree API for BST

This module provides a high-level API for splaying directly on the `BST` type.
It encapsulates the raw `BinaryTree` operations and their associated invariant
proofs, allowing users to safely and cleanly manipulate BSTs without manually
re-proving the `IsBST` invariant after every rotation.
-/

variable {α : Type} [LinearOrder α]

namespace SplayTree.BSTAPI

open SplayTree
open BinaryTree

/-! ### Core Operation -/

/--
Splays a key `q` in the given BST `t`.
Returns a new `BST` and automatically resolves the `IsBST` invariant internally.
-/
def splay (t : BST α) (q : α) : BST α :=
  ⟨SplayTree.splay t.tree q, IsBST_splay t.tree q t.hBST⟩

/-! ### Correctness -/

/-- If the underlying BST contains a key, splaying brings it to the root. -/
theorem splay_root_of_contains (t : BST α) (q : α) (hc : t.contains q) :
    ∃ l r, (splay t q).tree = .node l q r :=
  SplayTree.splay_root_of_contains t.tree q hc

/-- Splaying preserves the in-order traversal (and therefore the exact elements) of the BST. -/
@[simp]
theorem toKeyList_splay (t : BST α) (q : α) :
    (splay t q).tree.toKeyList = t.tree.toKeyList :=
  SplayTree.toKeyList_splay t.tree q

/-- Splaying preserves the exact number of nodes. -/
@[simp]
theorem num_nodes_splay (t : BST α) (q : α) :
    (splay t q).tree.num_nodes = t.tree.num_nodes :=
  SplayTree.num_nodes_splay t.tree q

/-! ### Complexity -/

/-- The potential Φ of a BST, inherited directly from its underlying tree. -/
noncomputable def φ (t : BST α) : ℝ := SplayTree.φ t.tree

/-- The concrete operational cost of splaying a key in the BST. -/
noncomputable def splayCost (t : BST α) (q : α) : ℝ := SplayTree.splay.cost t.tree q

/--
The core O(log n) amortized bound reformulated for the safe `BST` type.
The potential change plus the actual cost is bounded by `3 * log_2(n) + 1`.
-/
theorem splay_amortized_bound (t : BST α) (q : α) :
    φ (splay t q) - φ t + splayCost t q ≤ 3 * Real.logb 2 t.tree.num_nodes + 1 :=
  SplayTree.splay_amortized_bound t.tree q


/-! ### Sequence Cost and Total Complexity Bound -/

/-- The total cost of a sequence of `m` splays, defined directly on the initial BST. -/
noncomputable def sequenceCost {m : ℕ} (init : BST α) (X : Fin m → α) : ℝ :=
  SplayTree.splay.sequence_cost init.tree X

/--
The classical total sequence cost bound for `m` operations on a BST of size `n`.
It guarantees that the total sequence cost is bounded by O(m log n + n log n).
-/
theorem nlogn_cost (n m : ℕ) (X : Fin m → α)
    (init : BST α) (h_size : init.tree.num_nodes = n) :
    sequenceCost init X ≤ m * (3 * Real.logb 2 n + 1) + n * Real.logb 2 n :=
  SplayTree.nlogn_cost n m X init.tree h_size

end SplayTree.BSTAPI
