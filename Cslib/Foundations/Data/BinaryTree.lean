/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov, Antoine du Fresne von Hohenesche,
  Sorrachai Yingchareonthawornchai
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Metric

@[expose] public section

/-!
# Binary Tree

In this file we introduce the `BinaryTree` data structure and its basic operations.
-/

variable {α : Type}

inductive BinaryTree (α : Type) where
  | empty
  | node (left : BinaryTree α) (key : α) (right : BinaryTree α)
  deriving DecidableEq

namespace BinaryTree

/-! ### Core Definitions -/
section CoreDefs

def left : BinaryTree α → BinaryTree α
  | .empty => .empty
  | .node l _ _ => l

def right : BinaryTree α → BinaryTree α
  | .empty => .empty
  | .node _ _ r => r

theorem non_empty_exist (s : BinaryTree α) (h : s ≠ .empty) :
    ∃ A k B, s = .node A k B := by
  induction s <;> grind

def num_nodes : BinaryTree α → ℕ
  | .empty => 0
  | .node l _ r => 1 + num_nodes l + num_nodes r

@[simp] lemma num_nodes_empty : num_nodes (empty : BinaryTree α) = 0 := rfl

@[simp] lemma num_nodes_node (l : BinaryTree α) (k : α) (r : BinaryTree α) :
    (node l k r).num_nodes = 1 + l.num_nodes + r.num_nodes := rfl

/-- In-order traversal as a list of keys. -/
def toKeyList : BinaryTree α → List α
  | .empty => []
  | .node l k r => l.toKeyList ++ [k] ++ r.toKeyList

@[simp] lemma toKeyList_empty : toKeyList (empty : BinaryTree α) = [] := rfl

@[simp] lemma toKeyList_node (l : BinaryTree α) (k : α) (r : BinaryTree α) :
    (node l k r).toKeyList = l.toKeyList ++ [k] ++ r.toKeyList := rfl

/-- Number of nodes on the search path for `q` in `t`. Zero on the empty
tree; on a node this counts the root plus (if `q ≠ k`) the search path
length in the appropriate subtree. -/
def search_path_len [LinearOrder α] (t : BinaryTree α) (q : α) : ℕ :=
  match t with
  | .empty => 0
  | .node l key r =>
    if q < key then
      1 + l.search_path_len q
    else if key < q then
      1 + r.search_path_len q
    else
      1

/--
Remark:
This implementation is not really a "contain function",
because a binary tree could have q >/< key while being in
the left/right subtree of key respectively.
If `contains t q` is true, then `q` is in `t`; but
the converse need not necessarily hold true. The
converse is true for a binary search tree.
-/
def contains [LinearOrder α] (t : BinaryTree α) (q : α) : Prop :=
  match t with
  | .empty => False
  | .node l key r =>
    if q < key then
      l.contains q
    else if key < q then
      r.contains q
    else
      True

end CoreDefs


/-! ### Rotations and Mirroring -/
section Transformations

def rotateRight : BinaryTree α → BinaryTree α
  | .node (.node a x b) y c => .node a x (.node b y c)
  | t => t

def rotateLeft : BinaryTree α → BinaryTree α
  | .node a x (.node b y c) => .node (.node a x b) y c
  | t => t

/-- Mirror a binary tree: swap every left and right subtree. -/
def mirror : BinaryTree α → BinaryTree α
  | .empty => .empty
  | .node l k r => .node r.mirror k l.mirror

@[simp] lemma mirror_empty : (empty : BinaryTree α).mirror = .empty := rfl

@[simp] lemma mirror_node (l : BinaryTree α) (k : α) (r : BinaryTree α) :
    (node l k r).mirror = .node r.mirror k l.mirror := rfl

@[simp] lemma mirror_mirror (t : BinaryTree α) : t.mirror.mirror = t := by
  induction t <;> simp_all

@[simp] lemma num_nodes_mirror (t : BinaryTree α) : t.mirror.num_nodes = t.num_nodes := by
  induction t <;> simp_all [num_nodes]; omega

@[simp] lemma mirror_rotateRight (t : BinaryTree α) :
    (rotateRight t).mirror = rotateLeft t.mirror := by
  cases t; · rfl
  rename_i l _ _
  cases l <;> rfl

@[simp] lemma mirror_rotateLeft (t : BinaryTree α) :
    (rotateLeft t).mirror = rotateRight t.mirror := by
  cases t; · rfl
  rename_i _ _ r
  cases r <;> rfl

@[simp] theorem num_nodes_rotateRight (t : BinaryTree α) :
    (rotateRight t).num_nodes = t.num_nodes := by
  rcases t with _ | ⟨(_ | ⟨ll, lk, lr⟩), k, r⟩ <;>
    simp [rotateRight]; omega

@[simp] theorem num_nodes_rotateLeft (t : BinaryTree α) :
    (rotateLeft t).num_nodes = t.num_nodes := by
  have h := num_nodes_rotateRight t.mirror
  simp only [← mirror_rotateLeft, num_nodes_mirror] at h; exact h

end Transformations


/-! ### Contains Characterizations -/
section ContainsLemmas

@[simp] lemma not_contains_empty [LinearOrder α] (q : α) :
    ¬ (empty : BinaryTree α).contains q := nofun

@[simp] lemma contains_node_lt [LinearOrder α] {l : BinaryTree α} {k q : α}
    {r : BinaryTree α} (h : q < k) :
    (node l k r).contains q ↔ l.contains q := by
  simp [contains, h]

@[simp] lemma contains_node_gt [LinearOrder α] {l : BinaryTree α} {k q : α}
    {r : BinaryTree α} (h : k < q) :
    (node l k r).contains q ↔ r.contains q := by
  simp [contains, h, not_lt_of_gt h]

@[simp] lemma contains_node_not_eq_not_lt [LinearOrder α]
    {l : BinaryTree α} {k q : α} {r : BinaryTree α}
    (h1 : ¬ q = k) (h2 : ¬ q < k) :
    (node l k r).contains q ↔ r.contains q := by
  have hgt : k < q := lt_of_le_of_ne (Std.not_lt.mp h2) (Ne.symm (Ne.intro h1))
  simp [contains, hgt, not_lt_of_gt hgt]

end ContainsLemmas


/-! ### Tree Invariants and BST Properties -/
section Invariants

inductive ForallTree (p : α → Prop) : BinaryTree α → Prop
  | left : ForallTree p .empty
  | node l key r :
     ForallTree p l →
     p key →
     ForallTree p r →
     ForallTree p (.node l key r)

inductive IsBST [LinearOrder α] : BinaryTree α → Prop
  | left : IsBST .empty
  | node key l r :
     ForallTree (fun k => k < key) l →
     ForallTree (fun k => key < k) r →
     IsBST l → IsBST r →
     IsBST (.node l key r)

end Invariants


/-! ### Accessor Lemmas for ForallTree -/
section ForallTreeAccessors

@[simp] lemma ForallTree.left_sub {p : α → Prop} {l : BinaryTree α} {k : α} {r : BinaryTree α}
    (h : ForallTree p (.node l k r)) : ForallTree p l := by
  cases h with | node _ _ _ hl _ _ => exact hl

@[simp] lemma ForallTree.root {p : α → Prop} {l : BinaryTree α} {k : α} {r : BinaryTree α}
    (h : ForallTree p (.node l k r)) : p k := by
  cases h with | node _ _ _ _ hk _ => exact hk

@[simp] lemma ForallTree.right_sub {p : α → Prop} {l : BinaryTree α} {k : α} {r : BinaryTree α}
    (h : ForallTree p (.node l k r)) : ForallTree p r := by
  cases h with | node _ _ _ _ _ hr => exact hr

end ForallTreeAccessors


/-! ### Accessor Lemmas for IsBST -/
section IsBSTAccessors

@[simp] lemma IsBST.forallTree_left [LinearOrder α] {l : BinaryTree α} {k : α} {r : BinaryTree α}
    (h : IsBST (.node l k r)) : ForallTree (· < k) l := by
  cases h with | node _ _ _ hl _ _ _ => exact hl

@[simp] lemma IsBST.forallTree_right [LinearOrder α] {l : BinaryTree α} {k : α} {r : BinaryTree α}
    (h : IsBST (.node l k r)) : ForallTree (k < ·) r := by
  cases h with | node _ _ _ _ hr _ _ => exact hr

@[simp] lemma IsBST.left_bst [LinearOrder α] {l : BinaryTree α} {k : α} {r : BinaryTree α}
    (h : IsBST (.node l k r)) : IsBST l := by
  cases h with | node _ _ _ _ _ hl _ => exact hl

@[simp] lemma IsBST.right_bst [LinearOrder α] {l : BinaryTree α} {k : α} {r : BinaryTree α}
    (h : IsBST (.node l k r)) : IsBST r := by
  cases h with | node _ _ _ _ _ _ hr => exact hr

end IsBSTAccessors

end BinaryTree


/-! ### BST Structure -/
section BSTStructure

structure BST (α : Type) [LinearOrder α] where
  tree : BinaryTree α
  hBST : BinaryTree.IsBST tree

namespace BST

/-- Checks if the BST contains a given key by delegating to the underlying tree. -/
def contains [LinearOrder α] (t : BST α) (q : α) : Prop :=
  t.tree.contains q

end BST

end BSTStructure
