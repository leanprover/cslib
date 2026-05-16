/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov, Antoine du Fresne von Hohenesche,
  Sorrachai Yingchareonthawornchai
-/

import Cslib.Foundations.Data.SplayTree.Basic

/-!
# Splay Tree Correctness

This module proves the functional correctness of the splay operation.
It establishes that splaying preserves the binary search tree (BST) invariant
and guarantees that querying an existing key successfully rotates it to the root.
-/

variable {α : Type}

namespace SplayTree

open BinaryTree

/-! ### `toKeyList` Preservation -/
section ToKeyListPreservation

@[simp] theorem toKeyList_rotateRight (t : BinaryTree α) :
    (rotateRight t).toKeyList = t.toKeyList := by
  cases t; · rfl
  rename_i l _ r
  cases l <;> simp [rotateRight, toKeyList]

@[simp] theorem toKeyList_rotateLeft (t : BinaryTree α) :
    (rotateLeft t).toKeyList = t.toKeyList := by
  cases t; · rfl
  rename_i l _ r
  cases r <;> simp [rotateLeft, toKeyList]

@[simp] theorem toKeyList_bringUp (d : Dir) (t : BinaryTree α) :
    (d.bringUp t).toKeyList = t.toKeyList := by
  cases d <;> simp [Dir.bringUp]

@[simp] theorem toKeyList_applyChild (d : Dir) (op : BinaryTree α → BinaryTree α)
    (hop : ∀ s, (op s).toKeyList = s.toKeyList) (t : BinaryTree α) :
    (applyChild d op t).toKeyList = t.toKeyList := by
  cases t with
  | empty => rfl
  | node l k r => cases d <;> simp [applyChild, toKeyList, hop]

@[simp]
theorem toKeyList_applyChild_bringUp (d₁ d₂ : Dir) (t : BinaryTree α) :
    (applyChild d₁ d₂.bringUp t).toKeyList = t.toKeyList :=
  toKeyList_applyChild _ _ (toKeyList_bringUp _) _

@[simp] theorem toKeyList_Frame_attach (c : BinaryTree α) (f : Frame α) :
    (f.attach c).toKeyList =
      (match f.dir with
        | .L => c.toKeyList ++ [f.key] ++ f.sibling.toKeyList
        | .R => f.sibling.toKeyList ++ [f.key] ++ c.toKeyList) := by
  unfold Frame.attach
  cases f.dir <;> simp [toKeyList]

lemma reassemble_toKeyList_congr {c1 c2 : BinaryTree α} (path : List (Frame α))
    (h : c1.toKeyList = c2.toKeyList) :
    (reassemble c1 path).toKeyList = (reassemble c2 path).toKeyList := by
  induction path generalizing c1 c2 with
  | nil => simp [h]
  | cons f rest ih =>
    apply ih
    simp [h]

@[simp]
theorem toKeyList_splayUp (c : BinaryTree α) (path : List (Frame α)) :
    (splayUp c path).toKeyList = (reassemble c path).toKeyList := by
  induction c, path using splayUp_induction with
  | nil c => simp
  | single c f =>
    simp [splayUp, reassemble]
  | step c f1 f2 rest ih =>
    unfold splayUp; split_ifs <;>
      (rw [ih]; apply reassemble_toKeyList_congr; simp)

@[simp]
theorem toKeyList_splay [LinearOrder α] (t : BinaryTree α) (q : α) :
    (splay t q).toKeyList = t.toKeyList := by
  unfold splay
  have hpres := descend_preserves_tree t q
  match h : descend t q with
  | (.empty, []) =>
      rw [h] at hpres
      simp at hpres
      simp [← hpres]
  | (.empty, f :: rest) =>
      rw [h] at hpres
      rw [toKeyList_splayUp, ← hpres]
      simp [reassemble]
  | (.node l k r, path) =>
      rw [h] at hpres
      rw [toKeyList_splayUp, ← hpres]

theorem splay_empty_iff [LinearOrder α] (t : BinaryTree α) (q : α) :
    splay t q = .empty ↔ t = .empty := by
  constructor
  · intro h
    have hn := num_nodes_splay t q
    rw [h] at hn
    cases t with
    | empty => rfl
    | node l k r => simp at hn; omega
  · rintro rfl
    simp [splay, descend, descend.go]

end ToKeyListPreservation


/-! ### BST Preservation -/
section BSTPreservation

/-- `ForallTree p t` is equivalent to "every key in the in-order traversal
of `t` satisfies `p`". Reduces tree-quantifier reasoning to list-membership. -/
lemma ForallTree_iff_toKeyList (p : α → Prop) (t : BinaryTree α) :
    ForallTree p t ↔ ∀ k ∈ t.toKeyList, p k := by
  induction t with
  | empty => exact ⟨fun _ _ hk => by simp at hk, fun _ => .left⟩
  | node l k r ihl ihr =>
    simp only [toKeyList_node, List.mem_append,
      List.mem_singleton]
    constructor
    · intro h; cases h with | node _ _ _ hl hk hr =>
      rintro k' ((hk' | rfl) | hk')
      · exact ihl.mp hl k' hk'
      · exact hk
      · exact ihr.mp hr k' hk'
    · intro h
      exact .node _ _ _
        (ihl.mpr fun k' hk' => h _ (.inl (.inl hk')))
        (h _ (.inl (.inr rfl)))
        (ihr.mpr fun k' hk' => h _ (.inr hk'))

/-- A tree is a BST iff its in-order traversal is strictly sorted (pairwise
`<`). Reduces every BST-preservation question to "does the operation
preserve `toKeyList`?". -/
theorem IsBST_iff_toKeyList_sorted [LinearOrder α] (t : BinaryTree α) :
    IsBST t ↔ t.toKeyList.Pairwise (· < ·) := by
  induction t with
  | empty => exact ⟨fun _ => by simp, fun _ => .left⟩
  | node l k r ihl ihr =>
    simp only [toKeyList_node, List.pairwise_append,
      List.pairwise_cons, List.Pairwise.nil, List.mem_singleton,
      List.mem_append, List.not_mem_nil, false_implies,
      implies_true, and_true, true_and]
    constructor
    · intro h; cases h with | node _ _ _ hfl hfr hBl hBr =>
      have hlk := (ForallTree_iff_toKeyList _ _).mp hfl
      have hkr := (ForallTree_iff_toKeyList _ _).mp hfr
      exact ⟨⟨ihl.mp hBl, fun a ha b hb => hb ▸ hlk a ha⟩,
        ihr.mp hBr,
        fun a ha b hb => ha.elim
          (fun h => lt_trans (hlk a h) (hkr b hb))
          (fun h => h ▸ hkr b hb)⟩
    · intro ⟨⟨hl, hlk⟩, hr, hcross⟩
      exact .node _ _ _
        ((ForallTree_iff_toKeyList _ _).mpr
          fun k' hk' => hlk k' hk' k rfl)
        ((ForallTree_iff_toKeyList _ _).mpr
          fun k' hk' => hcross k (.inr rfl) k' hk')
        (ihl.mpr hl) (ihr.mpr hr)

/-- Transfer BST-ness between trees with the same in-order traversal. -/
lemma IsBST_of_toKeyList_eq [LinearOrder α] {t t' : BinaryTree α}
    (h : t'.toKeyList = t.toKeyList) (hbst : IsBST t) : IsBST t' := by
  rw [IsBST_iff_toKeyList_sorted] at hbst ⊢; rwa [h]

/-- Bottom-up splay preserves the BST invariant. -/
theorem IsBST_splay [LinearOrder α] (t : BinaryTree α) (q : α) (h : IsBST t) :
    IsBST (splay t q) :=
  IsBST_of_toKeyList_eq (toKeyList_splay t q) h

/-- Each primitive rotation preserves the BST invariant. -/
theorem IsBST_bringUp [LinearOrder α] (d : Dir) (t : BinaryTree α) (h : IsBST t) :
    IsBST (d.bringUp t) :=
  IsBST_of_toKeyList_eq (toKeyList_bringUp d t) h

theorem IsBST_applyChild [LinearOrder α] (d : Dir) (op : BinaryTree α → BinaryTree α)
    (hop_keys : ∀ s, (op s).toKeyList = s.toKeyList)
    (t : BinaryTree α) (h : IsBST t) :
    IsBST (applyChild d op t) :=
  IsBST_of_toKeyList_eq (toKeyList_applyChild d op hop_keys t) h

/-- Any frame-wise splay-up preserves BST-ness of the reassembled tree. -/
theorem IsBST_splayUp [LinearOrder α] (c : BinaryTree α) (path : List (Frame α))
    (h : IsBST (reassemble c path)) : IsBST (splayUp c path) :=
  IsBST_of_toKeyList_eq (toKeyList_splayUp c path) h

end BSTPreservation


/-! ### Root of `splay` on a Contained Key -/
section RootOfContainedKey

/-- If `t.contains q`, the subtree reached by `descend` is a node whose key
equals `q`. Mirrors how `descend` and `BinaryTree.contains` follow the same
comparison path. -/
theorem descend_contains [LinearOrder α] (t : BinaryTree α) (q : α) (h : t.contains q) :
    ∃ l r, (descend t q).1 = .node l q r := by
  induction t with
  | empty => simp [contains] at h
  | node lt k rt ihl ihr =>
    simp only [contains] at h
    by_cases hlt : q < k
    · simp only [hlt, ite_true] at h
      obtain ⟨l', r', hd⟩ := ihl h
      exact ⟨l', r', by rw [descend_node_lt hlt]; exact hd⟩
    · simp only [hlt, ite_false] at h
      by_cases hgt : k < q
      · simp only [hgt, ite_true] at h
        obtain ⟨l', r', hd⟩ := ihr h
        exact ⟨l', r', by rw [descend_node_gt hgt]; exact hd⟩
      · have hqk : q = k := le_antisymm (not_lt.mp hgt) (not_lt.mp hlt)
        subst hqk; exact ⟨lt, rt, by rw [descend_node_eq]⟩

/-- Splaying a node `c = .node l k r` upward along any path yields a tree
whose root key is still `k`. Each rotation step (`bringUp`, `applyChild
bringUp`) brings `c` one level higher without changing its root key. -/
theorem splayUp_root_key_of_node :
    ∀ (path : List (Frame α)) (l : BinaryTree α) (k : α) (r : BinaryTree α),
      ∃ l' r', splayUp (.node l k r) path = .node l' k r' := by
  intro path
  induction path using List.twoStepInduction with
  | nil => intro l k r; exact ⟨l, r, rfl⟩
  | singleton f =>
    intro l k r; obtain ⟨d, kf, s⟩ := f
    cases d <;> simp [splayUp, Dir.bringUp, Frame.attach,
      rotateRight, rotateLeft]
  | cons_cons f1 f2 rest ih _ =>
    intro l k r; simp only [splayUp]
    obtain ⟨d1, k1, s1⟩ := f1; obtain ⟨d2, k2, s2⟩ := f2
    suffices ∃ l' r', (if d1 = d2 then _ else _) =
        BinaryTree.node l' k r' by
      obtain ⟨l', r', heq⟩ := this; rw [heq]; exact ih l' k r'
    cases d1 <;> cases d2 <;>
      simp [Frame.attach, Dir.bringUp, applyChild,
        rotateRight, rotateLeft]

/-- If `t.contains q`, the bottom-up splay of `t` at `q` has `q` at the root.
Replaces `Correctness.splay_root_of_contains` for `splay`. -/
theorem splay_root_of_contains [LinearOrder α] (t : BinaryTree α) (q : α)
    (hc : t.contains q) : ∃ l r, splay t q = .node l q r := by
  obtain ⟨lr, rr, hd⟩ := descend_contains t q hc
  unfold splay
  rcases hdecomp : descend t q with ⟨reached, path⟩
  rw [hdecomp] at hd
  subst hd
  exact splayUp_root_key_of_node path lr q rr

end RootOfContainedKey

end SplayTree
