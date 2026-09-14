/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov, Antoine du Fresne von Hohenesche,
  Sorrachai Yingchareonthawornchai
-/

module

public import Cslib.Foundations.Data.SplayTree.Basic

/-!
# Splay Tree Correctness

This module proves the functional correctness of the splay operation.
It establishes that splaying preserves the binary search tree (BST) invariant
and guarantees that querying an existing key successfully rotates it to the root.
-/

@[expose] public section

variable {α : Type}

namespace SplayTree

open Tree

/-! ### `toKeyList` Preservation -/
section ToKeyListPreservation

@[simp] theorem toKeyList_rotateRight (t : Tree α) :
    (rotateRight t).toKeyList = t.toKeyList := by
  cases t; · rfl
  rename_i k l r
  cases l <;> simp [rotateRight, toKeyList]

@[simp] theorem toKeyList_rotateLeft (t : Tree α) :
    (rotateLeft t).toKeyList = t.toKeyList := by
  cases t; · rfl
  rename_i k l r
  cases r <;> simp [rotateLeft, toKeyList]

@[simp] theorem toKeyList_bringUp (d : Dir) (t : Tree α) :
    (d.bringUp t).toKeyList = t.toKeyList := by
  cases d <;> simp [Dir.bringUp]

@[simp] theorem toKeyList_applyChild (d : Dir) (op : Tree α → Tree α)
    (hop : ∀ s, (op s).toKeyList = s.toKeyList) (t : Tree α) :
    (applyChild d op t).toKeyList = t.toKeyList := by
  cases t with
  | nil => rfl
  | node k l r => cases d <;> simp [applyChild, toKeyList, hop]

theorem toKeyList_applyChild_bringUp (d₁ d₂ : Dir) (t : Tree α) :
    (applyChild d₁ d₂.bringUp t).toKeyList = t.toKeyList :=
  toKeyList_applyChild _ _ (toKeyList_bringUp _) _

@[simp] theorem toKeyList_Frame_attach (c : Tree α) (f : Frame α) :
    (f.attach c).toKeyList =
      (match f.dir with
        | .L => c.toKeyList ++ [f.key] ++ f.sibling.toKeyList
        | .R => f.sibling.toKeyList ++ [f.key] ++ c.toKeyList) := by
  unfold Frame.attach
  cases f.dir <;> simp [toKeyList]

lemma reassemble_toKeyList_congr {c1 c2 : Tree α} (path : List (Frame α))
    (h : c1.toKeyList = c2.toKeyList) :
    (reassemble c1 path).toKeyList = (reassemble c2 path).toKeyList := by
  induction path generalizing c1 c2 with
  | nil => simp [h]
  | cons f rest ih =>
    apply ih
    simp [h]

@[simp]
theorem toKeyList_splayUp (c : Tree α) (path : List (Frame α)) :
    (splayUp c path).toKeyList = (reassemble c path).toKeyList := by
  induction c, path using splayUp_induction with
  | nil c => simp
  | single c f =>
    simp [splayUp, reassemble]
  | step c f1 f2 rest ih =>
    unfold splayUp; split_ifs <;>
      (rw [ih]; apply reassemble_toKeyList_congr; simp)

@[simp]
theorem toKeyList_splay [LinearOrder α] (t : Tree α) (q : α) :
    (splay t q).toKeyList = t.toKeyList := by
  unfold splay
  have hpres := descend_preserves_tree t q
  match h : descend t q with
  | (.nil, []) =>
      rw [h] at hpres
      simp at hpres
      simp [← hpres]
  | (.nil, f :: rest) =>
      rw [h] at hpres
      rw [toKeyList_splayUp, ← hpres]
      simp [reassemble]
  | (.node k l r, path) =>
      rw [h] at hpres
      rw [toKeyList_splayUp, ← hpres]

theorem splay_empty_iff [LinearOrder α] (t : Tree α) (q : α) :
    splay t q = .nil ↔ t = .nil := by
  constructor
  · intro h
    have hn := nodeCount_splay t q
    rw [h] at hn
    cases t with
    | nil => rfl
    | node k l r => simp at hn; omega
  · rintro rfl
    simp [splay, descend, descend.go]

end ToKeyListPreservation


/-! ### BST Preservation -/
section BSTPreservation

/-- Helper: `IsBSTAux t lb ub` is equivalent to the key list being bounded
and sorted. Proved by induction on `t`. -/
private lemma IsBSTAux_iff_bounded_sorted (t : Tree α) [LinearOrder α] :
    ∀ lb ub : Option α,
    IsBSTAux t lb ub ↔
      (∀ x ∈ t.toKeyList, lb.elim True (· < x)) ∧
      (∀ x ∈ t.toKeyList, ub.elim True (x < ·)) ∧
      t.toKeyList.Pairwise (· < ·) := by
  induction t with
  | nil => intro lb ub; simp
  | node k l r ihl ihr =>
    intro lb ub
    rw [IsBSTAux_node, ihl lb (some k), ihr (some k) ub]
    simp only [Option.elim, toKeyList_node, List.mem_append, List.mem_singleton]
    grind

/-- A tree is a BST iff its in-order traversal is strictly sorted (pairwise
`<`). Reduces every BST-preservation question to "does the operation
preserve `toKeyList`?". -/
theorem IsBST_iff_toKeyList_sorted [LinearOrder α] (t : Tree α) :
    IsBST t ↔ t.toKeyList.Pairwise (· < ·) := by
  simp only [IsBST, IsBSTAux_iff_bounded_sorted t none none, Option.elim]
  exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨fun _ _ => trivial, fun _ _ => trivial, h⟩⟩

/-- Transfer BST-ness between trees with the same in-order traversal. -/
lemma IsBST_of_toKeyList_eq [LinearOrder α] {t t' : Tree α}
    (h : t'.toKeyList = t.toKeyList) (hbst : IsBST t) : IsBST t' := by
  rw [IsBST_iff_toKeyList_sorted] at hbst ⊢; rwa [h]

/-- Bottom-up splay preserves the BST invariant. -/
theorem IsBST_splay [LinearOrder α] (t : Tree α) (q : α) (h : IsBST t) :
    IsBST (splay t q) :=
  IsBST_of_toKeyList_eq (toKeyList_splay t q) h

/-- Each primitive rotation preserves the BST invariant. -/
theorem IsBST_bringUp [LinearOrder α] (d : Dir) (t : Tree α) (h : IsBST t) :
    IsBST (d.bringUp t) :=
  IsBST_of_toKeyList_eq (toKeyList_bringUp d t) h

theorem IsBST_applyChild [LinearOrder α] (d : Dir) (op : Tree α → Tree α)
    (hop_keys : ∀ s, (op s).toKeyList = s.toKeyList)
    (t : Tree α) (h : IsBST t) :
    IsBST (applyChild d op t) :=
  IsBST_of_toKeyList_eq (toKeyList_applyChild d op hop_keys t) h

/-- Any frame-wise splay-up preserves BST-ness of the reassembled tree. -/
theorem IsBST_splayUp [LinearOrder α] (c : Tree α) (path : List (Frame α))
    (h : IsBST (reassemble c path)) : IsBST (splayUp c path) :=
  IsBST_of_toKeyList_eq (toKeyList_splayUp c path) h

end BSTPreservation


/-! ### Root of `splay` on a Contained Key -/
section RootOfContainedKey

/-- If `t.contains q`, the subtree reached by `descend` is a node whose key
equals `q`. Mirrors how `descend` and `Tree.contains` follow the same
comparison path. -/
theorem descend_contains [LinearOrder α] (t : Tree α) (q : α) (h : t.bstContains q) :
    ∃ l r, (descend t q).1 = l △[q] r := by
  induction t with
  | nil => simp [bstContains] at h
  | node k lt rt ihl ihr =>
    simp only [bstContains] at h
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

/-- Membership-style variant of `descend_contains`: in a BST, if `q ∈ t` then
`descend` reaches the node with key `q`. -/
theorem descend_contains' [LinearOrder α] (t : Tree α) (q : α) (hbst : IsBST t)
    (h : q ∈ t) : ∃ l r, (descend t q).1 = l △[q] r :=
  descend_contains t q (mem_imp_contains hbst h)

/-- Splaying a node `c = l △[k] r` upward along any path yields a tree
whose root key is still `k`. Each rotation step brings `c` one level higher
without changing its root key. -/
theorem splayUp_root_key_of_node :
    ∀ (path : List (Frame α)) (l : Tree α) (k : α) (r : Tree α),
      ∃ l' r', splayUp (l △[k] r) path = l' △[k] r' := by
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
        l' △[k] r' by
      obtain ⟨l', r', heq⟩ := this; rw [heq]; exact ih l' k r'
    cases d1 <;> cases d2 <;>
      simp [Frame.attach, Dir.bringUp, applyChild,
        rotateRight, rotateLeft]

/-- If `t.contains q`, the bottom-up splay of `t` at `q` has `q` at the root. -/
theorem splay_root_of_contains [LinearOrder α] (t : Tree α) (q : α)
    (hc : t.bstContains q) : ∃ l r, splay t q = l △[q] r := by
  obtain ⟨lr, rr, hd⟩ := descend_contains t q hc
  unfold splay
  rcases hdecomp : descend t q with ⟨reached, path⟩
  rw [hdecomp] at hd
  subst hd
  exact splayUp_root_key_of_node path lr q rr

/-- Membership-style variant of `splay_root_of_contains`: in a BST, if `q ∈ t`
then splaying brings `q` to the root. -/
theorem splay_root_of_contains' [LinearOrder α] (t : Tree α) (q : α)
    (hbst : IsBST t) (h : q ∈ t) : ∃ l r, splay t q = l △[q] r :=
  splay_root_of_contains t q (mem_imp_contains hbst h)

end RootOfContainedKey

end SplayTree
