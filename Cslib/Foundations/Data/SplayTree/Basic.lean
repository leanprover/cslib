/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov, Antoine du Fresne von Hohenesche,
  Sorrachai Yingchareonthawornchai
-/

module

public import Cslib.Foundations.Data.BinaryTree
public import Mathlib.Data.List.Sort

/-!
# Splay Tree Basic Definitions

This module defines the core operations of a bottom-up splay tree, including
rotation primitives, path frames, and the `splay` and `splayUp` functions.
It also provides fundamental structural lemmas regarding tree size and descent paths.
-/

@[expose] public section

variable {α : Type}

namespace SplayTree

open Tree

/-! ### Definitions -/
section Definitions

/-- The direction taken from a parent while descending toward a target. -/
inductive Dir
  /-- The target lies in the left subtree of this parent. -/
  | L
  /-- The target lies in the right subtree of this parent. -/
  | R
  deriving DecidableEq, Repr

/-- Flip a direction: `L ↔ R`. -/
def Dir.flip : Dir → Dir
  | .L => .R
  | .R => .L

@[simp] lemma Dir.flip_flip (d : Dir) : d.flip.flip = d := by cases d <;> rfl
@[simp] lemma Dir.flip_ne (d : Dir) : d.flip ≠ d := by cases d <;> simp [flip]
@[simp] lemma Dir.ne_flip (d : Dir) : d ≠ d.flip := by cases d <;> simp [flip]

/-- Single primitive rotation that brings the `d`-child of the root up one
level. `L` ↦ `rotateRight`, `R` ↦ `rotateLeft`. -/
def Dir.bringUp : Dir → Tree α → Tree α
  | .L => rotateRight
  | .R => rotateLeft

/-- Apply `op` to the `d`-child of the root, leaving everything else fixed. -/
def applyChild (d : Dir) (op : Tree α → Tree α) : Tree α → Tree α
  | l △[k] r =>
    match d with
    | .L => (op l) △[k] r
    | .R => l △[k] (op r)
  | .nil => .nil

/-- One frame of the search path: the direction we took from this ancestor,
its key, and the subtree we did *not* descend into. -/
structure Frame α where
  /-- Direction taken from this ancestor. -/
  dir : Dir
  /-- Key stored at this ancestor. -/
  key : α
  /-- The subtree we did not descend into. -/
  sibling : Tree α

/-- Re-attach a subtree `c` below the ancestor described by `f`. -/
def Frame.attach (c : Tree α) (f : Frame α) : Tree α :=
  match f.dir with
  | .L => c △[f.key] f.sibling
  | .R => f.sibling △[f.key] c

@[simp] lemma mirror_bringUp (d : Dir) (t : Tree α) :
    (d.bringUp t).mirror = d.flip.bringUp t.mirror := by
  cases d <;> simp [Dir.bringUp, Dir.flip]

/-- Flip a frame: reverse the direction and mirror the sibling. -/
def Frame.flip (f : Frame α) : Frame α :=
  { dir := f.dir.flip, key := f.key, sibling := f.sibling.mirror }

@[simp] lemma mirror_attach (c : Tree α) (f : Frame α) :
    (f.attach c).mirror = f.flip.attach c.mirror := by
  cases f with | mk d k s =>
    cases d <;> simp [Frame.attach, Frame.flip, Dir.flip]

@[simp] lemma mirror_applyChild_bringUp (d₁ d₂ : Dir)
    (t : Tree α) :
    (applyChild d₁ d₂.bringUp t).mirror =
      applyChild d₁.flip d₂.flip.bringUp t.mirror := by
  rcases t with _ | ⟨k, l, r⟩
  · cases d₁ <;> cases d₂ <;> simp [applyChild]
  · cases d₁ <;> cases d₂ <;>
      simp only [applyChild, Dir.flip, Dir.bringUp,
        mirror_node] <;> congr 1 <;>
      first | exact mirror_rotateRight _ | exact mirror_rotateLeft _

/-- Descend from `t` toward `q`, returning the subtree reached (either the
matching node or `.nil` if `q` is absent) and the path above it. The head
of the returned list is the deepest frame (parent of the returned subtree). -/
def descend [LinearOrder α] (t : Tree α) (q : α) : Tree α × List (Frame α) :=
  go t []
where
  /-- Worker for `descend`: accumulates path frames while walking toward `q`. -/
  go : Tree α → List (Frame α) → Tree α × List (Frame α)
  | .nil, acc => (.nil, acc)
  | l △[k] r, acc =>
    if q = k then (l △[k] r, acc)
    else if q < k then go l ({ dir := .L, key := k, sibling := r } :: acc)
    else go r ({ dir := .R, key := k, sibling := l } :: acc)

/-- Splay the subtree `c` upward along `path`, pairing frames from the bottom
up. Each double step (parent `f1`, grandparent `f2`) is:
* **same-direction** (`zig-zig` / `zag-zag`): two outer rotations in direction
  `f2.dir`;
* **opposite-direction** (`zig-zag` / `zag-zig`): one inner rotation at the
  `f2.dir`-child (in direction `f1.dir`), then one outer rotation (in
  direction `f2.dir`).
A leftover single frame is a plain zig/zag. -/
def splayUp : Tree α → List (Frame α) → Tree α
  | c, [] => c
  | c, [f] => f.dir.bringUp (f.attach c)
  | c, f1 :: f2 :: rest =>
    let s := f2.attach (f1.attach c)
    let s' :=
      if f1.dir = f2.dir then
        f2.dir.bringUp (f2.dir.bringUp s)
      else
        f2.dir.bringUp (applyChild f2.dir f1.dir.bringUp s)
    splayUp s' rest

/-- Bottom-up splay: the "textbook" splay analysed by Tarjan, Sundar, and
Elmasry. If `q` is absent the last visited ancestor is splayed to the root. -/
def splay [LinearOrder α] (t : Tree α) (q : α) : Tree α :=
  match descend t q with
  | (.nil, []) => .nil
  | (.nil, f :: rest) => splayUp (f.attach .nil) rest
  | (x@(.node _ _ _), path) => splayUp x path

/-- Reassemble a subtree `c` with its ancestral path `path` (deepest frame
first) back into the original tree. -/
def reassemble (c : Tree α) (path : List (Frame α)) : Tree α :=
  path.foldl (fun c' f => f.attach c') c

@[simp] lemma reassemble_nil (c : Tree α) : reassemble c [] = c := rfl

@[simp] lemma reassemble_cons (c : Tree α) (f : Frame α) (rest : List (Frame α)) :
    reassemble c (f :: rest) = reassemble (f.attach c) rest := rfl

/-- Number of nodes a single frame contributes when re-attached: the
ancestor itself plus its sibling subtree. -/
def Frame.nodes (f : Frame α) : ℕ := 1 + f.sibling.nodeCount

/-- Total number of nodes contributed by a path above a subtree. -/
def pathNodes : List (Frame α) → ℕ
  | [] => 0
  | f :: rest => f.nodes + pathNodes rest

end Definitions


/-! ### Unfolding and Induction Lemmas for `splayUp` -/
section SplayUpInduction

@[simp] theorem splayUp_nil (c : Tree α) : splayUp c [] = c := rfl

@[simp] theorem splayUp_singleton (c : Tree α) (f : Frame α) :
    splayUp c [f] = f.dir.bringUp (f.attach c) := rfl

theorem splayUp_cons_cons (c : Tree α) (f1 f2 : Frame α) (rest : List (Frame α)) :
    splayUp c (f1 :: f2 :: rest) =
      splayUp
        (if f1.dir = f2.dir then
          f2.dir.bringUp (f2.dir.bringUp (f2.attach (f1.attach c)))
        else
          f2.dir.bringUp (applyChild f2.dir f1.dir.bringUp
            (f2.attach (f1.attach c))))
        rest := rfl

theorem splayUp_cons_cons_same (c : Tree α) (f1 f2 : Frame α)
    (rest : List (Frame α)) (h : f1.dir = f2.dir) :
    splayUp c (f1 :: f2 :: rest) =
      splayUp (f2.dir.bringUp (f2.dir.bringUp (f2.attach (f1.attach c)))) rest := by
  rw [splayUp_cons_cons]; simp [h]

theorem splayUp_cons_cons_opp (c : Tree α) (f1 f2 : Frame α)
    (rest : List (Frame α)) (h : f1.dir ≠ f2.dir) :
    splayUp c (f1 :: f2 :: rest) =
      splayUp (f2.dir.bringUp
        (applyChild f2.dir f1.dir.bringUp (f2.attach (f1.attach c)))) rest := by
  rw [splayUp_cons_cons]; simp [h]

/-- Two-step induction principle specialised to `splayUp`: base (empty path),
singleton frame, and the general pair-cons step. The tree `c` is
generalised automatically. -/
theorem splayUp_induction
    {motive : Tree α → List (Frame α) → Prop}
    (nil : ∀ c, motive c [])
    (single : ∀ c f, motive c [f])
    (step : ∀ c f1 f2 rest,
      (∀ c', motive c' rest) → motive c (f1 :: f2 :: rest))
    (c : Tree α) (path : List (Frame α)) : motive c path := by
  induction path using List.twoStepInduction generalizing c with
  | nil => exact nil c
  | singleton f => exact single c f
  | cons_cons f1 f2 rest ih _ => exact step c f1 f2 rest (fun c' => ih c')

end SplayUpInduction


/-! ### Node-Count Invariants -/
section NodeCount

@[simp] lemma pathNodes_nil : pathNodes ([] : List (Frame α)) = 0 := rfl

@[simp] lemma pathNodes_cons (f : Frame α) (rest : List (Frame α)) :
    pathNodes (f :: rest) = f.nodes + pathNodes rest := rfl

@[simp]
theorem nodeCount_Frame_attach (c : Tree α) (f : Frame α) :
    (f.attach c).nodeCount = c.nodeCount + f.nodes := by
  unfold Frame.attach Frame.nodes
  cases f.dir <;> simp <;> omega

@[simp]
theorem nodeCount_bringUp (d : Dir) (t : Tree α) :
    (d.bringUp t).nodeCount = t.nodeCount := by
  cases d <;> simp [Dir.bringUp]

@[simp]
theorem nodeCount_applyChild (d : Dir) (op : Tree α → Tree α)
    (hop : ∀ s, (op s).nodeCount = s.nodeCount) (t : Tree α) :
    (applyChild d op t).nodeCount = t.nodeCount := by
  cases t with
  | nil => rfl
  | node k l r =>
    cases d <;> simp [applyChild, hop]

theorem nodeCount_applyChild_bringUp (d₁ d₂ : Dir) (t : Tree α) :
    (applyChild d₁ d₂.bringUp t).nodeCount = t.nodeCount :=
  nodeCount_applyChild _ _ (nodeCount_bringUp _) _

@[simp]
theorem nodeCount_splayUp (c : Tree α) (path : List (Frame α)) :
    (splayUp c path).nodeCount = c.nodeCount + pathNodes path := by
  induction path using List.twoStepInduction generalizing c with
  | nil => simp [splayUp]
  | singleton f => simp [splayUp, Frame.nodes, pathNodes]
  | cons_cons f1 f2 rest ih _ =>
    unfold splayUp
    split_ifs with h
    · rw [ih]; simp [Frame.nodes, pathNodes_cons]; omega
    · rw [ih]; simp [Frame.nodes, pathNodes_cons]; omega

theorem nodeCount_descend_go [LinearOrder α] (t : Tree α) (q : α) (acc : List (Frame α)) :
    let r := descend.go q t acc
    r.1.nodeCount + pathNodes r.2 = t.nodeCount + pathNodes acc := by
  induction t generalizing acc with
  | nil => simp [descend.go]
  | node k l r ihl ihr =>
    unfold descend.go
    split_ifs with h1 h2
    · simp
    · have := ihl (acc := ⟨.L, k, r⟩ :: acc)
      simp [Frame.nodes] at this ⊢; omega
    · have := ihr (acc := ⟨.R, k, l⟩ :: acc)
      simp [Frame.nodes] at this ⊢; omega

theorem nodeCount_descend [LinearOrder α] (t : Tree α) (q : α) :
    (descend t q).1.nodeCount + pathNodes (descend t q).2 = t.nodeCount := by
  have := nodeCount_descend_go t q []
  simpa [descend] using this

@[simp]
theorem nodeCount_splay [LinearOrder α] (t : Tree α) (q : α) :
    (splay t q).nodeCount = t.nodeCount := by
  unfold splay
  have hd := nodeCount_descend t q
  match h : descend t q with
  | (.nil, []) =>
      rw [h] at hd
      simp at hd
      simp [hd]
  | (.nil, f :: rest) =>
      rw [h] at hd
      simp only [nodeCount_splayUp, nodeCount_Frame_attach,
        nodeCount_empty, pathNodes_cons] at hd ⊢
      omega
  | (.node k l r, path) =>
      rw [h] at hd
      simp only [nodeCount_splayUp]
      omega

end NodeCount


/-! ### Characterizations of `descend` -/
section DescendLemmas

@[simp] lemma descend_empty [LinearOrder α] (q : α) : descend .nil q = (.nil, []) := rfl

lemma descend_go_append [LinearOrder α] (q : α) (t : Tree α) (acc : List (Frame α)) :
    descend.go q t acc =
      ((descend.go q t []).1, (descend.go q t []).2 ++ acc) := by
  induction t generalizing acc with
  | nil => simp [descend.go]
  | node k l r ihl ihr =>
    unfold descend.go
    split_ifs with h1 h2
    · simp
    · rw [ihl (acc := ⟨.L, k, r⟩ :: acc),
        ihl (acc := [⟨.L, k, r⟩])]; simp
    · rw [ihr (acc := ⟨.R, k, l⟩ :: acc),
        ihr (acc := [⟨.R, k, l⟩])]; simp

lemma descend_node_eq [LinearOrder α] (l : Tree α) (k : α) (r : Tree α) :
    descend (l △[k] r) k = (l △[k] r, []) := by
  simp [descend, descend.go]

lemma descend_eq_descend_go [LinearOrder α] (t : Tree α) (q : α) :
    descend t q = descend.go q t [] := rfl

lemma descend_node_lt [LinearOrder α] {l : Tree α} {k : α}
    {r : Tree α} {q : α} (h : q < k) :
    descend (l △[k] r) q =
      ((descend l q).1,
       (descend l q).2 ++ [⟨.L, k, r⟩]) := by
  have hne : q ≠ k := ne_of_lt h
  change descend.go q (l △[k] r) [] = _
  unfold descend.go
  rw [if_neg hne, if_pos h, descend_go_append q l [⟨.L, k, r⟩]]; rfl

lemma descend_node_gt [LinearOrder α] {l : Tree α} {k : α}
    {r : Tree α} {q : α} (h : k < q) :
    descend (l △[k] r) q =
      ((descend r q).1,
       (descend r q).2 ++ [⟨.R, k, l⟩]) := by
  have hne : q ≠ k := ne_of_gt h
  change descend.go q (l △[k] r) [] = _
  unfold descend.go
  rw [if_neg hne, if_neg (not_lt.mpr h.le),
      descend_go_append q r [⟨.R, k, l⟩]]; rfl

lemma reassemble_append (c : Tree α) (p1 p2 : List (Frame α)) :
    reassemble c (p1 ++ p2) = reassemble (reassemble c p1) p2 := by
  simp [reassemble, List.foldl_append]

theorem descend_go_preserves_tree [LinearOrder α] (t : Tree α)
  (q : α) (acc : List (Frame α)) :
    reassemble (descend.go q t acc).1 (descend.go q t acc).2 =
      reassemble t acc := by
  induction t generalizing acc with
  | nil => simp [descend.go]
  | node k l r ihl ihr =>
    unfold descend.go
    split_ifs with h1 h2
    · simp
    · exact ihl (acc := ⟨.L, k, r⟩ :: acc)
    · exact ihr (acc := ⟨.R, k, l⟩ :: acc)

theorem descend_preserves_tree [LinearOrder α] (t : Tree α) (q : α) :
    reassemble (descend t q).1 (descend t q).2 = t := by
  have := descend_go_preserves_tree t q []
  simpa [descend] using this

end DescendLemmas

end SplayTree
